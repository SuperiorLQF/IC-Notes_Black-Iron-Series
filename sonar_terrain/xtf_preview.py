"""Inspect real XTF pings and create an explicitly uncalibrated relief preview."""
import argparse
import json
from pathlib import Path
import numpy as np
import pyxtf
from reconstruct import reconstruct, save_outputs


def load_pings(path):
    if path.with_suffix('.pyxtf_idx').exists():
        raise ValueError('Remove the optional pickle .pyxtf_idx cache before reading')
    header, packets = pyxtf.xtf_read(str(path))
    if header.NavUnits != 3:
        raise ValueError('This adapter requires latitude/longitude navigation (NavUnits=3)')
    pings = packets.get(pyxtf.XTFHeaderType.sonar, [])
    if not pings:
        raise ValueError('No sonar pings')
    selected = []
    for ping in pings:
        lat, lon, h = ping.SensorYcoordinate, ping.SensorXcoordinate, ping.SensorPrimaryAltitude
        if (not np.all(np.isfinite([lat, lon, h])) or not -90 <= lat <= 90
                or not -180 <= lon <= 180 or (lat == 0 and lon == 0) or h <= 0):
            continue
        channels = {}
        for ch, values in zip(ping.ping_chan_headers, ping.data):
            kind = int(header.ChanInfo[ch.ChannelNumber].TypeOfChannel)
            if kind in (1, 2) and ch.SlantRange > h and len(values) > 10:
                channels[kind] = (ch, np.asarray(values, dtype=float))
        if 1 in channels and 2 in channels:
            selected.append((ping, channels))
    if len(selected) < 5:
        raise ValueError('Fewer than five valid navigated pings with altitude and both sonar sides')
    lat = np.deg2rad([a.SensorYcoordinate for a, _ in selected])
    lon = np.deg2rad([a.SensorXcoordinate for a, _ in selected])
    # Local equirectangular projection is sufficient only for these short lines.
    east = 6371000 * (lon-lon[0])*np.cos(lat.mean())
    north = 6371000 * (lat-lat[0])
    distance = np.r_[0, np.cumsum(np.hypot(np.diff(east), np.diff(north)))]
    # Duplicate GPS fixes add no along-track information; retain one per position.
    keep = np.r_[True, np.diff(distance) > .005]
    selected = [s for s, ok in zip(selected, keep) if ok]
    y = distance[keep]
    if len(y) < 5 or y[-1] <= .1:
        raise ValueError('Navigation does not resolve a usable along-track grid')
    summary = dict(total_sonar_pings=len(pings), valid_pings_before_duplicate_removal=len(lat),
        selected_pings=len(y), navigation='Sensor latitude/longitude, local projection, cumulative path distance',
        track_length_m=float(y[-1]), first_time=str(selected[0][0].get_time()),
        last_time=str(selected[-1][0].get_time()),
        altitude_min_m=float(min(p.SensorPrimaryAltitude for p, _ in selected)),
        altitude_max_m=float(max(p.SensorPrimaryAltitude for p, _ in selected)),
        radiometric_calibration_available=False, paired_bathymetry_available=False)
    return selected, y, summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--output', type=Path, default=Path('outputs/real_xtf'))
    parser.add_argument('--exploratory-flat-calibration', action='store_true',
                        help='Explicitly permit empirical flat-bed normalization; NOT a measured calibration')
    args = parser.parse_args()
    try:
        records, y, summary = load_pings(args.input)
        output = args.output
        output.mkdir(parents=True, exist_ok=True)
        np.savetxt(output/'navigation.csv', np.array([
            [float(y[i]), p.SensorXcoordinate, p.SensorYcoordinate, p.SensorPrimaryAltitude,
             p.SensorHeading, p.SensorPitch, p.SensorRoll] for i, (p, _) in enumerate(records)]),
            delimiter=',', header='path_m,longitude_deg,latitude_deg,altitude_m,heading_deg,pitch_deg,roll_deg', comments='')
        import matplotlib
        matplotlib.use('Agg')
        import matplotlib.pyplot as plt
        # Preserve every raw ping in a separate view before navigation thinning.
        _, packet_map = pyxtf.xtf_read(str(args.input))
        raw_pings = packet_map[pyxtf.XTFHeaderType.sonar]
        fig_raw, raw_axes = plt.subplots(1, 2, figsize=(12, 6), constrained_layout=True)
        for j, ax in enumerate(raw_axes):
            image = np.array([np.asarray(p.data[j], dtype=float) for p in raw_pings])
            rmax = float(raw_pings[0].ping_chan_headers[j].SlantRange)
            display = np.log1p(image)
            lo, hi = np.percentile(display, [1, 99])
            ax.imshow(display, aspect='auto', origin='lower', extent=[0, rmax, 0, len(raw_pings)],
                      cmap='gray', vmin=lo, vmax=hi)
            ax.set(title=f'Raw channel {j}: all {len(raw_pings)} pings',
                   xlabel='Slant range (m), near to far assumed', ylabel='Ping index')
        fig_raw.savefig(output/'raw_all_pings.png', dpi=150)
        plt.close(fig_raw)
        heights = np.array([p.SensorPrimaryAltitude for p, _ in records])
        sides = {}
        fig, axes = plt.subplots(1, 2, figsize=(12, 5), constrained_layout=True)
        for ax, (kind, name) in zip(axes, [(1, 'port'), (2, 'starboard')]):
            # Conservative inner crop excludes the water column for all pings.
            limit = min(float(ch[kind][0].SlantRange)**2-p.SensorPrimaryAltitude**2
                        for p, ch in records)**.5
            inner = max(5., float(heights.max())*1.25)
            if limit <= inner+1:
                raise ValueError('No common ground-range swath after water-column removal')
            x = np.linspace(inner, .95*limit, 96)
            values = []
            for (p, channels), h in zip(records, heights):
                ch, raw = channels[kind]
                # Raw channel samples are assumed near-to-far slant range.
                slant = np.linspace(0, float(ch.SlantRange), len(raw), endpoint=False)
                values.append(np.interp(np.hypot(x, h), slant, raw))
            values = np.array(values)
            if kind == 1:
                x, values = -x[::-1], values[:, ::-1]
            sides[name] = (x, values)
            im = ax.pcolormesh(x, y, np.log1p(values), cmap='gray', shading='auto')
            ax.set(title=f'{name}: log(1 + raw counts)', xlabel='Reference-plane ground range (m)', ylabel='GPS path distance (m)')
            fig.colorbar(im, ax=ax)
        fig.savefig(output/'real_waterfall.png', dpi=150)
        plt.close(fig)
        reports = {}
        if args.exploratory_flat_calibration:
            # A common regular grid reduces GPS jitter/unequal spacing effects.
            regular_y = np.linspace(y[0], y[-1], min(64, len(y)))
            h = np.interp(regular_y, y, heights)
            for name, (x, raw) in sides.items():
                counts = np.array([np.interp(regular_y, y, raw[:, j]) for j in range(len(x))]).T
                flat = h[:, None]/np.hypot(h[:, None], x[None, :])
                # Estimate one range profile under a flat seabed assumption.
                # This removes any true cross-track structure common to pings.
                profile = np.median(counts / flat, axis=0)
                if np.any(profile <= 0): raise ValueError('Nonpositive empirical intensity profile')
                intensity = counts/profile
                z, slopes, mask, report = reconstruct(intensity, x, regular_y, h,
                    max_slope=.6, smooth_x=1., smooth_y=1., max_iterations=1600)
                report.update(interpretation='EXPLORATORY ONLY: empirical flat-bed calibration, no bathymetry validation',
                    calibration='per-range median counts divided by flat-plane cosine, NOT measured gain/reflectivity',
                    anchor='assumed zero at each nearest-nadir sample',
                    units='conditional model metres; not verified physical elevation',
                    attitude_correction=False, shadow_mask='only automatic validity filtering; no manual shadow annotation')
                dest=output/name
                save_outputs(dest, intensity, x, regular_y, z, slopes, mask, report)
                np.savez_compressed(dest/'exploratory_input.npz',intensity=intensity,x=x,y=regular_y,
                                    altitude=h,gain=1.,reflectivity=1.)
                # Replace default figure title to avoid presenting a measured surface.
                fig=plt.figure(figsize=(9,6));ax=fig.add_subplot(111,projection='3d')
                xx, yy=np.meshgrid(x,regular_y)
                ax.plot_surface(xx,yy,z,cmap='terrain')
                ax.set(title=f'{name}: UNCALIBRATED relief hypothesis',xlabel='Cross track (m)',
                       ylabel='GPS path (m)',zlabel='Model height (m)')
                fig.savefig(dest/'surface.png',dpi=150,bbox_inches='tight');plt.close(fig)
                reports[name]=report
            summary['exploratory_results']=reports
        summary['reconstruction_requested']=args.exploratory_flat_calibration
        (output/'metadata.json').write_text(json.dumps(summary,indent=2)+'\n')
        print(json.dumps(summary,indent=2))
        if any(not r['converged'] for r in reports.values()):
            parser.exit(2,'One or more exploratory surface solves did not converge.\n')
    except (ValueError, OSError, KeyError) as exc:
        parser.exit(2,f'XTF processing error: {exc}\n')


if __name__ == '__main__':
    main()
