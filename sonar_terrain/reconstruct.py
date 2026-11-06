"""CPU-only, reference-plane Lambertian sidescan relief reconstruction."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import numpy as np
from scipy import sparse
from scipy.sparse.linalg import lsqr


def validate(intensity, x, y, altitude, gain, reflectivity):
    intensity = np.asarray(intensity, dtype=float)
    x, y = np.asarray(x, dtype=float), np.asarray(y, dtype=float)
    if x.ndim != 1 or y.ndim != 1:
        raise ValueError('x and y must be one-dimensional coordinate arrays')
    if intensity.ndim != 2 or intensity.shape != (len(y), len(x)):
        raise ValueError('intensity must have shape (len(y), len(x))')
    if len(x) < 3 or len(y) < 3:
        raise ValueError('At least 3 pings and 3 cross-track samples are required')
    if intensity.size > 300_000:
        raise ValueError('CPU demo limit: 300000 pixels; crop or downsample first')
    if not np.all(np.isfinite(x)) or not np.all(np.isfinite(y)):
        raise ValueError('Coordinates must be finite')
    if np.any(np.diff(x) <= 0) or np.any(np.diff(y) <= 0):
        raise ValueError('x and y must be strictly increasing, in metres')
    if not (np.all(x > 0) or np.all(x < 0)):
        raise ValueError('Use one sonar side at a time; exclude nadir and x=0')
    def positive_vector(value, name):
        a = np.asarray(value, dtype=float)
        if a.ndim == 0:
            a = np.full(len(y), float(a))
        if a.shape != (len(y),) or not np.all(np.isfinite(a)) or np.any(a <= 0):
            raise ValueError(f'{name} must be positive scalar or one value per ping')
        return a
    return (intensity, x, y, positive_vector(altitude, 'altitude'),
            positive_vector(gain, 'gain'), positive_vector(reflectivity, 'reflectivity'))


def forward(slope, x, altitude, gain=1.0, reflectivity=1.0):
    """Diffuse intensity before any log/TVG processing; z << altitude approximation."""
    h = np.asarray(altitude).reshape(-1, 1)
    g = np.asarray(gain).reshape(-1, 1)
    rho = np.asarray(reflectivity).reshape(-1, 1)
    return g * rho * (h + x[None, :] * slope) / (
        np.hypot(h, x[None, :]) * np.sqrt(1 + slope * slope))


def reconstruct(intensity, x, y, altitude, gain=1.0, reflectivity=1.0,
                mask=None, anchor=None, max_slope=0.35, smooth_x=0.3,
                smooth_y=0.3, max_iterations=1200):
    """Invert the flat-connected angular branch, then solve a sparse surface fit.

    Each row's nearest-nadir elevation is a boundary condition, default zero.
    Invalid returns are excluded from observations but spatially interpolated.
    """
    intensity, x, y, h, gain, rho = validate(
        intensity, x, y, altitude, gain, reflectivity)
    if (not np.all(np.isfinite([max_slope, smooth_x, smooth_y]))
            or not 0 < max_slope <= 1 or smooth_x <= 0 or smooth_y <= 0):
        raise ValueError('Require 0 < max_slope <= 1 and positive smoothing weights')
    if not isinstance(max_iterations, (int, np.integer)) or max_iterations < 1:
        raise ValueError('max_iterations must be a positive integer')
    m, n = intensity.shape
    if mask is None:
        mask = np.ones_like(intensity, dtype=bool)
    else:
        mask = np.asarray(mask, dtype=bool)
        if mask.shape != intensity.shape:
            raise ValueError('mask shape must equal intensity shape')
    # cos(alpha-theta); choose the branch continuously connected to theta=0.
    q = intensity / (gain * rho)[:, None]
    alpha = np.arctan2(x[None, :], h[:, None])
    theta = alpha - np.sign(x)[None, :] * np.arccos(np.clip(q, 0, 1))
    slopes = np.tan(theta)
    # Branch monotonicity is not guaranteed outside this conservative region.
    branch_ok = np.abs(x)[None, :] / h[:, None] > 1.05 * max_slope
    valid = (mask & np.isfinite(q) & (q > 0) & (q < 1)
             & np.isfinite(slopes) & (np.abs(slopes) <= max_slope) & branch_ok)
    if np.count_nonzero(valid) < max(4, int(0.05 * intensity.size)):
        raise ValueError('Too few usable returns; check gain, mask, units, and nadir crop')
    slopes = np.where(valid, slopes, np.nan)
    # Edge gradients and reliability. Both endpoints must be observed.
    edges = valid[:, :-1] & valid[:, 1:]
    if not np.any(edges):
        raise ValueError('No adjacent valid samples for surface integration')
    edge_slopes = np.where(edges, (slopes[:, :-1] + slopes[:, 1:]) / 2, 0)
    dx, dy = np.diff(x), np.diff(y)
    # Nonuniform-grid gradient operators, in metre coordinates.
    gx = sparse.diags([-1/dx, 1/dx], [0, 1], shape=(n-1, n), format='csr')
    gy = sparse.diags([-1/dy, 1/dy], [0, 1], shape=(m-1, m), format='csr')
    d_x = sparse.kron(sparse.eye(m), gx, format='csr')
    d_y = sparse.kron(gy, sparse.eye(n), format='csr')
    # Smooth changes of cross-track slope; scale by median cell width so the
    # regularization strengths are dimensionless relative to the slope fit.
    d_xx = sparse.kron(sparse.eye(m),
        sparse.diags([-np.ones(n-2), np.ones(n-2)], [0, 1], shape=(n-2, n-1)) @ gx,
        format='csr')
    k = int(np.argmin(np.abs(x)))
    anchor = np.zeros(m) if anchor is None else np.asarray(anchor, dtype=float)
    if anchor.shape != (m,) or not np.all(np.isfinite(anchor)):
        raise ValueError('anchor must contain one finite elevation per ping')
    # Eliminate boundary variables rather than approximating hard anchors.
    fixed = np.arange(m) * n + k
    free = np.ones(m*n, dtype=bool)
    free[fixed] = False
    a = sparse.vstack([d_x.multiply(edges.ravel()[:, None]),
                       np.sqrt(smooth_x)*d_xx, np.sqrt(smooth_y)*d_y], format='csr')
    b = np.concatenate([edge_slopes.ravel(), np.zeros(d_xx.shape[0]+d_y.shape[0])])
    b -= a[:, fixed] @ anchor
    solved = lsqr(a[:, free], b, atol=1e-7, btol=1e-7, iter_lim=max_iterations)
    z = np.zeros(m*n)
    z[fixed], z[free] = anchor, solved[0]
    z = z.reshape(m, n)
    info = {'solver_stop': int(solved[1]), 'solver_iterations': int(solved[2]),
            'converged': bool(solved[1] in (0, 1, 2, 4, 5)),
            'valid_fraction': float(valid.mean()),
            'anchor_index': k, 'height_units': 'm',
            'meaning': 'relative relief, NOT measured absolute bathymetry'}
    return z, slopes, valid, info


def save_outputs(output, intensity, x, y, z, slopes, valid, info, truth=None):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(output/'reconstruction.npz', x=x, y=y, elevation=z,
                        slopes=slopes, observed_mask=valid)
    (output/'report.json').write_text(json.dumps(info, indent=2, ensure_ascii=False)+'\n')
    xx, yy = np.meshgrid(x, y)
    points = np.column_stack([xx.ravel(), yy.ravel(), z.ravel(), valid.ravel().astype(int)])
    np.savetxt(output/'points.csv', points, delimiter=',',
               header='x_m,y_m,relative_elevation_m,observed', comments='', fmt='%.7g')
    fig, axes = plt.subplots(1, 4 if truth is not None else 3, figsize=(16, 4),
                             constrained_layout=True)
    panels = [(intensity, 'Linear return intensity', 'gray'),
              (valid.astype(float), 'Used observations (white)', 'gray'),
              (z, 'Relative relief (m)', 'terrain')]
    if truth is not None:
        panels.append((z-truth, 'Error against synthetic truth (m)', 'coolwarm'))
    for ax, (data, title, cmap) in zip(axes, panels):
        im = ax.pcolormesh(x, y, data, shading='auto', cmap=cmap)
        fig.colorbar(im, ax=ax)
        ax.set(title=title, xlabel='Cross track (m)', ylabel='Along track (m)')
    fig.savefig(output/'overview.png', dpi=150)
    plt.close(fig)
    fig = plt.figure(figsize=(9, 6))
    ax = fig.add_subplot(111, projection='3d')
    ax.plot_surface(xx, yy, z, cmap='terrain', rcount=70, ccount=100)
    ax.set(xlabel='Cross track (m)', ylabel='Along track (m)',
           zlabel='Relative elevation (m)', title='Model-based relative relief')
    fig.savefig(output/'surface.png', dpi=150, bbox_inches='tight')
    plt.close(fig)


def demo(output, seed=7):
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    rng = np.random.default_rng(seed)
    x, y = np.linspace(8, 48, 128), np.linspace(0, 30, 40)
    xx, yy = np.meshgrid(x, y)
    # The nearest-nadir boundary is exactly zero for each row.
    z_true = 0.8*np.sin(2*np.pi*(xx-x[0])/40) * (0.8+0.2*np.cos(2*np.pi*yy/30))
    slope = 0.8*2*np.pi/40*np.cos(2*np.pi*(xx-x[0])/40)*(0.8+0.2*np.cos(2*np.pi*yy/30))
    h = 10+0.3*np.sin(2*np.pi*y/30)
    gain = 1+0.05*np.cos(2*np.pi*y/30)
    clean = forward(slope, x, h, gain)
    observed = clean + rng.normal(0, .0015, clean.shape)
    mask = rng.random(clean.shape) > .015
    mask[14:20, 50:57] = False  # missing patch, NOT simulated physical shadow
    observed[~mask] = np.nan
    np.savez_compressed(output/'input.npz', intensity=observed, x=x, y=y,
                        altitude=h, gain=gain, reflectivity=1., mask=mask,
                        anchor=z_true[:, 0])
    np.savez_compressed(output/'truth.npz', elevation=z_true)
    z, slopes, valid, info = reconstruct(observed, x, y, h, gain, mask=mask,
                                        anchor=z_true[:, 0])
    info.update(seed=seed, rmse_m=float(np.sqrt(np.mean((z-z_true)**2))),
                mae_m=float(np.mean(np.abs(z-z_true))),
                experiment='synthetic same-model sanity check; not real-data accuracy')
    save_outputs(output, observed, x, y, z, slopes, valid, info, z_true)
    return info


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('demo', help='Generate and reconstruct a small synthetic swath')
    p.add_argument('--output', type=Path, default=Path('outputs/demo'))
    p.add_argument('--seed', type=int, default=7)
    p = sub.add_parser('reconstruct', help='Reconstruct calibrated one-side NPZ input')
    p.add_argument('input', type=Path)
    p.add_argument('--output', type=Path, default=Path('outputs/reconstruction'))
    p.add_argument('--max-slope', type=float, default=.35)
    p.add_argument('--smooth-x', type=float, default=.3)
    p.add_argument('--smooth-y', type=float, default=.3)
    args = parser.parse_args()
    try:
        if args.command == 'demo':
            info = demo(args.output, args.seed)
        else:
            with np.load(args.input, allow_pickle=False) as d:
                for key in ('intensity', 'x', 'y', 'altitude', 'gain', 'reflectivity'):
                    if key not in d: raise ValueError(f'Missing input key: {key}')
                optional = {key: d[key] for key in ('mask', 'anchor') if key in d}
                z, slopes, valid, info = reconstruct(
                    d['intensity'], d['x'], d['y'], d['altitude'], d['gain'],
                    d['reflectivity'], **optional, max_slope=args.max_slope,
                    smooth_x=args.smooth_x, smooth_y=args.smooth_y)
                save_outputs(args.output, d['intensity'], d['x'], d['y'], z,
                             slopes, valid, info)
        print(json.dumps(info, indent=2, ensure_ascii=False))
        if not info['converged']:
            parser.exit(2, 'Solver did not converge; outputs are provisional.\n')
    except (ValueError, OSError, KeyError) as exc:
        parser.exit(2, f'Input/output error: {exc}\n')


if __name__ == '__main__':
    main()
