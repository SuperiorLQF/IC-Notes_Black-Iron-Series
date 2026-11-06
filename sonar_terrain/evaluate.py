"""Small reproducible sensitivity study; deliberately includes model mismatch."""
import argparse
import json
from pathlib import Path
import numpy as np
from reconstruct import forward, reconstruct


def evaluate():
    x, y = np.linspace(8, 40, 96), np.linspace(0, 20, 24)
    xx, yy = np.meshgrid(x, y)
    truth = .65*np.sin(2*np.pi*(xx-8)/32)*(1+.1*np.cos(yy/5))
    p = .65*2*np.pi/32*np.cos(2*np.pi*(xx-8)/32)*(1+.1*np.cos(yy/5))
    h = 12.
    nominal = forward(p, x, h)
    # A more complete synthetic normal includes along-track slope and actual
    # sonar-to-terrain vertical separation. Inversion still uses a flat plane.
    py = -.65/50*np.sin(2*np.pi*(xx-8)/32)*np.sin(yy/5)
    actual_geometry = ((h-truth)+xx*p)/(np.hypot(h-truth, xx)*np.sqrt(1+p*p+py*py))
    rng = np.random.default_rng(19)
    scenarios = {'matched_clean': nominal,
                 'matched_noise': nominal+rng.normal(0, .0015, nominal.shape),
                 'reflectivity_mismatch': nominal*(1+.05*np.sin(xx/6)),
                 'geometry_mismatch': actual_geometry}
    report = {}
    for name, data in scenarios.items():
        z, _, valid, info = reconstruct(data, x, y, h)
        report[name] = {'rmse_m': float(np.sqrt(np.mean((z-truth)**2))),
                        'valid_fraction': float(valid.mean()),
                        'converged': info['converged']}
    report['interpretation'] = ('Synthetic sensitivity only. Same-model error is not real-world accuracy. '
        'Unknown reflectivity and nonplanar geometry introduce bias.')
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    report = evaluate()
    text = json.dumps(report, indent=2)+'\n'
    print(text, end='')
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    if not all(v['converged'] for v in report.values() if isinstance(v, dict)):
        raise SystemExit(2)
