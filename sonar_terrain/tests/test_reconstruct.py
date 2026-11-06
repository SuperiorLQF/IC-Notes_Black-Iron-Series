import sys
import unittest
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from reconstruct import forward, reconstruct


class ReconstructionTests(unittest.TestCase):
    def case(self, port=False):
        x = np.linspace(-45, -8, 72) if port else np.linspace(8, 45, 72)
        y = np.linspace(0, 15, 12)
        h = np.linspace(9, 11, len(y))
        gain = np.linspace(.8, 1.2, len(y))
        slope = np.full((len(y), len(x)), .08)
        return x, y, h, gain, slope

    def test_tilted_plane_both_sides_and_varying_calibration(self):
        for port in (False, True):
            x, y, h, gain, slope = self.case(port)
            intensity = forward(slope, x, h, gain, .7)
            anchor = np.full(len(y), 2.)
            z, p, valid, info = reconstruct(intensity, x, y, h, gain, .7, anchor=anchor)
            truth = 2+.08*(x-x[np.argmin(np.abs(x))])
            self.assertTrue(info['converged'])
            self.assertTrue(np.all(valid))
            np.testing.assert_allclose(p, slope, atol=1e-12)
            np.testing.assert_allclose(z, np.broadcast_to(truth, z.shape), atol=.0005)
            np.testing.assert_array_equal(z[:, info['anchor_index']], anchor)

    def test_nonuniform_coordinates(self):
        x = np.array([8., 8.3, 9., 11., 14., 20.])
        y = np.array([0., .5, 2., 5.])
        slope = np.full((4, 6), -.04)
        z, _, _, info = reconstruct(forward(slope, x, 10), x, y, 10)
        self.assertTrue(info['converged'])
        np.testing.assert_allclose(z, np.broadcast_to(-.04*(x-8), z.shape), atol=1e-4)

    def test_invalid_returns_excluded_and_missing_patch_interpolated(self):
        x, y, h, gain, slope = self.case()
        intensity = forward(slope, x, h, gain)
        intensity[3:6, 20:28] = np.nan
        intensity[1, 30] = 9.
        z, _, valid, info = reconstruct(intensity, x, y, h, gain)
        self.assertTrue(np.isfinite(z).all())
        self.assertFalse(valid[3:6, 20:28].any())
        self.assertFalse(valid[1, 30])
        truth = .08*(x-x[0])
        self.assertLess(np.max(np.abs(z-truth)), .005)

    def test_reject_bad_input(self):
        x, y, h, gain, slope = self.case()
        intensity = forward(slope, x, h, gain)
        for changed in ({'x': -x}, {'gain': 0}, {'altitude': -1},
                        {'intensity': np.zeros_like(intensity)},
                        {'mask': np.zeros((2, 2), dtype=bool)},
                        {'x': np.linspace(-10, 10, len(x))},
                        {'anchor': np.array([0.])}, {'smooth_y': 0}):
            kw = dict(intensity=intensity, x=x, y=y, altitude=h, gain=gain)
            kw.update(changed)
            with self.assertRaises(ValueError): reconstruct(**kw)

    def test_nadir_ambiguity_is_masked(self):
        x = np.linspace(.1, 20, 50)
        y = np.arange(5.)
        data = forward(np.zeros((5, 50)), x, 10)
        _, _, valid, _ = reconstruct(data, x, y, 10)
        self.assertFalse(valid[:, x < 3.675].any())

    def test_iteration_limit_is_not_reported_as_convergence(self):
        x, y, h, gain, slope = self.case()
        _, _, _, info = reconstruct(forward(slope, x, h, gain), x, y, h, gain,
                                     max_iterations=1)
        self.assertFalse(info['converged'])


if __name__ == '__main__':
    unittest.main()
