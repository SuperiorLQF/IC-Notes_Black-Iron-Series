import ctypes
import importlib.util
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))


@unittest.skipUnless(importlib.util.find_spec('pyxtf'), 'Optional pyxtf dependency not installed')
class RealXtfTests(unittest.TestCase):
    def test_excerpt_ends_at_complete_record_and_has_real_navigation(self):
        import pyxtf
        from xtf_preview import load_pings
        source = ROOT/'data/real/opensidescan/starfish_excerpt.xtf'
        data = source.read_bytes()
        offset = ctypes.sizeof(pyxtf.XTFFileHeader)
        count = 0
        while offset < len(data):
            packet = pyxtf.XTFPacketStart.from_buffer_copy(data, offset)
            self.assertEqual(packet.MagicNumber, 0xFACE)
            self.assertGreaterEqual(packet.NumBytesThisRecord, ctypes.sizeof(packet))
            offset += packet.NumBytesThisRecord
            self.assertLessEqual(offset, len(data))
            count += 1
        self.assertEqual(count, 439)
        records, y, report = load_pings(source)
        self.assertEqual(report['total_sonar_pings'], 439)
        self.assertEqual(report['valid_pings_before_duplicate_removal'], 412)
        self.assertEqual(len(records), 15)
        self.assertGreater(y[-1], 20)
        self.assertTrue(all(p.SensorPrimaryAltitude > 0 for p, _ in records))
        self.assertFalse(report['radiometric_calibration_available'])


if __name__ == '__main__':
    unittest.main()
