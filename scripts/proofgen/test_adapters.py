import copy
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from generate_lean_adapter import render


class AdapterTests(unittest.TestCase):
    def setUp(self):
        self.placement = json.loads((ROOT / 'scripts/proofgen/layout_placements.json').read_text())
        self.cleanup = json.loads((ROOT / 'scripts/proofgen/twist_cleanup.json').read_text())

    def test_reproducible(self):
        for manifest, module in [(self.placement, 'LayoutPlacementGenerated'), (self.cleanup, 'TwistCleanupGenerated')]:
            self.assertEqual(render(manifest), (ROOT / f'IntegerMultBounds/Schoenhage/{module}.lean').read_text())

    def test_slot_alias(self):
        self.placement['cases'][0]['slots'][1] = 34
        with self.assertRaises(ValueError):
            render(self.placement)

    def test_out_of_range(self):
        self.placement['cases'][0]['slots'][1] = 48
        with self.assertRaises(ValueError):
            render(self.placement)

    def test_cleanup_overlaps_rewind(self):
        self.cleanup['clear'].append(17)
        with self.assertRaises(ValueError):
            render(self.cleanup)

    def test_duplicate_cleanup(self):
        self.cleanup['clear'].append(11)
        with self.assertRaises(ValueError):
            render(self.cleanup)

    def test_duplicate_names(self):
        self.placement['cases'].append(copy.deepcopy(self.placement['cases'][0]))
        with self.assertRaises(ValueError):
            render(self.placement)


if __name__ == '__main__':
    unittest.main()
