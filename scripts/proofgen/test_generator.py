"""Authoring-format regression tests; kernel rejection tests use the safe runner."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location('sequence_generator', ROOT / 'scripts/generate_lean_sequence.py')
GENERATOR = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GENERATOR)


class GeneratorTests(unittest.TestCase):
    def setUp(self):
        self.manifest = json.loads((ROOT / 'scripts/proofgen/layout_setup.json').read_text())

    def test_checked_in_output_is_reproducible(self):
        self.assertEqual(GENERATOR.render(self.manifest),
                         (ROOT / 'IntegerMultBounds/Schoenhage/LayoutSequenceGenerated.lean').read_text())

    def test_empty_sequence_is_rejected(self):
        self.manifest['cases'][0]['stages'] = []
        with self.assertRaises(ValueError):
            GENERATOR.render(self.manifest)

    def test_duplicate_names_are_rejected(self):
        self.manifest['cases'].append(copy.deepcopy(self.manifest['cases'][0]))
        with self.assertRaises(ValueError):
            GENERATOR.render(self.manifest)

    def test_missing_proof_is_rejected(self):
        del self.manifest['cases'][0]['stages'][0]['proof']
        with self.assertRaises(ValueError):
            GENERATOR.render(self.manifest)

    def test_zero_tapes_is_rejected(self):
        self.manifest['cases'][0]['tapes'] = 0
        with self.assertRaises(ValueError):
            GENERATOR.render(self.manifest)


if __name__ == '__main__':
    unittest.main()
