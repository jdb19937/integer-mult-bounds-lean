"""Tests of untrusted frame generation; Lean checks the emitted certificates."""
import json
from math import gcd
from pathlib import Path
import tempfile
import unittest

import stage2framebank as bank


def triple(a, b, c):
    return a + 32 * b + 1024 * c


class FrameBankTests(unittest.TestCase):
    def test_inverse_is_primitive_and_exact(self):
        basis = [triple(0, 1, 2), triple(0, 1, 3), 32768]
        scale, inverse = bank.inverse_witness(basis)
        self.assertGreater(scale, 0)
        common = scale
        for row in inverse:
            for x in row:
                common = gcd(common, x)
        self.assertEqual(common, 1)
        vectors = [bank.vector(k) for k in basis]
        gram = [[9 * sum(x * y for x, y in zip(a, b)) - sum(a) * sum(b)
                 for b in vectors] for a in vectors]
        for i in range(len(basis)):
            for j in range(len(basis)):
                self.assertEqual(sum(gram[i][k] * inverse[k][j] for k in range(len(basis))),
                                 scale if i == j else 0)

    def test_empty_inverse(self):
        self.assertEqual(bank.inverse_witness([]), (1, []))

    def test_singular_basis_is_rejected(self):
        with self.assertRaises(StopIteration):
            bank.inverse_witness([triple(0, 1, 2)] * 2)

    def test_span_sharing_remaps_edges_and_occurrences(self):
        a, b = triple(0, 1, 2), triple(0, 1, 3)
        original = {
            'records': [{'basis': [a, b], 'generators': [a, b]},
                        {'basis': [b, a], 'generators': [b, a]},
                        {'basis': [a], 'generators': [a]}],
            'edges': [[0, 2], [1, 2]],
            'occurrences': [['sigma', 1, 0], ['sigma', 2, 1]],
            'computedRuns': [['slot', 0, [0, 2]], ['slot', 1, [1, 2]]],
        }
        result = bank.compact_bank(json.loads(json.dumps(original)))
        self.assertEqual(len(result['records']), 2)
        self.assertEqual(result['edges'], [[0, 1]])
        self.assertEqual([row[2] for row in result['occurrences']], [0, 0])
        self.assertEqual([row[2] for row in result['computedRuns']], [[0, 1], [0, 1]])
        self.assertEqual(result, bank.compact_bank(json.loads(json.dumps(original))))

    def test_extension_rejects_nonbasis_generators(self):
        a, b = triple(0, 1, 2), triple(0, 1, 3)
        result = {'source': {'upstream': bank.df.dbm.UPSTREAM, 'sha256': bank.df.dbm.PINS},
                  'records': [{'basis': [a], 'generators': [a, b]}]}
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(AssertionError):
                bank.emit_bank(result, directory, bank_name='SignedExtra', self_basis=True)

    def test_extension_preserves_non_power_of_two_lookup_layout(self):
        codes = [triple(0, 1, i) for i in range(2, 7)]
        result = {'source': {'upstream': bank.df.dbm.UPSTREAM, 'sha256': bank.df.dbm.PINS},
                  'records': [{'basis': [a], 'generators': [a]} for a in codes]}
        with tempfile.TemporaryDirectory() as directory:
            bank.emit_bank(result, directory, per_module=2, bank_name='SignedExtra', self_basis=True)
            root = Path(directory) / 'IntegerMultBounds/MathlibTM2/M8/Frames/SignedExtra'
            text = (root / 'Data.lean').read_text()
            self.assertIn('def bankWidth : Nat := 8', text)
            self.assertIn('def bankSize : Nat := 5', text)
            self.assertEqual(len(list((root / 'Data').glob('Bank*.lean'))), 3)
            self.assertEqual(text.count('(bank002)'), 2)
            check = (root / 'Checks/Bank000.lean').read_text()
            self.assertIn('Record.check_self', check)
            self.assertNotIn('generatorCheck', check)

    def test_emission_rejects_unpinned_provenance(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(AssertionError):
                bank.emit_bank({'source': {'upstream': 'wrong', 'sha256': {}}}, directory)
            self.assertEqual(list(Path(directory).iterdir()), [])


if __name__ == '__main__':
    unittest.main()
