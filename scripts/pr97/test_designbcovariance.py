"""Small independent compiler examples for the untrusted covariance generator."""
import unittest

from designbcovariance import coefficients


class CovarianceTests(unittest.TestCase):
    def test_unlinked_addition(self):
        dag = {'N': 3, 'v': 2, 'R': 2, 'nodes': [{}, {}, {'args': [0, 1]}], 'roots': [{}]}
        compiled = {'servingOrders': [[['gate', 2, False]], [['gate', 2, True]], [['root', 0]]],
                    'slotsBefore': [0, 1, 2], 'rootSlots': [0], 'side': [['add', 0, 1, 2]]}
        args, slots = coefficients(dag, compiled, [1])
        self.assertEqual(args[2], [1, 1])
        self.assertEqual(slots, [1, 1])

    def test_linked_operand_cancellation(self):
        dag = {'N': 4, 'v': 2, 'R': 2, 'nodes': [{}, {},
               {'args': [0, 1], 'link': {'operand': True, 'user': 3, 'pos': False}},
               {'args': [1, 2]}], 'roots': [{}]}
        compiled = {'servingOrders': [[['gate', 2, False]], [['gate', 2, True]],
                    [['gate', 3, True]], [['root', 0]]], 'slotsBefore': [0, 1, 2, 2],
                    'rootSlots': [1], 'side': [['add', 0, 1, 2], ['add', 1, 0, 3]]}
        args, slots = coefficients(dag, compiled, [1])
        self.assertEqual(args[2], [1, 0])
        self.assertEqual(slots, [1, 0])

    def test_copies_and_multiple_targets(self):
        dag = {'N': 2, 'v': 1, 'R': 3, 'nodes': [{}, {'args': [0, 0]}], 'roots': [{}, {}]}
        compiled = {'servingOrders': [[['gate', 1, False], ['gate', 1, True]],
                    [['root', 0], ['root', 1]]], 'slotsBefore': [0, 2], 'rootSlots': [0, 2],
                    'side': [['add', 0, 1, 1], ['copy', 0, 2, 1]]}
        args, slots = coefficients(dag, compiled, [1, 2])
        self.assertEqual(args[1], [3, 3])
        self.assertEqual(slots, [3, 3, 2])
        compiled['side'][1] = ['copy', 1, 2, 1]
        with self.assertRaisesRegex(AssertionError, 'disagrees'):
            coefficients(dag, compiled, [1, 2])


if __name__ == '__main__':
    unittest.main()
