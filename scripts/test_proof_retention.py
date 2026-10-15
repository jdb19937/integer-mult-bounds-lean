"""Check the import parser and removal boundary with small independent graphs."""
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location('proof_retention', Path(__file__).with_name('proof-retention.py'))
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


class ImportAuditTests(unittest.TestCase):
    def test_comments_do_not_create_dependencies(self):
        source = '''/- import IntegerMultBounds.Fake
          /- nested -/ import IntegerMultBounds.AlsoFake -/
        public import IntegerMultBounds.Real -- import IntegerMultBounds.Fake
        def message := "import IntegerMultBounds.String"
        '''
        self.assertEqual(audit.imports(source), {'IntegerMultBounds.Real'})

    def test_modifiers_and_multiple_imports(self):
        self.assertEqual(audit.imports('public meta import IntegerMultBounds.A IntegerMultBounds.B\n'
                                       'import Mathlib.Data.Nat.Basic\nimport IntegerMultBounds\n'),
                         {'IntegerMultBounds.A', 'IntegerMultBounds.B', 'IntegerMultBounds'})

    def test_transitive_diamond_and_cycle(self):
        graph = {'main': {'left', 'right'}, 'left': {'shared'}, 'right': {'shared'},
                 'shared': {'left'}, 'legacy': {'shared'}}
        self.assertEqual(audit.closure(graph, ['main']), {'main', 'left', 'right', 'shared'})

    def test_missing_dependency_is_an_error(self):
        with self.assertRaisesRegex(ValueError, 'Missing local module'):
            audit.closure({'main': {'absent'}}, ['main'])

    def test_removal_includes_transitive_legacy_importers(self):
        graph = {'retired': set(), 'wrapper': {'retired'}, 'outer': {'wrapper'},
                 'proof': set(), 'IntegerMultBounds': {'outer', 'proof'}}
        self.assertEqual(audit.removal_closure(graph, {'retired'}, {'proof'}),
                         {'retired', 'wrapper', 'outer'})

    def test_removal_cannot_reach_protected_proof(self):
        graph = {'shared': set(), 'proof': {'shared'}}
        with self.assertRaisesRegex(ValueError, 'protected modules'):
            audit.removal_closure(graph, {'shared'}, {'proof'})


if __name__ == '__main__':
    unittest.main()
