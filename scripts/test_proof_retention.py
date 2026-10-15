"""Check the import parser and removal boundary with small independent graphs."""
import importlib.util
from pathlib import Path
import unittest
import tempfile

spec = importlib.util.spec_from_file_location('proof_retention', Path(__file__).with_name('proof-retention.py'))
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


class ImportAuditTests(unittest.TestCase):
    def test_development_checks_protect_transitive_dependencies(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            dependency = 'IntegerMultBounds.FutureBound'
            unwired = 'IntegerMultBounds.MathlibTM2.Cost.CompactUnwired'
            unwired_dependency = 'IntegerMultBounds.FutureSetup'
            unused = 'IntegerMultBounds.Unused'
            for module in {*audit.PUBLIC_ROOTS, *audit.DEVELOPMENT_ROOTS,
                           audit.THEOREM, dependency, unused, unwired, unwired_dependency}:
                path = root / audit.module_path(module)
                path.parent.mkdir(parents=True, exist_ok=True)
                source = (f'import {dependency}\n'
                          if module in audit.DEVELOPMENT_ROOTS else '')
                if module == unwired:
                    source = f'import {unwired_dependency}\n'
                path.write_text(source)
            data = audit.inventory(root)
            self.assertIn(audit.module_path(dependency), data['retain_for_development'])
            self.assertNotIn(audit.module_path(dependency), data['candidate_files'])
            self.assertIn(audit.module_path(unwired_dependency), data['retain_for_development'])
            self.assertNotIn(audit.module_path(unwired), data['candidate_files'])
            self.assertIn(audit.module_path(unused), data['conservative_candidate_files'])

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
