"""Test prefix isolation and guard cleanup without launching Lean."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import Mock, patch


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(filename))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


prefixes = load('prefixes', 'profile-lean-prefixes.py')
guard = load('guard', 'check-lean-safe.py')


class PrefixTests(unittest.TestCase):
    def test_prefix_preserves_proofs_and_stops_without_placeholders(self):
        source = 'import Mathlib\nnamespace Example\ntheorem one : 1 = 1 := rfl\nend Example\n'
        self.assertEqual(prefixes.prefix_source(source, 3),
                         'import Mathlib\nnamespace Example\ntheorem one : 1 = 1 := rfl\n\n#exit\n')
        for boundary in (0, -1, 5):
            with self.assertRaises(ValueError):
                prefixes.prefix_source(source, boundary)

    def run_fake_check(self, exit_code):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / 'Example.lean'
            original = 'import Mathlib\ntheorem one : 1 = 1 := rfl\n'
            source.write_text(original)
            output = root / 'diagnostics'
            commands = []

            def launch(command, **kwargs):
                commands.append(command)
                report = Path(command[command.index('--report-json') + 1])
                report.write_text(json.dumps({'elapsed_seconds': 2, 'peak_rss_mib': 100}))
                return Mock(wait=Mock(return_value=exit_code), poll=Mock(return_value=exit_code))

            with patch.object(prefixes, '__file__', str(root / 'scripts' / 'profile.py')), \
                    patch.object(sys, 'argv', ['profile', str(source), '--through', '1', '2',
                                               '--output', str(output), '--serialize']), \
                    patch.object(prefixes.subprocess, 'Popen', side_effect=launch):
                self.assertEqual(prefixes.main(), exit_code)
            self.assertEqual(source.read_text(), original)
            for command in commands:
                self.assertEqual(Path(command[1]).name, 'check-lean-safe.py')
                self.assertIn('--wait-for-lock', command)
                self.assertTrue(Path(command[command.index('-o') + 1]).is_relative_to(output.resolve()))
            return commands, json.loads((output / 'summary.json').read_text())

    def test_runs_sequential_isolated_copies(self):
        commands, summary = self.run_fake_check(0)
        self.assertEqual(len(commands), 2)
        self.assertTrue(all(row['valid'] for row in summary['results']))

    def test_failed_prefix_stops_and_is_not_ranked(self):
        commands, summary = self.run_fake_check(1)
        self.assertEqual(len(commands), 1)
        self.assertFalse(summary['results'][0]['valid'])


class GuardTests(unittest.TestCase):
    def run_guard(self, readings, running=False):
        with tempfile.TemporaryDirectory() as directory:
            report = Path(directory) / 'usage.json'
            proc = Mock(pid=4321, returncode=0)
            proc.poll.side_effect = [None, None] if running else [None, 0, 0]

            def stopped(**kwargs):
                proc.returncode = -15
                return -15

            proc.wait.side_effect = stopped
            with patch.object(sys, 'argv', ['check', '--report-json', str(report), 'Example.lean']), \
                    patch.object(guard.tempfile, 'gettempdir', return_value=directory), \
                    patch.object(guard.signal, 'signal'), \
                    patch.object(guard.subprocess, 'run', side_effect=readings), \
                    patch.object(guard.subprocess, 'Popen', return_value=proc) as launch, \
                    patch.object(guard.os, 'killpg') as kill, \
                    patch.object(guard.time, 'sleep'):
                try:
                    result = guard.main()
                except subprocess.CalledProcessError:
                    result = 'inspection failed'
                self.assertEqual(launch.call_args.args[0][:3], ['lean', '-M24576', '-j1'])
                self.assertTrue(launch.call_args.kwargs['start_new_session'])
                return result, json.loads(report.read_text()), kill.call_count

    def test_success_reports_measured_peak(self):
        result, report, kills = self.run_guard([Mock(stdout=''), Mock(stdout='4321 2048\n')])
        self.assertEqual(result, 0)
        self.assertEqual(report['peak_rss_mib'], 2)
        self.assertEqual(kills, 0)

    def test_rss_limit_still_stops_process_group(self):
        result, report, kills = self.run_guard(
            [Mock(stdout=''), Mock(stdout=f'4321 {29000 * 1024}\n')], running=True)
        self.assertEqual(result, 137)
        self.assertTrue(report['stopped_by_guard'])
        self.assertEqual(kills, 1)

    def test_inspection_failure_still_stops_process_group(self):
        result, report, kills = self.run_guard(
            [Mock(stdout=''), subprocess.CalledProcessError(1, ['ps'])], running=True)
        self.assertEqual(result, 'inspection failed')
        self.assertEqual(report['child_returncode'], -15)
        self.assertEqual(kills, 1)


if __name__ == '__main__':
    unittest.main()
