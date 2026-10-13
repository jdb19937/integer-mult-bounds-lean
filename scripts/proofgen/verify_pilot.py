#!/usr/bin/env python3
"""Check the pilot, audit axioms, and require Lean to reject three corruptions.

All Lean invocations go through the workspace's guarded, serialized checker.
Existing LayoutGenRun dependencies must already be built. Times include guard
startup and any wait for the shared lock; they are not isolated Lean benchmarks.
"""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location('sequence_generator', ROOT / 'scripts/generate_lean_sequence.py')
GENERATOR = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GENERATOR)


def check(path, *, output=None, reject=False):
    command = [sys.executable, 'scripts/check-lean-safe.py', '--wait-for-lock', str(path)]
    if output is not None:
        command += ['-o', str(output)]
    started = time.monotonic()
    result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    seconds = time.monotonic() - started
    success = (result.returncode == 1 and 'error:' in result.stdout) if reject else result.returncode == 0
    if not success:
        print(result.stdout)
        raise RuntimeError(f'{path.name}: unexpected check result {result.returncode}')
    print(f'{path.name}: {"rejected as expected" if reject else "passed"} ({seconds:.2f}s)', flush=True)
    if not reject:
        print(result.stdout.strip(), flush=True)
    return seconds


def main():
    manifest = json.loads((ROOT / 'scripts/proofgen/layout_setup.json').read_text())
    generated = GENERATOR.render(manifest)
    folder = ROOT / 'IntegerMultBounds/Schoenhage'
    if (folder / 'LayoutSequenceGenerated.lean').read_text() != generated:
        raise RuntimeError('Regenerate LayoutSequenceGenerated.lean first')
    for name in ['CertifiedSequence', 'LayoutSequenceGenerated']:
        check(folder / f'{name}.lean', output=ROOT / f'.lake/build/lib/lean/IntegerMultBounds/Schoenhage/{name}.olean')
    check(folder / 'LayoutSequencePilot.lean')
    with tempfile.TemporaryDirectory(prefix='sequence-check-', dir=ROOT / 'scripts/proofgen') as temporary:
        changed = copy.deepcopy(manifest)
        stages = changed['cases'][0]['stages']
        stages[0], stages[1] = stages[1], stages[0]
        mismatched = GENERATOR.render(changed)
        changed = copy.deepcopy(manifest)
        changed['cases'][0]['stages'][0]['command'] = 'nPhase'
        wrong_program = GENERATOR.render(changed)
        missing_join = generated.replace('.bound + 1 := by', '.bound + 0 := by', 1)
        assert missing_join != generated
        for name, source in [('MismatchedBanks', mismatched), ('WrongProgram', wrong_program), ('UnpaidJoin', missing_join)]:
            path = Path(temporary) / f'{name}.lean'
            path.write_text(source)
            check(path, reject=True)
    print('All positive checks, transitive axiom audit, and kernel rejection tests passed.')


if __name__ == '__main__':
    main()
