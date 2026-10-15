#!/usr/bin/env python3
"""Locate memory growth by checking source prefixes at complete-command boundaries.

Every prefix starts a fresh guarded Lean process with the same cached imports.
The source is copied, never edited; diagnostic artifacts stay in the output
directory. Prefix peaks include earlier declarations and imported environments,
so peak differences are not individual proofs' allocations.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile


def prefix_source(source, through):
    lines = source.splitlines(keepends=True)
    if not 1 <= through <= len(lines):
        raise ValueError(f'boundary {through} is outside 1..{len(lines)}')
    # Lean's own exit command stops parsing at this boundary. No placeholders
    # or replacement axioms are introduced, even inside an open namespace.
    return ''.join(lines[:through]).rstrip('\n') + '\n\n#exit\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('--through', type=int, nargs='+', required=True,
                        help='inclusive line numbers after complete commands, in increasing order')
    parser.add_argument('--output', type=Path,
                        help='new output directory (default: a fresh .lake/profiling directory)')
    parser.add_argument('--serialize', action='store_true',
                        help='also serialize each partial module into the diagnostic directory')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    source_path = args.source.resolve()
    try:
        relative = source_path.relative_to(root)
        source = source_path.read_text()
        if source_path.suffix != '.lean':
            raise ValueError('source must be a Lean file in this workspace')
        if args.through != sorted(set(args.through)):
            raise ValueError('boundaries must be unique and increasing')
        prefixes = [(line, prefix_source(source, line)) for line in args.through]
    except (OSError, ValueError) as error:
        parser.error(str(error))
    if args.output:
        output = args.output.resolve()
        # Never overwrite a previous measurement or a source tree.
        output.mkdir(parents=True, exist_ok=False)
    else:
        parent = root / '.lake' / 'profiling'
        parent.mkdir(parents=True, exist_ok=True)
        output = Path(tempfile.mkdtemp(prefix='prefix-memory-', dir=parent))
    summary = {
        'source': str(source_path),
        'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
        'serialize': args.serialize,
        'scope': 'Fresh sequential guarded processes; cached imports; lock waiting excluded.',
        'interpretation': 'Cumulative prefix peaks, not exclusive per-proof allocations. '
                          'Invalid boundaries and failed checks must not be ranked.',
        'results': [],
    }
    print(f'Results: {output}', flush=True)
    for line, text in prefixes:
        run = output / f'through-{line}'
        snapshot = run / 'source'
        copied = snapshot / relative
        copied.parent.mkdir(parents=True)
        copied.write_text(text)
        report = run / 'usage.json'
        log = run / 'check.log'
        command = [sys.executable, str(root / 'scripts' / 'check-lean-safe.py'),
                   '--wait-for-lock', '--report-json', str(report), str(copied),
                   '--root=' + str(snapshot)]
        if args.serialize:
            command.extend(['-o', str(run / 'prefix.olean')])
        print(f'Checking through line {line}...', flush=True)
        with log.open('w') as stream:
            proc = subprocess.Popen(command, cwd=root, stdout=stream, stderr=subprocess.STDOUT)
            try:
                code = proc.wait()
            finally:
                if proc.poll() is None:
                    # Interrupt the guard, which cleans up its entire Lean group.
                    proc.terminate()
                    proc.wait()
        row = {'through_line': line, 'exit_code': code, 'log': str(log),
               'valid': code == 0}
        if report.exists():
            row.update(json.loads(report.read_text()))
        summary['results'].append(row)
        (output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
        if code:
            print(f'Check failed; inspect {log}. No memory ranking made.', file=sys.stderr)
            return code
        print(f"  {row['elapsed_seconds']:.1f} s, {row['peak_rss_mib']:.1f} MiB peak", flush=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
