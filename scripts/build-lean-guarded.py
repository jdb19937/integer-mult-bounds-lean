#!/usr/bin/env python3
"""Run a parallel `lake build` under a total memory budget and a workspace-wide lock.

The whole build runs in its own process group; if the group's combined RSS exceeds the
budget, or the build runs past the time limit, every process in the group is stopped.
"""
import argparse
import fcntl
import hashlib
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time

# Combined RSS of lake and all its Lean processes. The machine has 128 GB; an unguarded
# parallel build once grew past 200 GB.
BUDGET_GIB = 80
TIMEOUT_S = 3 * 3600


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('targets', nargs='*', help='lake build targets (default: the default target)')
    parser.add_argument('--budget-gib', type=int, default=BUDGET_GIB)
    parser.add_argument('--project-dir', type=Path,
                        help='build a source snapshot while retaining this workspace\'s lock')
    args = parser.parse_args()

    def interrupted(_signal, _frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)

    root = Path(__file__).resolve().parent.parent
    build_root = args.project_dir.resolve() if args.project_dir else root
    if not build_root.is_dir():
        parser.error(f'project directory does not exist: {build_root}')
    key = hashlib.sha256(str(root).encode()).hexdigest()[:16]
    # Same lock as check-lean-safe.py: never run a build and a guarded check at once.
    lock_path = Path(tempfile.gettempdir()) / ('integer-mult-lean-' + key + '.lock')
    with lock_path.open('a') as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            print('Another guarded Lean check or build is running; no build started.', file=sys.stderr)
            return 75

        def usage(group):
            result = subprocess.run(['ps', '-axo', 'pgid=,rss='], check=True, text=True, capture_output=True)
            return sum(int(f[1]) for line in result.stdout.splitlines()
                       if len(f := line.split()) == 2 and int(f[0]) == group)
        usage(-1)

        proc = subprocess.Popen(['lake', 'build', *args.targets], cwd=build_root, start_new_session=True)
        peak = 0
        stopped = False
        start = time.monotonic()
        try:
            while proc.poll() is None:
                rss = usage(proc.pid)
                peak = max(peak, rss)
                if rss > args.budget_gib * 1024 * 1024:
                    print(f'Stopping build: process group exceeded {args.budget_gib} GiB RSS.', file=sys.stderr)
                    stopped = True
                    break
                if time.monotonic() - start > TIMEOUT_S:
                    print(f'Stopping build: exceeded {TIMEOUT_S} s.', file=sys.stderr)
                    stopped = True
                    break
                time.sleep(0.2)
        finally:
            if proc.poll() is None:
                try:
                    os.killpg(proc.pid, signal.SIGTERM)
                except ProcessLookupError:
                    pass
                try:
                    proc.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    try:
                        os.killpg(proc.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    proc.wait()
            elapsed = time.monotonic() - start
            print(f'Guarded build peak RSS: {peak / 1024 / 1024:.1f} GiB, {elapsed / 60:.1f} min.', file=sys.stderr)
        return 137 if stopped else (proc.returncode if proc.returncode >= 0 else 128 - proc.returncode)


if __name__ == '__main__':
    sys.exit(main())
