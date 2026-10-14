#!/usr/bin/env python3
"""Run one Lean check with bounded memory and a workspace-wide process lock."""
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

# User-authorized modest increase; retain one check and a hard RSS ceiling.
LEAN_MIB = 24576
GUARD_MIB = 28672
# Stop runaway elaboration (loops) rather than letting it grow.
TIMEOUT_S = 1200


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--wait-for-lock', action='store_true',
                        help='queue this check behind the current workspace verifier')
    parser.add_argument('lean_args', nargs=argparse.REMAINDER,
                        help='Lean arguments, normally a source file and optional -o path')
    args = parser.parse_args()
    if not args.lean_args:
        parser.error('supply a Lean source file')
    def interrupted(_signal, _frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    # Never allow callers to defeat this runner's memory/thread limits.
    if any(arg.startswith(('-M', '--memory', '-j', '--threads')) for arg in args.lean_args):
        parser.error('memory and thread limits are fixed by this runner')
    root = Path(__file__).resolve().parent.parent
    key = hashlib.sha256(str(root).encode()).hexdigest()[:16]
    lock_path = Path(tempfile.gettempdir()) / ('integer-mult-lean-' + key + '.lock')
    with lock_path.open('a') as lock:
        try:
            lock_mode = fcntl.LOCK_EX if args.wait_for_lock else fcntl.LOCK_EX | fcntl.LOCK_NB
            fcntl.flock(lock, lock_mode)
        except BlockingIOError:
            print('Another guarded Lean check is running; no check started.', file=sys.stderr)
            return 75
        # Verify process inspection works before launching any expensive work.
        def usage(group):
            result = subprocess.run(['ps', '-axo', 'pgid=,rss='], check=True,
                                    text=True, capture_output=True)
            return sum(int(fields[1]) for line in result.stdout.splitlines()
                       if len(fields := line.split()) == 2 and int(fields[0]) == group)
        usage(-1)
        # Avoid retaining Lake's dependency/configuration heap alongside Lean.
        # All dependencies must already be built; this is a checker, not a builder.
        libdirs = sorted((root / '.lake' / 'packages').glob('*/.lake/build/lib/lean'))
        libdirs.append(root / '.lake' / 'build' / 'lib' / 'lean')
        env = os.environ.copy()
        env['LEAN_PATH'] = os.pathsep.join(str(p) for p in libdirs)
        proc = subprocess.Popen(['lean', f'-M{LEAN_MIB}', '-j1', *args.lean_args],
                                cwd=root, env=env, start_new_session=True)
        peak = 0
        stopped = False
        start = time.monotonic()
        try:
            while proc.poll() is None:
                rss = usage(proc.pid)
                peak = max(peak, rss)
                if rss > GUARD_MIB * 1024:
                    print(f'Stopping check: process group exceeded {GUARD_MIB} MiB RSS.', file=sys.stderr)
                    stopped = True
                    break
                if time.monotonic() - start > TIMEOUT_S:
                    print(f'Stopping check: exceeded {TIMEOUT_S} s.', file=sys.stderr)
                    stopped = True
                    break
                time.sleep(0.05)
        finally:
            # Also stop on interruption or a failed monitor; never leave children behind.
            if proc.poll() is None:
                try:
                    os.killpg(proc.pid, signal.SIGTERM)
                except ProcessLookupError:
                    pass
                try:
                    proc.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    try:
                        os.killpg(proc.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    proc.wait()
            print(f'Guarded check peak RSS: {peak / 1024:.1f} MiB.', file=sys.stderr)
        return 137 if stopped else (proc.returncode if proc.returncode >= 0 else 128 - proc.returncode)


if __name__ == '__main__':
    sys.exit(main())
