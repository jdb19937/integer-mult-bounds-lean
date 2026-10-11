# Local verification resources

The user experienced a system out-of-memory crash during parallel Lean checks.

- Only the root agent launches local Lean verification; workers edit source and report readiness.
- Run one check at a time through `python3 scripts/check-lean-safe.py FILE`.
- The runner holds a workspace-wide lock, uses one Lean thread, sets a 2048 MiB Lean memory limit, and stops its process group when observed RSS exceeds 2560 MiB.
- Do not launch unguarded Lean processes or broad local Lake builds.
- If a check reaches the memory guard, reduce its imports or elaboration work rather than raising the cap.
- Preserve default proof limits and all existing proof-integrity requirements.
