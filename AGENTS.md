# Local verification resources

An unguarded parallel Lean build once grew past 200 GB and crashed the machine (128 GB, 16 cores).
Every local Lean process runs under a memory guard.

- Check single files with `python3 scripts/check-lean-safe.py FILE`: one Lean thread, a 24576 MiB Lean memory limit, stopped when its RSS exceeds 28672 MiB or it runs past 20 minutes.
- Build with `python3 scripts/build-lean-guarded.py [TARGETS]`: a normal parallel `lake build`, stopped when the combined RSS of all its processes exceeds 80 GiB or it runs past 3 hours.
- Both share one workspace-wide lock, so only one check or build runs at a time.
- Add `--wait-for-lock` before the single-file checker arguments to queue a check; without it, a busy lock exits with status 75 without starting Lean.
- Do not launch Lean or Lake outside these two scripts.
- Preserve default proof limits and all existing proof-integrity requirements.

# Proof naming

Use conventional mathematical names such as `x`, `y`, `z`, `i`, and `n` for
generic values and indices. Prefer descriptive names when they convey a
meaningful role, such as `parentLive`, `childVolume`, `rowCount`, or `savedStack`,
and name hypotheses by the facts they establish. Avoid replacing single-letter
names with generic ordinal names such as `first`, `second`, and `third` unless
order matters. Use this principle for new proofs and when revising existing proofs.
