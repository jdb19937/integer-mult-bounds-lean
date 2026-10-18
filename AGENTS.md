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

# Proof style and checking cost

The CI runner has about 16 GB and builds four modules at once. Keep every
module under about 4 GB peak; measure with `check-lean-safe.py`.

- Prefer structural proofs to generated certificates. Prove a lemma over an
  arbitrary list, circuit or schedule with hypotheses, and instantiate the
  concrete data last. The kernel blows up when it must compare two large
  concrete terms (an abbreviation against its expansion, `Fin 1176` against
  `Fin (choose 49 2)`).
- Prefer the simplest statement the main proof needs. Remove code the main
  theorem does not use, and leave a one-line note with the restore commit.
- No `sorry`, new axioms, `native_decide` or raised `maxHeartbeats` and
  `maxRecDepth`. When a proof times out, restructure it.
- Use `decide +kernel` for large finite checks. Kernel memory is freed per
  declaration, so split a big check into chunk theorems joined by a generic
  lemma over the chunk list (`sum_map_chunks`, `all_of_chunks`, `*_flatten`).
- Check each fact once. Factor parts that do not depend on a case index out
  of per-case checks (the T16 frame check is per stage, not per replica).
- Write computable checks with structural recursion over lists, not
  `Fin.foldl` or well-founded recursion, which the kernel reduces slowly.
- Between two concrete tape banks or vectors, use
  `fin_cases i <;> first | (simp [..]; done) | rfl` or unfold, not a bare `rfl`.
- Keep definitions that check files evaluate in a small module of their own,
  mark large checkers `@[irreducible]`, and import only that module, so check
  files have a narrow import closure. Never `import Mathlib.Tactic`.
- Under the module system, proof-only edits do not rebuild dependents, but
  changes to exposed definitions do. Keep heavy data out of exposed statements.
- Generated data files come from a deterministic script that records pinned
  provenance.
- Find slow declarations with `set_option profiler true` or
  `-Dtrace.profiler=true -Dtrace.profiler.threshold=1000`.
