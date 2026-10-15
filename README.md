# Integer multiplication in Lean

**Integer multiplication below `n log n` is proved in Lean on Mathlib's finite Turing machines.**

## Main result

`IntegerMultBounds.MathlibTM2.statement` is unconditional: one fixed
`Turing.FinTM2` machine multiplies every pair of natural numbers, with standard
binary input/output encodings, in worst-case time `O(n (log n)^(1-kappa))`.
The construction proves the positive saving
`kappa = 296 / (10^11 * 2^131)`, approximately `1.09e-48`, where `n` is the
total encoded input length. See [the completed plan](plan/C-mathlib-end-to-end.md).

This completed proof is the primary route. The [retention audit](docs/proof-retention.md)
lists its dependencies and legacy removal candidates; the retired native controller is preserved in Git history.

## Stronger compact-control target

The original target is an actual deterministic machine with a fixed finite alphabet and
a fixed number of one-dimensional tapes, correct on every positive input
length, with worst-case runtime
`O(n (max(ceil(log₂ n), 1))^(1 - 83/10^12))`.

`IntegerMultBounds/Machine.lean` defines the machine semantics and the target
proposition `IntegerMultBounds.Machine.EndToEnd`. This is a proposition to be
proved, not a theorem or an assumed interface. Its transition function only
sees the finite state and scanned symbols. Each step writes at most one cell
per tape and moves each head at most one cell. Constants and the machine are
chosen before quantifying over inputs.

## Mathlib statement

`IntegerMultBounds/MathlibTM2/Statement.lean` states the target with Mathlib definitions only:
`Turing.TM2ComputableInTime` with Mathlib's binary encodings `encodingProd` and
`encodingNatBool`. `MathlibTM2.statement_of_endToEnd` proves `EndToEnd → MathlibTM2.Statement`,
so an auditor of the final result reads only that statement and its axioms. Applied to the
elementary multiplier, the same bridge gives the unconditional `MathlibTM2.mul_quadratic`, a
quadratic-time Mathlib machine. [The note](docs/mathlib-tm2/mathlib-tm2.pdf) explains the
statement and the simulation; `lake env lean MathlibTM2Check.lean` checks the axioms.

`IntegerMultBounds/MathlibTM2/Theorem.lean` proves `MathlibTM2.statement : MathlibTM2.Statement`:
a fixed `Turing.FinTM2` machine multiplies in worst-case time `O(n (log n)^(1-κ))` for an
explicit `κ > 0`. To verify it: read `Statement.lean` (its imports are Mathlib only), run
`lake build`, then `lake env lean FastPathCheck.lean`, which prints nothing when `statement` and
the main intermediate theorems depend on `propext`, `Classical.choice` and `Quot.sound` only
(`#guard_msgs` fails loudly otherwise). [The note](docs/fast-mult/fast-mult.pdf) describes the
machine and the proof.

## Status

The primary Mathlib host route is complete: the fixed machine, recursive
layers, transforms, resampling, CRT routing, products, output and total-time
bound are proved by `MathlibTM2.statement`.

The superseded native CompactComplex controller and its unused dependent
wrappers have been retired: 635 modules and 109,973 lines. The two
CompactComplex modules imported by the completed proof remain, along with all
other proof dependencies, compatibility bridges and focused audit dependencies.
See the [retirement record](docs/retired-compact-complex.md) for the exact
manifest and the Git revision from which the old development can be restored.

[PLAN.md](PLAN.md) records the completed result and the surviving supporting
components. The larger `83/10^12` saving remains a separate unproved target;
its retired native controller can be recovered from history if that route is
resumed. No algorithmic or runtime assumption remains in the completed
Mathlib theorem.

## Building and verification

Install the version of Lean in `lean-toolchain`, then use the guarded local
verification commands:

```sh
python3 scripts/build-lean-guarded.py IntegerMultBounds
python3 scripts/check-lean-safe.py AxiomAudit.lean
python3 scripts/check-lean-safe.py MathlibTM2Check.lean
python3 scripts/check-lean-safe.py FastPathCheck.lean
python3 scripts/check-lean-safe.py CompletedProofCheck.lean
```

For local component checks, use `python3 scripts/check-lean-safe.py FILE`.
This runner permits one check per workspace, uses one Lean thread and a
24576 MiB Lean memory limit, and stops the process group if its observed RSS
exceeds 28672 MiB or the check runs past twenty minutes. It also stops child
processes if monitoring fails or the check is interrupted. Dependencies must already have compiled artifacts;
it does not launch a broad build. The guarded build stops at 80 GiB combined
RSS or three hours. Both runners share one workspace-wide lock.

Lean and mathlib are pinned to v4.34.1; `lake-manifest.json` pins transitive
dependencies. No theorem in this project uses a custom axiom or an admitted
proof.

`AxiomAudit.lean` checks public and private project declarations, transitively,
allowing only Lean's standard `propext`, `Quot.sound`, and `Classical.choice`.
It rejects admitted proofs, custom axioms, and native-evaluation axioms. CI
builds the project and runs this audit.

## References

### Primary sources

- Douglas Colkitt, *A sharper exponent for integer multiplication*, research
  draft, [CrocSwap/integer-mult-bounds](https://github.com/CrocSwap/integer-mult-bounds),
  commit [`6e56487`](https://github.com/CrocSwap/integer-mult-bounds/tree/6e564879f51ae16f23d392e9e196c605f36d90df)
  (October 7, 2026).
- Its pinned OpenAI manuscript,
  [*Integer multiplication below n log n*](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026),
  in [openai/math](https://github.com/openai/math), commit `adc7f12`.
- David Harvey and Joris van der Hoeven,
  [*Integer multiplication in time O(n log n)*](https://doi.org/10.4007/annals.2021.193.2.4),
  Annals of Mathematics 193(2), 2021, 563–617. The upstream proof uses this
  multiplier as a subroutine. Lemma and section numbers in `NLogN/` refer to the
  [author-hosted manuscript](https://www.texmacs.org/joris/nlogn/nlogn.pdf).

### Classical results formalized here

- J. W. Cooley and J. W. Tukey, [*An algorithm for the machine calculation of
  complex Fourier series*](https://doi.org/10.1090/S0025-5718-1965-0178586-1),
  Mathematics of Computation 19(90), 1965, 297–301. (`NLogN/FFT.lean`)
- A. Schönhage and V. Strassen, [*Schnelle Multiplikation großer
  Zahlen*](https://doi.org/10.1007/BF02242355), Computing 7, 1971, 281–292.
  (`Schoenhage/`)
- L. I. Bluestein, [*A linear filtering approach to the computation of discrete
  Fourier transform*](https://doi.org/10.1109/TAU.1970.1162132), IEEE
  Transactions on Audio and Electroacoustics 18(4), 1970, 451–455.
  (`NLogN/Bluestein.lean`)
- R. C. Agarwal and J. W. Cooley, [*New algorithms for digital
  convolution*](https://doi.org/10.1109/TASSP.1977.1162981), IEEE Transactions
  on Acoustics, Speech, and Signal Processing 25(5), 1977, 392–410.
  (`NLogN/Multidim.lean`)

### Lean libraries

- [complexitylib](https://github.com/SamuelSchlesinger/complexitylib), commit
  [`3f4b5fe`](https://github.com/SamuelSchlesinger/complexitylib/tree/3f4b5fee8bbd49721a5b70473c81bf3db2e7500d),
  for the machine composition design (no code imported).
- [mathlib4](https://github.com/leanprover-community/mathlib4), v4.34.1.

The local `integer-mult-bounds/` checkout is reference material and is ignored
by this project's Git repository. The Lean project does not execute or trust
the source repository's Python certificates.

## License

[MIT](LICENSE).
