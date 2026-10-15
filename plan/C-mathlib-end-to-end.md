# C. Proved Mathlib end-to-end multiplier

Part of the [plan](../PLAN.md). See [COMPONENTS.md](../COMPONENTS.md) for what each file proves.

## Result and scope

`IntegerMultBounds.MathlibTM2.statement : MathlibTM2.Statement` is an
unconditional theorem. It constructs one fixed `Turing.FinTM2` machine that
multiplies every pair of natural numbers with the standard Mathlib binary
encodings in worst-case time `O(n (log n)^(1-kappa))`, where `n` is the total
encoded input length and `kappa > 0`.

The public theorem `MathlibTM2.mulInTime` proves saving `2^-66`. The exact
internal margin is `Cost.totKappa = 296 / (10^11 * 2^37)`, between `2^-66`
and `2^-65`, with positivity and the exact value proved by `tot_kappa_pos`
and `tot_kappa_eq`. This establishes multiplication below `n log n`. It does not
establish the larger saving `83/10^12` in the original compact-control target
`Machine.EndToEnd`, or the particular native-bank interfaces tracked in parts
2–B of the [archived native roadmap](archive/native-roadmap.md). Those
targets remain historical alternatives; their open rows are not gaps in this
completed theorem.

## How the proof closes

The contribution merged in PR #3 supplies the recursive factor procedures,
layout and transform loops, table generation, CRT routing, both resampling
directions, chirps, pointwise multiplication, final scaling, carry output and
cleanup. `MainCorrect.mn_hostMul_ge` verifies the assembled program beyond its
cutoff; `statement_of_dispatch` handles shorter inputs with finite control.
The actual stage costs are matched to `Cost.totBound`, and
`Cost.MatchSynLoop.mr_loop_cost_le` closes the final transform-cost premise of
`Fast.Main.fast_statement_of`. `Theorem.lean` applies that proved bound, so
`MathlibTM2.statement` has no program, correctness or cost assumptions.

### Complete fixed machine and sub-n-log-n bound

- Math milestone: `IntegerMultBounds.MathlibTM2.statement` — There exists a positive exponent saving and a fixed finite Mathlib machine computing integer multiplication within the corresponding sub-n-log-n worst-case bound, with no algorithmic hypotheses.
- Tape milestone: `IntegerMultBounds.MathlibTM2.statement` — The same theorem includes the concrete finite-machine witness, standard input/output encodings, correctness on every input pair and a bound on actual TM2 steps; the model is Mathlib's finite multi-stack machine.

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Complete numerical algorithm and exact recovery | `MathlibTM2/Mult/*` | ✅ | — | The CRT/resampling/chirp/synthetic-convolution pipeline returns the exact product coefficients; the existing `PipelineOutput` bridge also provides exact-width native output semantics. |
| Recursive factors, layer and normalized public kernel | `MathlibTM2/Node/*` | ✅ | ✅ | `layer_exec` supplies recursive factor execution by level induction; `topProg_exec` and `topProg_exec_Hl` include phases, row padding, base-m pieces, normalization and truncation. The earlier abstract factor-program premise is discharged by this implementation. |
| Complete host stages and assembled multiplier | `MathlibTM2/Fast/*`, `MathlibTM2/Host/*` | ✅ | ✅ | Runtime-generated parameters, tables, layouts, CRT, resampling, synthetic forward/opposite transforms, chirps, products, scaling, carry output, cleanup and small-input dispatch compose into a single fixed host program and hence a finite Mathlib machine. |
| Actual step costs and final exponent | `MathlibTM2/Cost/*` | ✅ | ✅ | Component execution costs match the analytic bounds; `mr_loop_cost_le` discharges the final loop-cost premise, and `tot_direct_htime` supplies the sub-n-log-n bound with the positive `totKappa` witness. |
| Unconditional theorem and axiom checks | `MathlibTM2/Theorem`, `MathlibTM2/Statement`, `FastPathCheck`, `MathlibTM2Check`, `CompletedProofCheck`, `AxiomAudit` | ✅ | ✅ | `statement` proves the Mathlib-only proposition without arguments. The library audit and focused checks reject dependencies beyond `propext`, `Classical.choice` and `Quot.sound`. `CompletedProofCheck` independently audits the theorem's import closure without the all-components root, protecting the primary route during legacy retirement. |

M2 uses actual direct CRT routing linear in the axis count, with complete
runtime setup and cleanup, and reuses the existing linear resampling exposure.
The final parameters are `epsilon=2^-5`, `c=2^-32`, and `lambda'=1-1/10^11`.
The public exponent saving is `2^27` times the historical M1 value `2^-93`;
this ratio is not a measured runtime speedup.

## Validation

Use the repository's guarded build and single-file checker for the library,
`AxiomAudit.lean`, `MathlibTM2Check.lean` and `FastPathCheck.lean`. The full audit
includes private project declarations transitively; the focused fast-path
check asserts the final theorem's exact three-axiom dependency set.

Final M2 verification on 2026-10-15 refreshed 113 affected modules and checks
with the guarded single-file checker. `CompletedProofCheck.lean` audited
111,887 declarations; `CRTControlCheck.lean` audited 172 contracts. Both passed,
with peak RSS below 4.3 GiB. No full build ran and no proof limits were raised.

Historical library-wide validation on 2026-10-14 against merge `9a7e575f` (PR #3):

- Guarded library build: passed, 7,559 jobs, 5.0 minutes, 26.8 GiB peak combined RSS.
- Full axiom audit: passed for 158,434 declarations.
- `FastPathCheck.lean`: passed, including the unconditional final theorem's exact standard-axiom assertion.
- `MathlibTM2Check.lean`: passed, retaining the original simulation and quadratic multiplier checks.
- Plan regeneration and whitespace checks: passed.

Validation used the merged proof source, including its existing local
elaboration-limit settings; it did not increase any proof or verifier limit.
