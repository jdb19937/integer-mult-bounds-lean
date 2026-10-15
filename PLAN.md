# Plan and progress

## Bound scoreboard

We measure progress by the **proved exponent saving `kappa`** in worst-case
time `O(n (log n)^(1-kappa))`. Larger saving means a smaller time exponent.

| Bound | Exponent saving `kappa` | Status |
| --- | --- | --- |
| **Current unconditional result** | **`296 / (10^11 * 2^131)`, approximately `1.09e-48`** | Proved on one fixed finite Mathlib machine, for all input pairs. |
| **Next improvement: tune the existing construction** | **To be established; must exceed the current saving** | First check admissible parameters, then prove the improved actual-step bound. |
| **Goal: match the selected community construction** | **`836330098538459 / 500000000000000000 = 0.001672660197076918`** | Upstream construction is conditional; our goal is an unconditional machine theorem at this exact saving. |

The goal corresponds to a log exponent of `0.998327339802923082`.
These are asymptotic exponent bounds, not measured execution speedups.
Update the current-result row only after the stronger machine theorem passes
the guarded checks and axiom audit; parameter arithmetic or a finite
certificate alone does not improve the proved multiplication bound.

**Integer multiplication below `n log n` is proved.**
`IntegerMultBounds.MathlibTM2.statement` constructs a fixed finite Mathlib
machine that multiplies every input pair correctly in worst-case time
`O(n (log n)^(1-kappa))`, with positive saving
`kappa = 296 / (10^11 * 2^131)`. No algorithmic or runtime assumption remains.

## Completed proof

| Part of the proof | Source | Mathematics | Tape | Files |
| --- | --- | --- | --- | --- |
| [Proved Mathlib end-to-end multiplier](plan/C-mathlib-end-to-end.md) | — | ✅ 1/1 | ✅ 1/1 | 227 |

The [proof details](plan/C-mathlib-end-to-end.md) cover the numerical
algorithm, recursive layers, transforms, resampling, CRT routing, exact
recovery, fixed-machine assembly and actual step bound. All are complete.
The machine model is Mathlib's `Turing.FinTM2`, with standard binary encodings.
The Files column counts the components listed in that detail file; the full
transitive proof dependency set is larger, as recorded by the
[retention audit](docs/proof-retention.md).

The guarded build and library-wide axiom audit passed after the latest
native-wrapper retirement. `CompletedProofCheck.lean` independently audits
the completed theorem's import closure; the library and focused checks allow
only `propext`, `Classical.choice` and `Quot.sound`.

## Improvement milestones

The next research goal is to reproduce the stronger bounds developed in
[CrocSwap/integer-mult-bounds](https://github.com/CrocSwap/integer-mult-bounds)
using the completed Mathlib machine proof as the foundation. These are new
milestones, not prerequisites for the result above.

The [implementation plan](plan/D-sharper-bound.md) pins the selected source,
maps the reuse candidates and orders the work. Start by tuning the existing
construction: its saving is `epsilon * cParam * (1 - tau)`, where currently
`epsilon = 2^-75` and `cParam = 2^-56`. Larger admissible values may improve the
bound while reusing the existing algorithm and correctness infrastructure.
The achievable improvement remains unproved. Importing better finite circuits
alone retains these very small parameter factors.

| ID | Milestone | Status | Completion criterion and effect on bound |
| --- | --- | --- | --- |
| P1 | Find safe parameter headroom | **Next** | Inventory every constraint on `epsilon` and `cParam`, including sizing, layouts, precision and actual costs; give an exact feasible candidate and its prospective saving. No proved-bound change yet. |
| P2 | Prove the first parameter improvement | Planned | Implement the P1 candidate, reprove all affected bounds and expose an explicit stronger `MulInTime` theorem. Pass guarded verification and axiom checks; record the exact new saving in the scoreboard. |
| P3 | Generalize the bound for further tuning | Planned | Parameterize the cost and size contracts needed for repeated tuning, recover the existing instances and identify the active bottleneck. Record any further improvement only when its machine theorem is proved. |
| S0 | Pin the selected source | **Done: source identity only** | Exact upstream revision, selected target and six record digests are recorded in the source pin. Full supplier replay and obligation proofs remain below. |
| S1 | Map the target to our host | Planned | Trace each inherited assumption to its precise source definition and map all 47 outer inequalities to local stages. Identify required analytic or program changes and explain how the target saving survives the transfer. |
| S2 | Prove both selected finite suppliers | Planned | Reproduce pinned replay and prove complex and bit words, dirty restoration, frames, complete rank/cost profiles and strict endpoint inequalities in Lean. This proves component bounds, not the final saving. |
| S3 | Prove uniform recursion and workspace | Planned | Discharge all-size compilation, common labels, mutable sources, seven bootstrap stages, reserve coefficients and cutoff conditions for the selected suppliers. |
| S4 | Realize and price the new Mathlib program | Planned | Prove whole-call hosting, routing, precision, exact recovery and all actual-step costs at the required sharp exponents. |
| S5 | Prove the exact target end to end | Planned | Prove unconditional `MulInTime` at the exact goal saving; pass the guarded build and full/focused axiom audits, then update the scoreboard. |

P1–P2 are the shortest route to a stronger proved bound. P3 and S1 establish
the interfaces for the larger supplier integration. Each completed logical
section gets its own checked commit and push. These planning statuses are
maintained explicitly; the completed-proof table above is generated separately.

The external project's currently reviewed saving is approximately
`0.001672660197076918`, but its complete asymptotic multiplication theorem
remains conditional. Reproducing finite certificates alone will not complete
this roadmap. Pin and recheck the selected result before implementation;
its [selected record](https://github.com/CrocSwap/integer-mult-bounds/blob/main/certificates/selected-result.json)
tracks a moving research frontier.

## Archived route and reusable work

The [archived native-machine roadmap](plan/archive/native-roadmap.md)
preserves the old manuscript-section tables and the separate `83/10^12`
compact-control target. Its yellow rows describe unfinished historical native
interfaces; they are not gaps in the completed Mathlib proof and are not the
active work queue. The archive is preserved for reference, not automatically
refreshed against the current library.

Reusable mathematics and surviving implementations remain indexed in
[COMPONENTS.md](COMPONENTS.md). The [retention audit](docs/proof-retention.md)
and retirement records document which code supports the completed theorem,
what remains unused and how to recover retired code. Archiving a roadmap
does not itself remove any Lean modules.

Run `python3 scripts/plan-status.py --check` to check the active proof summary;
`--list` lists its theorem milestones. Detail files under `plan/archive/`
are excluded from regeneration and the active milestone list.
