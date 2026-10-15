# Plan and progress

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

## Next direction: sharper exponent bounds

The next research goal is to reproduce the stronger bounds developed in
[CrocSwap/integer-mult-bounds](https://github.com/CrocSwap/integer-mult-bounds)
using the completed Mathlib machine proof as the foundation. These are new
milestones, not prerequisites for the result above.

| Milestone | Status | Completion criterion |
| --- | --- | --- |
| Pin the external construction and its obligations | Next | Record an exact upstream revision, selected certificate, target saving and every inherited assumption. |
| Connect the finite construction to the existing library | Planned | Prove the selected circuit, frame, restoration and rank/cost contracts, identifying reusable local lemmas. |
| Realize and price the construction on the Mathlib machine | Planned | Prove the required uniform execution, routing, precision and recovery contracts with bounds on actual steps. |
| Close the sharper end-to-end bound | Planned | Instantiate the recurrence and total-cost analysis and prove an unconditional multiplication theorem with the new explicit saving. |

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
