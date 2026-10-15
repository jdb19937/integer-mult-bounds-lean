# Plan and progress

## Bound scoreboard

We measure progress by the **proved exponent saving `kappa`** in worst-case
time `O(n (log n)^(1-kappa))`. Larger saving means a smaller time exponent.

| Bound | Exponent saving `kappa` | Status |
| --- | --- | --- |
| **Current unconditional result** | **`2^-93`** | Proved on one fixed finite Mathlib machine, for all input pairs. |
| **Previous unconditional result** | `296 / (10^11 * 2^131)` (between `2^-160` and `2^-159`) | Superseded by M1; the existential theorem remains compatible. |
| **Next improvement: direct CRT routing** | To be proved after retuning | M2 removes the quadratic routing restriction; §6 remains the active bottleneck. |
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
`kappa = 2^-93`. No algorithmic or runtime assumption remains.

## Completed proof

| Part of the proof | Source | Mathematics | Tape | Files |
| --- | --- | --- | --- | --- |
| [Proved Mathlib end-to-end multiplier](plan/C-mathlib-end-to-end.md) | — | ✅ 1/1 | ✅ 1/1 | 230 |

The [proof details](plan/C-mathlib-end-to-end.md) cover the numerical
algorithm, recursive layers, transforms, resampling, CRT routing, exact
recovery, fixed-machine assembly and actual step bound. All are complete.
The machine model is Mathlib's `Turing.FinTM2`, with standard binary encodings.
The Files column counts the components listed in that detail file; the full
transitive proof dependency set is larger, as recorded by the
[retention audit](docs/proof-retention.md).

The guarded theorem-only build and focused axiom audit passed for M1. The
earlier library-wide build and audit passed after native-wrapper retirement.
`CompletedProofCheck.lean` independently audits
the completed theorem's import closure; the library and focused checks allow
only `propext`, `Classical.choice` and `Quot.sound`.

## Bottlenecks by original manuscript section

The [section-by-section implementation plan](plan/D-sharper-bound.md) is based
on the original OpenAI manuscript and the pinned selected community
construction. **Today's binding cost is §6 transform-layout movement.**
Increasing its parameters then runs into §9's quadratic CRT schedule and §5's
full-slot control costs; reaching the selected target also requires §8's new
Gaussian/bulk analysis and §3's stronger suppliers.

Section numbers below are the manuscript's **printed numbers**, verified
against its PDF contents. §7 is polynomial products, §8 is resampling,
§9 is multiplication, and grouped packed additions are Appendix A. Earlier
archived plans used inconsistent source-filename numbering.

| Manuscript section | What limits our bound | Improvement needed |
| --- | --- | --- |
| §2 Machine model and streams | Every new algorithm needs actual finite-machine costs and clean returned state. | Reuse Mathlib FinTM2 and existing host primitives; price new schedules. |
| §3 Finite networks | Current bit/complex primitive savings are `2.96e-9` and `4.18e-10`. | Selected PR589 bit supplier and T16 complex supplier, with checked words, restoration, owner schedules and variable-rank moments. |
| §4 Address interchange | All field moves inherit the bit exponent; current CRT routing uses quadratic adjacent swaps. | Direct distant-field routing first, then selected arbitrary-source routing contracts. |
| §5 Butterfly layers; Appendix A | Full-slot overhead pays `K^tau`; actual piece matching requires `c < lambda'-lambda`. | Compact dirty controls, stopped recursion, linear semantic precision and proved recursive stock. |
| **§6 Synthetic transforms/layout** | **`p K^(tau-1)` gives saving `epsilon c (1-tau) > 2^-93`.** | M1 retuned epsilon/c; next replace this charge by selected coordinate routing and a balanced prefix. |
| §7 Exact polynomial products | Packing widths and extra logarithms must remain within budget. | Reuse the proved fast subroutine and exact algebra; revalidate under new widths. Not currently binding. |
| §8 Resampling | Current Gaussian exponent is `7/8 + 3 epsilon/2`, preventing epsilon near one. | Faster rounded inverse, bulk core/halo execution and proved error/normalization bounds. |
| §9 Exact multiplication/cost | CRT charge `d^2 ell^tau` forces epsilon below about `3e-9`; final bound is the smallest stage margin. | Linear CRT routing, seven-stage bootstrap, all 47 linked target inequalities and unchanged exact output semantics. |
| §§10–11 Arithmetic/transposition corollaries | Downstream consequences, not multiplication bottlenecks. | Defer until the multiplication bound advances. |

## Ordered implementation milestones

All rows below concern **improvements to an already completed theorem**.
Detailed source references, code integration points, contracts and acceptance
criteria are in the [implementation plan](plan/D-sharper-bound.md).

| ID | Original sections | Concrete deliverable | Status / bound effect |
| --- | --- | --- | --- |
| **M1** | **§§5, 6, 9** | **Set `epsilon=2^-30`, `c=2^-34`; reprove dependent sizing, executable parameter generation, cost and machine lemmas.** | **Complete.** Public saving `kappa=2^-93`; exact internal margin `296/(10^11 * 2^64)` lies between `2^-93` and `2^-92`. Internal margin improved by `2^67`; public saving improves the former exact bound by more than `2^66`. |
| M2 | §§4.3, 8.2, 9.3 | Replace adjacent CRT walks by direct nonadjacent swaps; reuse already linear resampling exposure and price residual CRT arithmetic separately. | **In progress.** Distant-swap bridge, order-independent rotation semantics and executable descriptor/offset kernels proved. Next: assemble the descriptor-tape/fiber loop and linear driver, then match costs and retune. Current saving remains `2^-93`. |
| M3 | §5.2–5.3, Appendix A | Compact dirty-control host adapter, stopped recursion and locally charged exceptional repair. | Planned. Remove `K^tau` from node overhead, with complete temporary-field restoration. |
| M4 | §5.4, §9.7 | Linear completed-child precision bound and explicit recursive workspace/stock contracts. | Planned. Remove conservative guard-growth restrictions and prove the reserve coefficients required at selected cutoffs. |
| M5 | §6.2, §4 | Balanced prefix and arbitrary-source coordinate routing in both transform directions. | Planned. Replace layout saving `epsilon c a_b` by direct movement saving `a_b`; restore spectators and frequency order. |
| M6 | §3.1–3.6, §§4–5 interfaces | Prove both selected finite suppliers, their variable-rank moments and the 144-call owner schedule. | Planned. Target primitive endpoints about `0.00173343` (bit) and `0.00167546` (complex); component bounds alone do not update the final bound. |
| M7 | §8.1–8.3, §9.2/9.7 | Prove faster rounded Gaussian inverse and bulk core/halo tape execution, including prime supply and exact recovery interfaces. | Planned. Remove the current Gaussian restriction on epsilon; establish the selected near-one-dimension parameter regime. |
| M8 | §9.1–9.8 | Prove bootstrap base/stages, link all 47 inequalities to actual stages and close the audited fixed-machine theorem. | Planned. Goal: exact unconditional saving `0.001672660197076918`. |

**Execution order:** M1 complete → M2 → M3–M5 → M6/M7 → M8. Use current
smaller networks while establishing the structural interfaces; then plug in
the selected suppliers. M6 and M7 are separate major requirements, both needed
for M8. The bootstrap base saving `0.0000384599` must itself be proved or
replaced by a sufficiently strong proved base; our current theorem does not
supply it.

After each integration, record the **achieved saving**, the **smallest remaining
cost margin**, and its **manuscript section**. Commit and push each checked
logical section. Source records are pinned, but full supplier replay and
inherited machine/analytic obligations remain unfinished. Planning statuses
are maintained explicitly; the completed-proof summary above is generated.

The external selected result remains conditional. Its
[selected record](https://github.com/CrocSwap/integer-mult-bounds/blob/0fdd7d82de03e43c9e5a1000dfbcd380d1b687d2/certificates/selected-result.json)
and [pinned source evidence](docs/sharper-bound-source.json) distinguish it
from our unconditional result and from older intermediate research witnesses.

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
