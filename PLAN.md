# Plan and progress

✅ Complete · 🟡 In progress / partially complete · ⬜ Not started.

**Bound improvement progress:** M1 ✅ · M2 ✅ · M3 🟡 · M4 ⬜ · M5 ⬜ · M6 🟡 · M7 🟡 · M8 ⬜.
The completed compact multiplier proves saving `88279/2^46 ≈ 2^-29.5702`, up from the previous `25222/2^46 ≈ 2^-31.3776` (and `14229/2^46 ≈ 2^-32.2035`, `3213/2^44 ≈ 2^-32.3512` and `36261/2^48 ≈ 2^-32.8539` before that); further structural improvements remain in progress.

## Bound scoreboard

We measure progress by the **proved exponent saving `kappa`** in worst-case
time `O(n (log n)^(1-kappa))`. Larger saving means a smaller time exponent.

| Bound | Exponent saving `kappa` | Status |
| --- | --- | --- |
| **Current unconditional result** | **`88279/2^46 ≈ 2^-29.5702`** | ✅ T16 node with seven-eighths-power chunks `K = ⌊d^(7/8)⌋` (`c = 7/8`, from PR 4). The binding layout margin `epsilon c (1-tau)` grows by `7/2`; `lambda = 1-28/10^10`, `lambda' = 1-23/2^33` keep the layer margin `epsilon (1-lambda')` above it. The saving is the layout margin rounded down to `2^-46`. |
| **PR 4 mixer result** | `651/2^39 ≈ 2^-29.6534` | Proved on the `further-improvements` branch only; not adopted. Size-25 mixer supplier (`sigma = 1-25/10^10`) with `c = 7/8`, binding layer margin `epsilon (1-lambda')` at `lambda' = 1-21/2^33`. T16 replaces the mixer in the complex-supplier slot. |
| **Previous T16 result** | `25222/2^46 ≈ 2^-31.3776` | ✅ Superseded; T16 layer node: 73 slots, 14336 data roles and 8 private centres, 1,041,408 children (`log_73 (F/NW) < 999/1000`), lowered to factors, half-integral gates, translations, slot XORs and slot phases on the layer machine. With `lambda = 1-2/10^9`, `lambda' = 1-2^-30` the layer margin `epsilon (1-lambda')` no longer binds; the saving is the layout margin `epsilon c (1-tau)` rounded down. |
| **Previous T25 result** | `14229/2^46 ≈ 2^-32.2035` | ✅ Superseded; retune to `epsilon=31/64`, `delta=2^-7`, `lambda'=1-459/2^40`: the Schönhage–Strassen allowance is `M(p) = p^{1+2^-7}`, the resampling envelope uses the logarithmic band width `α ≤ 4 b^{ε/2^33}`, and every size relation (moduli room, `d ≤ 2^(ℓ-1)`, `d+1 ≤ ℓ`, `16 d α² ≤ b`) is re-proved from `d^64 ≤ b^31` with `d ≥ 2^192`. All-input correctness and cost bound on one fixed finite Mathlib machine. |
| **Previous T25 dimension result** | `3213/2^44 ≈ 2^-32.3512` | ✅ Superseded; `epsilon=7/16`, `delta=2^-5`. |
| **Previous dyadic-dimension result** | `36261/2^48 ≈ 2^-32.8539` | ✅ Superseded; `epsilon=79/256`, capped by the coarse `α ≤ 2√d` resampling bound. |
| **Previous rounded result** | `2^-33.0000` | ✅ Rounded synthetic layers and transforms at `epsilon=9/32`. |
| **Previous dyadic result** | `2^-34` | ✅ Superseded by rounded synthetic layers, which allow the `9/32` dimension. |
| **Previous eighth-root result** | `2^-35` | ✅ Superseded by the audited dyadic dimension retune and fourth-root chunks. |
| **Previous dimension result** | `2^-36` | ✅ Superseded by the audited eighth-root retune and sharper logarithmic cost estimates. |
| **Previous compact result** | `2^-37` | ✅ Superseded by the checked sixteenth-root dimension retune. |
| **Historical M2 result** | `2^-66` | ✅ Superseded; the current theorem improves the public saving by more than `2^36`, not a measured runtime speedup. |
| **Pre-M1 unconditional result** | `296 / (10^11 * 2^131)` (between `2^-160` and `2^-159`) | Superseded by M1; the existential theorem remains compatible. |
| **Historical M1 result** | `2^-93` | M2 improves the public exponent saving by `2^27`; this is not a timing speedup. |
| **Goal: match the selected community construction** | **`836330098538459 / 500000000000000000 = 0.001672660197076918`** | ⬜ Not yet proved here. Upstream construction is conditional; our goal is an unconditional machine theorem at this exact saving. |

The goal corresponds to a log exponent of `0.998327339802923082`.
These are asymptotic exponent bounds, not measured execution speedups.
Update the current-result row only after the stronger machine theorem passes
the guarded checks and axiom audit; parameter arithmetic or a finite
certificate alone does not improve the proved multiplication bound.

**Integer multiplication below `n log n` is proved.**
`IntegerMultBounds.MathlibTM2.statement` constructs a fixed finite Mathlib
machine that multiplies every input pair correctly in worst-case time
`O(n (log n)^(1-kappa))`, with positive saving
`kappa = 88279/2^46`. No algorithmic or runtime assumption remains.

## Completed proof

| Part of the proof | Source | Mathematics | Tape | Files |
| --- | --- | --- | --- | --- |
| [Proved Mathlib end-to-end multiplier](plan/C-mathlib-end-to-end.md) | — | ✅ 1/1 | ✅ 1/1 | 636 |

The [proof details](plan/C-mathlib-end-to-end.md) cover the numerical
algorithm, recursive layers, transforms, resampling, CRT routing, exact
recovery, fixed-machine assembly and actual step bound. All are complete.
The machine model is Mathlib's `Turing.FinTM2`, with standard binary encodings.
The Files column counts the components listed in that detail file; the full
transitive proof dependency set is larger, as recorded by the
[retention audit](docs/proof-retention.md).

The complete compact theorem and its import-closure axiom audit passed at saving `2^-34`. The audit covers 125034 declarations; the focused compact audit covers 572 contracts. The
earlier library-wide build and audit passed after native-wrapper retirement.
`CompletedProofCheck.lean` independently audits
the completed theorem's import closure; the library and focused checks allow
only `propext`, `Classical.choice` and `Quot.sound`.

## Bottlenecks by original manuscript section

The [section-by-section implementation plan](plan/D-sharper-bound.md) is based
on the original OpenAI manuscript and the pinned selected community
construction. **Today's binding margin is the compact layout: `epsilon c (1-tau) ≈ 2^-29.5702` at `c = 7/8`, rounded down to the public saving `88279/2^46`.** The T16 node moved the §5 layer margin `epsilon (1-lambda')` off the critical path: `1-lambda'` is now capped only by `lambda' > lambda > tau`, i.e. by the basis-change exponent `tau = 1-296/10^11`. Both remaining margins scale with `1-tau` and with `epsilon` (`epsilon < 1/2` from the resampling margin and the moduli construction), and `c < 1`, so beyond about `2^-29.4` the route needs a smaller `tau` (sharper slot-XOR interchanges) or `epsilon > 1/2`.

**The `epsilon < 1/2` barrier.** `2^-32` needs `epsilon > 0.557` with the existing supplier. Beyond `1/2` the `d` pairwise coprime moduli must sit in windows `[(1-2η)t, (1-η)t]` of relative width `η = 1/(4d)`, with `d ≫ log t`. Every elementary construction (`oddProd`, `1 + iM`, primorial shifts) needs `d² log d ≲ b`; the selected construction instead cites Baker–Harman–Pintz primes in short intervals. Mathlib has only Chebyshev bounds and Bertrand. So the next dyadic step needs **both** a short-interval prime supply (at least PNT with a `(log x)^-A` error term, `A > 2`) **and** a faster forward Gaussian map. The forward map is the selected chirped correlation (`notes/fast-gaussian-resampling.tex`), `O(M(p))` per element. The existing banded `B̃₀` with a larger `α² ≈ p^r`, `r < 1-ε`, suffices for the inverse up to `epsilon < 2/3`, so the phase-cell inverse is not on the critical path for `2^-32`.
The actual compact runtime removes the old full-slot control restriction. A
checked route certificate (`CompactGaussianRoute`) shows that with the **existing** supplier the selected Gaussian margin
lets every stage margin cover `2^-32` at `epsilon=5/8`, while no Gaussian
improvement alone reaches `2^-31`; M6 is needed beyond `2^-32`. Stopped recursion and precision/workspace accounting in M3–M5 continue.

Section numbers below are the manuscript's **printed numbers**, verified
against its PDF contents. §7 is polynomial products, §8 is resampling,
§9 is multiplication, and grouped packed additions are Appendix A. Earlier
archived plans used inconsistent source-filename numbering.

The progress column tracks the stronger-bound work in each section, using the
same ✅ / 🟡 / ⬜ markers as the milestone tables. §7 is complete for the
current widths; any future width change requires revalidation. Yellow rows
include checked improvements with further work remaining; they are not gaps
in the completed multiplier.

| Manuscript section | Progress | What limits our bound | Improvement needed |
| --- | --- | --- | --- |
| §2 Machine model and streams | 🟡 | Every new algorithm needs actual finite-machine costs and clean returned state. | Reuse Mathlib FinTM2 and existing host primitives; price new schedules. |
| §3 Finite networks | 🟡 | Current bit/complex primitive savings are `2.96e-9` and, with the T16 node on the layer machine, `10^-3` (`log_73 (F/NW) < 999/1000`). | Selected PR589 bit supplier and T16 complex supplier, with checked words, restoration, owner schedules and variable-rank moments. |
| §4 Address interchange | 🟡 | All field moves inherit the bit exponent; the running CRT now uses linear direct routing. | Prove selected arbitrary-source routing contracts. |
| §5 Butterfly layers; Appendix A | 🟡 | **The T16 node takes the layer margin `epsilon (1-lambda')` off the critical path; the layout margin `epsilon c (1-tau)` binds.** Complete compact runtime is proved. | Tighten recursive layer costs using stopped recursion, precision and proved recursive stock. |
| **§6 Synthetic transforms/layout** | 🟡 | **Layout saving `epsilon c (1-tau)` exceeds the public saving by a factor of about `1.77` but remains a nearby restriction.** | M2 retuned epsilon/c; next replace this charge by selected coordinate routing and a balanced prefix. |
| §7 Exact polynomial products | ✅ | Packing widths and extra logarithms must remain within budget. | Reuse the proved fast subroutine and exact algebra; revalidate under new widths. Not currently binding. |
| §8 Resampling | 🟡 | Current Gaussian exponent is `1/2 + 2^-7 + epsilon(1+2^-33)` (band width `α` logarithmic); margin `2^-7 - 31/2^39` at `epsilon=31/64`. | Chirped-correlation forward map (`O(M(p))` per element) and a wider banded inverse for `epsilon > 1/2`. |
| §9 Exact multiplication/cost | 🟡 | Direct CRT charge is `d(1+ell^tau)`; the final bound is the smallest stage margin. | Seven-stage bootstrap, all 47 linked target inequalities and unchanged exact output semantics. |
| §§10–11 Arithmetic/transposition corollaries | ⬜ | Downstream consequences, not multiplication bottlenecks. | Defer until the multiplication bound advances. |

## Ordered implementation milestones

Use ✅ only when the entire deliverable is checked, 🟡 when some work is checked
but integration or proof obligations remain, and ⬜ before implementation starts.

All rows below concern **improvements to an already completed theorem**.
Detailed source references, code integration points, contracts and acceptance
criteria are in the [implementation plan](plan/D-sharper-bound.md).

| ID | Progress | Original sections | Concrete deliverable | Bound effect / remaining work |
| --- | --- | --- | --- | --- |
| **M1** | ✅ | **§§5, 6, 9** | **Set `epsilon=2^-30`, `c=2^-34`; reprove dependent sizing, executable parameter generation, cost and machine lemmas.** | **Complete, historical.** Public saving `kappa=2^-93`; exact internal margin `296/(10^11 * 2^64)` lies between `2^-93` and `2^-92`. Internal margin improved by `2^67`; public saving improves the former exact bound by more than `2^66`. |
| M2 | ✅ | §§4.3, 8.2, 9.3 | Replace adjacent CRT walks by direct nonadjacent swaps; preserve exact semantics and price setup, controls, movement and cleanup. | **Complete.** The running multiplier uses linear CRT routing and sharp linear resampling costs. Final parameters `epsilon=2^-5`, `c=2^-32`, `lambda'=1-1/10^11` give exact margin `296/(10^11 * 2^37)` and public saving `2^-66`; theorem and focused audit pass. |
| M3 | 🟡 | §5.2–5.3, Appendix A | Compact dirty controls, actual caller integration, stopped recursion and local repair costs. | **Compact integration complete:** actual fourth-root transforms, main input/distribution, full arithmetic chain, output, cleanup and finite-machine dispatch prove public saving `2^-33`, with rounded synthetic layers (one scale per level, truncation errors absorbed by the rounds) at `epsilon=9/32`. **Remaining:** stopped top/layer integration and cost absorption; actual global cutoff, reservation/root construction and configured precision are checked. |
| M4 | ⬜ | §5.4, §9.7 | Linear completed-child precision bound and explicit recursive workspace/stock contracts. | Planned. Remove conservative guard-growth restrictions and prove the reserve coefficients required at selected cutoffs. |
| M5 | ⬜ | §6.2, §4 | Balanced prefix and arbitrary-source coordinate routing in both transform directions. | Planned. Replace layout saving `epsilon c a_b` by direct movement saving `a_b`; restore spectators and frequency order. |
| M6 | 🟡 | §3.1–3.6, §§4–5 interfaces | Prove both selected finite suppliers, their variable-rank moments and the 144-call owner schedule. | The complete selected PR589 scalar word and finite-register dirty endpoint are checked, including source/helper restoration. Exact PR589 frame-state/compiler boundaries, concrete rational frame/COPY interpretation and all636 label dimensions, plus T16 charge profile, owner-row bounds, label traces, finite geometry and source-faithful binary tableau ranks for every native event with all1004 literal extension matrices are checked. Exact selected moment bills (T16 at `7/4178` tied to the checked schedule; PR589 at `10/5769`, occurrence link open) and the layer moment interface are checked. The T16 node is lowered to the layer machine and runs in the completed proof; the PR589 bit supplier and a variable-child layer recurrence remain. Target primitive endpoints about `0.00173343` (bit) and `0.00167546` (complex); component bounds alone do not update the final bound. |
| M7 | 🟡 | §8.1–8.3, §9.2/9.7 | Prove faster rounded Gaussian inverse and bulk core/halo tape execution, including prime supply and exact recovery interfaces. | Actual executable coefficients, square-root band, periodic operator error≤`2^(-45p)` and small-gap exact/rounded inverse bounds `4p`/`8p` are checked and audited, including all aliases. Also checked: the actual rational periodic matrix with elimination margin `1/(8p)`; exact, `8p`-conditioned boundary solves with band-or-same-cell sparsity and block-Schur identification; Gohberg–Semencul inverses of actual interior Toeplitz blocks with rounded scaled block-solve errors; and the exact four-step interior/boundary solve with rounded-error composition. Rounded boundary factorization, boundary ordering, tape costs and bulk execution remain; these must remove the Gaussian restriction and support near-one dimensions. |
| M8 | ⬜ | §9.1–9.8 | Prove bootstrap base/stages, link all 47 inequalities to actual stages and close the audited fixed-machine theorem. | Planned. Goal: exact unconditional saving `0.001672660197076918`. |

### M3 integration progress

| Deliverable | Progress | Remaining gate |
| --- | --- | --- |
| Compact slot, basis, factor and recursive layer execution | ✅ | Checked actual programs and local costs. |
| Full runtime top transform and original size/precision bridges | ✅ | No per-piece readiness or execution premise remains. |
| Persistent original guard/dimension, per-round refresh and cleanup | ✅ | Checked from explicit original parameter sources. |
| Individual round stages and expanded main-host placement | ✅ | Checked staging/frame contracts and register embeddings. |
| Complete compact chunk round | ✅ | Checked actual preparation, top execution, restoration and cleanup from original round state. |
| Original-input bootstrap and transform-boundary cleanup | ✅ | Checked the dimension-minus-one correction, parameter precision source, retained globals and charged exit. |
| Counter-driven compact/direct dispatch | ✅ | Checked both actual branches, original butterfly semantics and full main-register frame. |
| Forward/opposite rounds and complete scans | ✅ | Checked original transform stream semantics and full-register restoration except I/O. |
| Bootstrap-to-transform frame | ✅ | Derives setup from real sources, establishes readiness and restores the original file except output after charged exit. |
| Complete forward/opposite transform specifications | ✅ | Existing layouts, actual distributed parameters and charged setup/exit; no layout, execution or readiness oracle remains. |
| Expanded main/source-stage entry and execution | ✅ | Original main invariant supplies entry; concrete source forward/opposite stages run with exact costs. |
| Expanded fifteen-stage arithmetic chain | ✅ | Actual retuned source stages and original primitive stages compose with exact twelve-step normalization overhead; outer input/distribution/output and full cleanup are also integrated. |
| Concrete round and setup cost accounting | ✅ | Checked actual records, setup, recursive calls, controls and cleanup; scalar-budget obligations remain explicit. |
| Uniform caller budgets and round overhead | ✅ | Combined scalar/divisor budgets, actual record validity and full overhead are derived for the old and larger chunks. |
| Larger-chunk recursive readiness and top execution | ✅ | Uniform shape, selected rows, descendant packing and actual parked top execution; full retuned chunk/transform composition remains. |
| Compact layer guard growth | ✅ | Actual original-precision guard fits any positive dimension power with dyadic constants; closed recurrence guard factor fits the proposed layer exponent. |
| Executable fourth-root parameters and distribution | ✅ | Charged table-slot overwrite and distribution wrapper preserve other fields; derived synthetic/layout fields consistently use the new chunk. |
| Complete fourth-root transforms | ✅ | Actual forward/opposite specifications use the new initial wires and existing executable layouts, with no execution/layout/readiness oracles. |
| Retuned reservation and complete top-cost exponent | ✅ | All reserved axes and the actual recursive top program, kernels and controls fit the proposed layer exponent with dyadic coefficients. |
| Retuned distribution-to-transform entry | ✅ | Actual charged distribution preserves the main invariant and supplies the new transform entry state. |
| Retuned aggregate analytic bound | ✅ | Stage envelope and actual machine costs are matched at saving `2^-34`. |
| Replaceable main procedure entry | ✅ | Checked restricted-call transport preserves layer execution when installing the expanded main body. |
| Actual retuned layer costs | ✅ | Complete chunk layer and direct branch costs match the retuned envelope; loop summation remains. |
| Retuned source transforms under replaceable main entry | ✅ | Full source stages execute with exact costs under the expanded recursive procedure table. |
| Main overhead, normalization and cleanup cost bridge | ✅ | Original primitive costs, fixed wrapper steps and expanded-host cleanup fit the sharper bound given the actual source-run match. |
| Actual compact round and loop cost sums | ✅ | Both loop directions fit the retuned convolution envelope given the explicit stash budget. |
| Expanded source and total-time aggregation | ✅ | All three actual source-run costs plus main overhead fit the stronger asymptotic bound, conditional on the two complete transform costs. |
| Complete transform and concrete main-time estimate | ✅ | Actual stash, layout, bootstrap, loops, source runs and main overhead satisfy the `2^-34` envelope with no remaining stage-cost hypotheses. |
| Stronger fixed-machine theorem | ✅ | Public `MathlibTM2.mulInTime` proves `2^-34` for every input pair; complete actual execution and cost hypotheses are discharged. |
| Stopped recursion | 🟡 | The full stopped digit scanner, semantic rebased records and cutoff from a supplied threshold are checked; global threshold generation, caller/precision integration and final layer-cost matching remain. |

**Execution order:** M1–M2 complete → M3–M5 → M6/M7 → M8. Use current
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
