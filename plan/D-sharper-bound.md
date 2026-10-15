# D. Reproduce the selected community exponent

Part of the [plan](../PLAN.md). This is a new research programme on top of the
[completed Mathlib proof](C-mathlib-end-to-end.md).

## Target and frozen evidence

As checked on 2026-10-15, the selected upstream result is still PR #1094's
rare-pattern T16 owner-exchange construction, with saving
`836330098538459 / 500000000000000000 = 0.001672660197076918`.
The [source record](../docs/sharper-bound-source.json) pins upstream revision
`0fdd7d82de03e43c9e5a1000dfbcd380d1b687d2` and SHA-256 digests of the selected
record, assembly, source manifest, review and two obligation summaries.
The assembly digest matches the selected record. This establishes source
identity; the full supplier replay and Lean verification remain to be done.

References at that revision:

- [Selected result](https://github.com/CrocSwap/integer-mult-bounds/blob/0fdd7d82de03e43c9e5a1000dfbcd380d1b687d2/certificates/selected-result.json).
- [Construction review](https://github.com/CrocSwap/integer-mult-bounds/blob/0fdd7d82de03e43c9e5a1000dfbcd380d1b687d2/docs/research/community-batch1099-review.md).
- [Current bottleneck brief](https://github.com/CrocSwap/integer-mult-bounds/blob/0fdd7d82de03e43c9e5a1000dfbcd380d1b687d2/docs/research/bottleneck-brief.md).
- [Selected stock audit](https://github.com/CrocSwap/integer-mult-bounds/blob/0fdd7d82de03e43c9e5a1000dfbcd380d1b687d2/research/selected-bootstrap-stock-audit/README.md).

The complex primitive is binding: its certified endpoint is approximately
`0.0016754626768081035`, versus `0.0017334270395898442` on the bit side.
Both suppliers are needed. The assembly includes seven bootstrap stages and
47 outer inequalities. Its conservative complex pricing gives the slightly
smaller final saving `0.001672660194225008`. Matching that conservative result
would be progress, but would not reproduce the exact selected target.

## First milestone: prove that the gain can survive the host

Before porting the large finite construction, make the exponent transfer
explicit. The existing `MathlibTM2/Cost/Total.lean` proves
`totKappa = epsilon * cParam * (1 - Parameters.tau)`, with
`epsilon = 2^-75` and `cParam = 2^-56` in `Mult/Sizes.lean`.
Changing the primitive exponent alone retains this enormous loss.

Produce a parameterized statement of the total-cost exponent inequalities,
and recover the current theorem as its first instance. Compare every term
with the upstream assembly's 47 inequalities, particularly CRT movement,
resampling, packed products, phase changes, layer recursion and recovery.
Identify which estimates need sharpening, which parameter choices can be
relaxed, and whether any execution stage must change. Do not assume the
upstream primitive endpoints can be substituted for our `tau` and `sigma`:
first prove the correspondence between their contracts and our costs.

**Acceptance:** a checked parameterized cost lemma instantiated by the current
proof, plus a source-bound comparison of every upstream outer charge with a
local stage. Each mismatch has a specific missing estimate or implementation
contract. Only then choose the final host architecture and porting order.
An infeasible parameter system is a useful finding, not a reason to weaken
the target silently.

## Ordered implementation milestones

| Order | Work | Acceptance |
| --- | --- | --- |
| 1 | Exponent transfer and host feasibility, as above | Current parameters recover the existing result; all target cost terms and required changes are identified. |
| 2 | Selected supplier contracts and finite evidence | Reproduce pinned upstream replay; formalize both suppliers' exact words, arbitrary dirty inputs, outputs, restoration, frames, rank histograms and complete charges. Prove strict endpoint moment inequalities in Lean. |
| 3 | Uniform recursive construction and stock | Compile the finite contracts at every required size; prove the seven bootstrap stages, reserve envelopes and cutoff obligations with explicit source bindings. |
| 4 | Mathlib realization and sharp accounting | Implement the selected construction on one fixed finite machine; prove label compatibility, mutable-source behavior, routing, restoration, precision and exact recovery, with actual-step costs matching the analytic contracts. |
| 5 | Exact target theorem | Close the outer inequalities and prove `MathlibTM2.MulInTime (836330098538459 / 500000000000000000)` unconditionally; retain the existing theorem and audit the new theorem's import closure. |

Milestone 2 should start with one small complete selected operation, including
its dirty restoration and physical charges, before importing large generated
inventories. Its arithmetic certificate alone is not the supplier theorem.
After milestone 1 fixes the interfaces, finite algebra and host work can be
separated without guessing incompatible contracts.

## Reuse map and obligations

These are reuse candidates identified from their existing statements, not
proved adapters for the new suppliers.

| Obligation | Existing foundation | New work that must be checked |
| --- | --- | --- |
| Finite word and frame semantics | `Networks/FramedCircuit.lean`, `BoundedFramedCircuit.lean` | Bind the selected complex and bit words; prove all dirty inputs, source mutations, final restoration and finite register bounds. |
| Projector ranks and recursive calls | `Networks/Shared50GlobalProjectionRank.lean`, generic circuit/frame algebra | Replace construction-specific Shared50 budgets with selected rank histograms and fully priced endpoint contracts. |
| All-size compiler, labels and borrowing | `MathlibTM2/Node/TopProc.lean`, `Node/LayerProc.lean` | Selected all-size uniformity and common labels; verify changed rank/shape assumptions and ordinary-leaf interfaces. |
| Stock and bootstrap | `MathlibTM2/Layer/Recurrence.lean`, existing restoration proofs | Derive the selected stage reserve coefficients and valid cutoffs. Upstream's stock audit explicitly leaves these coefficients unknown; large headrooms do not prove fit. |
| Whole-call hosting and actual steps | `MathlibTM2/Fast/Final.lean`, `Cost/MatchSynLoop.lean` | Pay every source read, frame change, address operation, copy, cleanup and child call for the new program. |
| Precision, tape and exact recovery | `MathlibTM2/Mult/*`, `Fast/*`, `Host/*` | Re-establish intermediate magnitude/error bounds and word widths for changed operations before reusing CRT, resampling, rounding and carry proofs. |
| Analytic and bit H1–H5 interfaces | `MathlibTM2/Layer/Recurrence.lean`, `Cost/Total.lean` | State each inherited hypothesis from its pinned definition and prove a local implication; similarly named local results are insufficient. |

The pin records upstream's obligation categories. Exhaustively tracing their
definitions and dependencies remains work in milestones 1–3. In particular,
the current completed theorem discharges these concerns for its own program;
it does not discharge them automatically for a new supplier.

## Validation and integration

Preserve the current unconditional theorem as a regression target throughout.
Keep generic mathematics separate from selected generated data and machine
implementation. Preserve upstream attribution and license notices when
importing source or certificates. Use exact arithmetic and checked Lean
proofs for certificate acceptance; Python replay is supporting evidence.

Use only the guarded Lean scripts and preserve proof limits. At each completed
logical section, run the relevant guarded checks, update this plan, commit and
push. Before declaring the exact target complete, run the guarded library
build, the full axiom audit and a focused audit for the new theorem, allowing
only the existing three standard axioms. Avoid further broad legacy deletions
until the supplier comparison establishes which reusable lemmas are needed.
