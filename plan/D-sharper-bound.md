# D. Sharper multiplication bound, by manuscript section

Part of the [bound scoreboard and work queue](../PLAN.md).

## Sources and section numbering

Section numbers below are **printed section numbers in the original OpenAI
manuscript**, pinned at `adc7f1241b42e322a6451854ab7e4b4c146bf78a`:
[PDF and source](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026).
The PDF contents and TeX include order were checked directly. In particular,
§7 is *Exact normalized polynomial products*, §8 is resampling, §9 is exact
integer multiplication, §11 is matrix transposition, and grouped rectangles
are Appendix A. Source filenames do not consistently equal section numbers:
`06-transforms.tex` contains both §§6 and 7. Earlier archived plan headings
used filenames as section numbers; do not propagate that mistake.

The sharper target is the **selected** community construction at revision
`0fdd7d82de03e43c9e5a1000dfbcd380d1b687d2`, not the older numerical witnesses
in individual notes. The [source pin](../docs/sharper-bound-source.json)
records the selected certificate, supporting sources and manuscript digests.
The original manuscript proves saving `2^-182`; our present Lean theorem proves
`2^-93` after M1. The exact internal margin is `296 / (10^11 * 2^64)`,
between `2^-93` and `2^-92`. The selected upstream
conditional saving is `0.001672660197076918`.

## Diagnosis: where our current bound is lost

Write `a_b = 1 - tau = 296/10^11`, `a_c = 1 - sigma = 418/10^12`,
`d ≍ p^epsilon`, `K ≍ d^c`, and `p ≍ log n`. Costs below are divided by
input-scale volume `Tp ≍ n`. A term of size `p^x` allows saving at most `1-x`.
These are the **current local** estimates in `MathlibTM2/Cost/Total.lean`,
not an assumption that every row already matches the sharper manuscript.

| Original section | Current normalized charge or restriction | Consequence for the saving | Concrete bottleneck |
| --- | --- | --- | --- |
| §3.6, finite-network exponents | `tau = 1 - 2.96e-9`, `sigma = 1 - 4.18e-10` | Both primitive savings are tiny. | Local fixed networks have not been replaced by the selected suppliers. |
| §4.2–4.3, address interchange | `O(u^tau)` per volume | Every routed field move inherits `tau`. | Arbitrary-gap correctness alone does not prove a cheaper whole schedule. |
| §5.2–5.3 and Appendix A, layer control | Node overhead includes `(K e)^tau`; actual piece estimate is `d^(lambda+c)` times logarithms | `c < lambda' - lambda = 2e-10` in `mrP_eps_pos`; also the generic stopped-layer condition involves `tau(1+c/beta)`. | Full slot width is paid during basis/control changes. The actual current host recurses to level zero; the generic stopped recurrence is not itself a stopped implementation. |
| §6.2, transform layout | `p K^(tau-1)` | **Current active bottleneck:** `epsilon c a_b`, exactly our proved `kappa`. | Moving many K-bit chunks multiplies the primitive saving by both small parameters. |
| §§8.2, 9.3, CRT and axis exposure | `d^2 (1 + ell^tau)` | Saving `a_b - epsilon(1+a_b)`; positivity forces `epsilon < a_b/(1+a_b)`. | Quadratic adjacent field routing prevents a large dimension exponent even after tuning. |
| §8.1–8.2, Gaussian arithmetic | Local bound has exponent `7/8 + 3 epsilon/2` | Saving `1/8 - 3 epsilon/2`; it would force `epsilon < 1/12`. | Present Gaussian width, inverse and line-by-line implementation cannot support the selected near-one dimension exponent. |
| §7, packed ring products | Local logarithmic product factor has exponent bounded by `1-epsilon+epsilon c` | Saving `epsilon(1-c)`. | Must preserve a fast conventional subroutine and account for its extra logarithms under new parameters. Not currently binding. |
| §9.7–9.8, precision and assembly | Maximum of all stage exponents, with exact recovery and fixed-machine assembly | The smallest surviving saving wins; isolated network improvement is insufficient. | Every changed stage must match actual costs and the exact recovery interface. |

The direct optimization has a ceiling: as long as the quadratic CRT charge
remains, `epsilon` must stay below about `3e-9`; as long as the current layer
piece estimate remains, `c` must stay below `2e-10` with the current lambdas.
Thus tuning alone cannot approach `0.00167`. It is an inexpensive first
improvement and a way to expose the constraints before changing algorithms.

## M1 completed: retune the existing construction

**M1 — §§5, 6, 9:** `epsilon = 2^-30` and `c = 2^-34`, keeping the existing
primitive exponents and layer exponents. The public theorem is now
`MathlibTM2.mulInTime : MulInTime (2 ^ 93 : ℝ)⁻¹`.

The exact internal saving, exposed separately by `mulInTime_exact`, is
`296 / (10^11 * 2^64)`, between `2^-93` and `2^-92`. It is `2^67` times the
previous internal saving; the rounded public saving improves the previous
exact bound by more than `2^66`. These are improvements in the asymptotic
exponent saving, not measured runtime speedups.

Implementation completed:

1. Changed the root indices and value lemmas in `Mult/Sizes.lean`, and the
   executable root programs, stage proofs and step counts in `Fast/ParamProg.lean`.
   The existing sizing, width, finite-cutoff and cost proofs check unchanged.
2. Updated `Cost/Total.tot_kappa_eq`; exposed `MainStatement.mulInTime_of_bundles`
   and the explicit theorem in `Theorem.lean`. `statement : Statement` remains
   available through the stronger bound. The power-of-two corollary follows
   from the existing monotonicity of the logarithmic time exponent.
3. Verified the theorem's dependencies with the guarded targeted build and
   its import closure with `CompletedProofCheck.lean`, which also checks the
   explicit public bound and allows only the three standard axioms. Use these
   focused checks for this change; a full-library rebuild is unnecessary.

**Remaining minimum margin:** §6's layout term still gives the exact internal
saving `epsilon c (1-tau)`. The next smallest current stage margin is the layer
term `epsilon (1-lambda')`; CRT routing is still the restriction on increasing
epsilon substantially. **Next task: M2**, direct CRT routing followed by retuning.

## Section-by-section implementation work

#### §2 — The machine model and elementary streams

Reuse Mathlib `FinTM2`, the existing finite host/compiler, encodings, scanning,
stack frames and guarded audits. No new machine model is required. New
schedules must use a fixed number of stacks and labels; growing network,
owner and address descriptions must be runtime data or a fixed finite program,
with generation and interpretation priced explicitly. Preserve arbitrary
spectators, workspace restoration and standard binary input/output.

**Deliverable:** extend existing host contracts for each new stage, with an
actual-step bound and clean returned state. This is a requirement of M2–M8,
not an independent attempt to improve the exponent.

#### §3 — Two finite networks with a rank saving

**M6a — replace the scalar/frame suppliers.** The current implementation uses
Shared50 bit machinery and the h=25 complex branching certificate
(`Cost/Branching.lean`). The target instead combines PR589's punctured R439
bit word with the selected T16 complex owner packing. Formalize both exact
words from pinned data, their complete dirty-input linear maps, source
mutations, restoration, entrance/exit frames and physical occurrence order.
Use `Networks/FramedCircuit.lean`, `BoundedFramedCircuit.lean`, existing
projection-rank and finite-field algebra as foundations, not as already proved
adapters for these words.

The selected complex rank histogram is
`{1:349604, 2:60192, 3:62585, 4:20448, 5:11808, 7:7, 8:1152, 48:4866}`.
The selected complex parent width is 73; the PR589 bit parent width is 64.
The primitive endpoint savings are approximately `0.0016754626768081035`
and `0.0017334270395898442`, respectively. Prove the exact moment inequalities
for the full histograms and all surcharges; a total-rank inequality alone
loses the benefit of variable-rank children.

**M6b — prove the physical owner schedule.** T16 changes 193 placements while
retaining the scalar word, role widths and source-event times. Prove the
144 complete-call ownership schedule, lifetime/capacity constraints, frame
availability and mutable-source behavior. Check the actual selected inventory;
older SW4/72-call proofs explain ancestry but do not prove the selected schedule.

**Done means:** both supplier semantics and fully charged profiles are checked
in Lean, including bit H1–H5 and the native-complex pricing justification.
The conservative complex surcharge gives final saving `0.001672660194225008`;
that is a distinct fallback waypoint, not the exact selected target.

#### §4 — Faster interchange of address chunks

**M2 — direct nonadjacent axis routing, also §§8.2 and 9.3.**
The sharper [nonadjacent-axis note](https://github.com/CrocSwap/integer-mult-bounds/blob/0fdd7d82de03e43c9e5a1000dfbcd380d1b687d2/notes/nonadjacent-axis-note.tex)
uses the existing arbitrary-gap primitive to reverse axes with paired distant
swaps and expose each resampling axis with one swap and its inverse. It replaces
`d^2(1+ell^tau)` by `d(1+ell^tau)`, changing the saving from
`a_b-epsilon(1+a_b)` to `a_b(1-epsilon)`.

The current resampling machines already use two distant-field swaps per
nonfinal axis (`Fast/ResampAAll.lean`, `Fast/ResampBAll.lean`), so retain those
implementations and expose their sharper charge separately from `totCRT`.
`Fast/ResampASwap.lean` supplies a reusable arbitrary-gap host adapter, including
axis widths differing by one. Adapt it for the CRT headers, then replace
the adjacent walks in `Fast/CRTSwap.lean` and `Fast/CRTDrive.lean`; update
`Cost/MatchCRT.lean` and both resampling matchers. Audit the existing residual
`O(d^2 Tp)` arithmetic separately: reducing swaps alone must not silently
delete that term. Retain its exponent `2 epsilon` or prove the stronger
controlled-rotation schedule needed by later near-one epsilon parameters. Keep the original axis arithmetic order so
rounding and numerical correctness proofs can be reused. Price descriptors,
cleanup and all intermediate data movement. Merely tightening `totCRT` would
be unsound: the current CRT machine actually performs the quadratic schedule.

**M2 implementation status:** the first bridge is proved in
`Fast/CRTGap.lean`. `crtSwapGapBox` and `crtSwapGapBoxBits` connect the
arbitrary-gap interchange to CRT record layouts; `crtGapHeaderP_runs`
constructs the middle-count header in `4g+8` host steps while restoring its
scratch register. `crtGapHdrBits_canonical` and `crtGapHdrBits_value` establish
the full header contract. `crtSwapGapPass_runs` proves the executable pass,
its volume/width cost, and restoration of all other registers. The pass assumes
prepared headers; it does not absorb their generation or cleanup for free.
The public fast-path aggregator imports this module, and `CRTGapCheck.lean`
audits the new contracts against the standard axiom set.

The driver is **not** a one-swap substitution. `crtFwdWalk_runs` moves
`i :: reverse(range i)` to `reverse(range i) ++ [i]`. For three axes,
`[2,1,0]` must become `[1,0,2]`; swapping the endpoints instead produces
`[0,1,2]`. More importantly, `crtRotP_runs` in `Fast/CRTRot.lean` expects
exactly `crtRevAx i` before the target: its address-validity count supplies
`crtKI`, the weighted mixed-radix control value. Arbitrarily reordering that
prefix changes the interpretation of the counter. The pure CRT content
lemmas in `CRTSpec.lean` remain reusable once that machine interface is proved.

**M2b progress:** `Fast/CRTControl.lean` now proves an alternative to the
order-dependent validity counter. Each physical field carries its place,
modulus bound, original mixed-radix weight and active-control flag. The
address evaluator recovers exactly `crtKI` and the original validity predicate,
even with higher spectator axes mixed into the prefix. `crtControlRotOut_top`
proves that all fibers together produce the same forward/inverse `crtRotC`,
including invalid controls and padded target slots. A direct multiplication
and remainder replaces iteration of `crtLo`; `crtControlShift_mod` proves the
same cyclic shift.

`Fast/CRTControlProg.lean` implements one descriptor in a fixed ten-variable
binary program: at most nine interpreter atoms, with scratch cleared and
spectators preserved. `crtControlStep_host` gives the actual host bound
`9 * tblC W w`; this is not nine Turing-machine steps. A separate three-atom
kernel computes the modular offset and complement. `CRTControlCheck.lean`
audits the semantic and executable contracts. No descriptor generation,
loading, fiber-loop or conversion cost has been silently included in these
kernel bounds. The subsequent loader/scanner and conversion contracts below
price these additional operations explicitly.

**Chosen driver design:** retain the fully reversed axis layout during the
triangular arithmetic passes. Expose each nonzero target by swapping it with
axis zero at the inner end, run the descriptor-controlled rotation, then swap
back. Finish the forward machine with paired distant swaps reversing the
whole axis list; perform that reversal first in the inverse machine. This
preserves the original target order and content maps while using at most
`2(d-1) + floor(d/2)` swaps in either direction. `Fast/CRTSchedule.lean` proves the exact forward/inverse route and count,
including exposure-prefix completeness and restoration. `Fast/CRTLinear.lean`
now implements each distant exposure and unexposure, including header
construction, upgrade and cleanup, with all scratch restored. Runtime unary
width generation and the complete driver remain to be assembled.

For each target, the new scan visits `2^(L-a_i)` fibers. There are at most `d`
descriptors per fiber, so the proved arithmetic kernel would contribute at
most `9 d 2^(L-a_i) tblC W w` before loading, offset conversion and loop costs.
`Fast/CRTControlBounds.lean` proves descriptor widths `L+1`, accumulated
values below `2^(2L)` even for invalid controls, and final products below
`2^(3L+1)`. Its budget invariant discharges intermediate overflow.
`Cost/CRTControl.lean` uses `mr_b_pow_le_r` to absorb any fixed polynomial
per-fiber budget over all axes into a constant times padded volume. The
actual scanner now supplies that budget through the contracts below.

`Fast/CRTControlTape.lean` proves the fixed four-word loader costs at most
`48 W + 56` host steps, with descriptor reversal saved for restoration.
The complete saved tape restores in `8 d W + 2` steps. A positive width
makes tape emptiness exactly descriptor-list emptiness; the arithmetic step
plus descriptor cleanup uses at most 13 interpreter atoms. These contracts
are included in the focused axiom audit.

`Fast/CRTControlBank.lean`, `CRTControlScan.lean` and `CRTControlScanner.lean`
now compose the loader with the interpreter and a fixed runtime `while` loop.
The concrete scanner has no assumed packet-execution premise: arithmetic
fit follows from the preserved budget, including invalid controls. Its output
is the exact control sum and sticky validity flag, with descriptor tape restored
and other registers preserved. The scan costs at most
`2^10 * d * (W+4)^2 + 4` actual host steps. `Cost/CRTControlScan.lean`
bounds the exact scan cost by `2^15*(L+1)^3` for `d≤L`, `W≤3L+1`, and
absorbs all fibers of all pipeline axes into `2^19*T` eventually.

`Fast/CRTControlOffset.lean` compiles the modular-offset kernel, converts
both directional lengths to unary, and clears those counters afterward.
Conversion costs `W*(4*S+22)+2*S+12`, separate from the three-atom
binary kernel and the `2*S+4` counter cleanup. This linear-in-modulus work
is **not** part of the polynomial descriptor-scan absorption. `Fast/CRTControlBridge.lean` now computes offsets directly in the scanner's
ten-variable bank, preserving its control sum and validity flag; the separate
five-variable interface is no longer required for this path.
`CRTControlConstants.lean` loads permanent target constants while preserving
sources. `CRTControlFiber.lean` selects rotation or copying from the binary
validity flag, and `CRTControlRotate.lean` composes offset computation,
materialization, physical movement and counter cleanup. `CRTControlPass.lean`
combines the actual scanner, constants load and rotation into one fiber with
no assumed execution contract. Descriptor tape and scratch return restored.

`Cost/CRTControlOffset.lean` separately bounds materialization plus cleanup
across all fibers by `2^7*d*T*p`, a linear number of full-volume record passes.
This does not include binary arithmetic or physical data movement; their
explicit bounds must be added when matching the complete pass.

`CRTControlReset.lean` loads the outer loop's binary address and establishes
the next fiber's canonical bank, costing `8W+8+10*tblC W w`.
`CRTControlLoop.lean` supplies a fixed indexed loop exposing that address to
each body, including initialization, runtime count construction and cleanup.
Its bound is `2^L*(bodyCost+4W+16)+6W+9L+17`. The body contract is discharged by `CRTControlAllFibers.lean`, including
output reversal and exact ordered execution of every fiber.
`CRTControlRotation.lean` specializes this execution to the original `crtRotC`
semantics with automatically proved arithmetic fits at width `3B+1`.
`CRTControlWorkspace.lean`, `CRTControlSetup.lean` and
`CRTControlAllWorkspace.lean` initialize and clear the bank and construct the
actual unary word width. The rotation wrapper changes only the data source
and restores every other register.
`Cost/CRTControlAllFibers.lean` bounds all passes, bank setup/cleanup and width
setup/cleanup by `2^21*(cw+1)*d*T*p` eventually, excluding descriptor generation.

`CRTControlGenerate.lean` provides actual packet emission, binary powers
without unary expansion, exposed-place/active-field arithmetic, and original
weight advancement. `CRTControlGenerateLayout.lean` proves that ascending
traversal with target omission and saved-zero insertion produces exactly the
required descriptors in physical exposed-axis order.
`CRTControlGenerateLoop.lean` now proves the concrete per-axis operation:
read both unary entries, construct the power directly in binary, emit/select
its packet, advance the original mixed-radix weight, and save the entries.
`CRTControlGenerateSetup.lean` provisions the bank and target constants from
unary inputs, preserving those sources. `Cost/CRTControlGenerate.lean` proves
that all target setup costs and all per-axis generation costs are each
absorbed by one padded volume eventually. Loop overhead and terminal stream
cleanup are included in the complete producer match below. `CRTControlGenerateTraversal.lean`
discharges the complete traversal's per-axis execution and derives all
arithmetic fits at width `3B+1`. `CRTControlGenerateTraversalLayout.lean`
proves its exact exposed descriptor tape, including parked-zero handling.
`CRTControlProducer.lean` now composes setup, immutable target-counter copy,
traversal and bank release into an exact descriptor producer. Only its tape
destination changes. `Cost/CRTControlProducer.lean` matches its actual budget,
including source restoration and descriptor disposal: all target producers
cost at most one padded volume eventually. The generator
kernels and one-fiber pass are audited; neither constitutes a new complete CRT
driver or a stronger public bound.

`CRTControlExposeRotation.lean` now composes the actual distant exposure,
workspace rotation and unexposure for a nonzero target, returning the fixed
reversed layout and restoring every register except the data source. Its
routing parameters and descriptor/constants tapes are still prepared inputs.
`CRTControlDriverSpec.lean` identifies descending and ascending target folds
with the existing `crtFwdC` and `crtInvC`, independently of physical layout;
target zero is an identity and can be omitted. `CRTReverse.lean` and
`CRTReverseFull.lean` execute the complete paired reversal, constructing the
opposite width stream and unary half-count at runtime and restoring every
register except data. `Cost/CRTReverse.lean` bounds the complete reversal by
a linear number of interchange budgets, including runtime setup and cleanup.
`CRTControlRouting.lean` ties the distant header widths
to the existing driver's upper/lower unary counters. `CRTControlStreams.lean`
constructs preserved ascending copies of the original descending entry streams.
The complete driver and its cost match are supplied by the direct-machine
modules below.

`CRTControlParameters.lean` now executes the complete conversion from unary
modulus, multiplier, axis width and total width into the two binary constants,
unary padding and fiber-address width. It preserves all inputs and returns
its arithmetic bank and temporary registers empty. Its checked disposal
returns the four outputs empty; preparation plus disposal over all targets
is absorbed by one padded volume in `Cost/CRTControlGenerate.lean`.

The existing resampling programs now have sharp matching theorems
`mt_rsa_stage_le_linear` and `mt_rsb_stage_le_linear`: their layout charge is
`totDirectCRT = T*p*d*(1+ell^tau)`, without the old extra factor of `d`.
`DirectGrowth.lean` proves the corresponding routing exponent margin
`(1-epsilon)*(1-tau)`. The old cost APIs remain compatibility wrappers;
the running main multiplier now uses direct routing and this aggregate scale.
Retuning is still required to publish a stronger saving.

`CRTControlTarget.lean` now composes unary parameter preparation, descriptor
production, routing-gap setup, distant exposure, rotation and full cleanup.
Only the data register changes. `Cost/CRTControlTarget.lean` bounds the sum of
actual nonzero target costs by a constant times `totDirectCRT` plus `T`.
`CRTDirectDrive.lean` implements both unary-stream traversal directions with
exact stream restoration and a sum of individual target costs, avoiding an
extra dimension factor. Its target-body contract is discharged by the concrete machine
instantiation below, including runtime setup and padding/reversal assembly. These contracts pass the focused standard-axiom audit.

`DirectTotal.lean` supplies the aggregate envelope with linear routing and
its logarithmic time-bound bridge, using the direct routing margin. It is
checked at the existing parameters. The actual executable pipeline is now
matched to this envelope; no stronger public saving is claimed before retuning.

`MainDirectCore.lean` connects both linear resampling bounds to the existing
source-transform core. `mn_core_le_linear` bounds its actual `srcCoreCost` by
the linear stage sum plus the explicit forward/inverse transform charges.
Those charges are discharged by the concrete direct-machine cost match.

`CRTDirectBacking.lean` embeds the 40 direct-driver registers and 25 arithmetic
bank registers into the expanded finite CRT register family. The seven
persistent input aliases are preserved; all 58 scratch slots belong to the
existing rest-empty contract. Focused checks of `CRTMachine`, `SrcStage`,
`MainRegs` and `DistSpec` confirm the old entry contracts supply that backing.

`CRTDirectSetup.lean` now constructs the ascending streams, cached axis-zero
width, dimension count, encoded record width and bank width directly from
legacy inputs. Its six-output frame and exact cleanup back to the original
register state are proved. `Cost/CRTDirectSetup.lean` bounds actual setup plus
all six-output cleanup by one padded volume eventually. The allocation
verification also refreshed all 19 affected dependency modules through
`MainRegs` and `DistSpec`, with no full build.

`CRTDirectMachine.lean` instantiates both weighted loops with the actual target
program, without an assumed target execution contract. `CRTDirectMachineCore`
adds runtime initialization and stream restoration; only data changes.
`CRTDirectMachineSetup` proves the setup result supplies its ready-state
contract. `Cost/CRTDirectMachine` bounds the actual loop by
`(mtCrtControlTargetC + 2) * totDirectCRT`, including all metadata.
Padding/reversal and complete legacy entry composition are supplied below.

`CRTDirectMachineFull.lean` composes padding, concrete traversal and paired
reversal forward, and reversal, inverse traversal and deletion backward.
`CRTDirectEntry.lean` adds actual runtime setup and complete cleanup: both
entry theorems start from legacy inputs and update only data, with no execution
oracle. `Cost/CRTDirectFull.lean` bounds both full entries by a fixed constant
times `totDirectCRT`. `CRTDirectSource.lean` and `SrcDirectStage.lean` now bridge the complete
entries to both source transforms, preserving their exact original semantics.
`Cost/CRTDirectEntry.lean` matches the named entry and generic-dimension source
costs. `MainProg`, `MainChain` and `MainCorrect` now use these actual source
programs and preserve exact multiplication semantics. `MainTimeRuns`,
`MainTimeGlue`, `MainTime` and `MainStatement` match the running program to
`totDirectBound` and its logarithmic bound. The remaining 22 affected theorem-path modules were refreshed, and
`CompletedProofCheck.lean` passed for 111885 declarations (peak 4.3 GiB),
including the actual public fixed-machine theorem. No full build was used.

Remaining integration steps, in order:

1. **M2b — rotation scanner and producer: complete.** The actual all-fiber
   rotation, workspace provisioning/restoration, runtime descriptor producer,
   exact exposed tape, and matching production/rotation costs are proved.
   These components preserve the existing triangular arithmetic semantics.
2. **M2c — driver and matching: complete.** runtime parameter preparation, paired
   reversal, complete entries and source transforms are proved with linear
   costs. The running main multiplier and its final cost theorem now use
   them; theorem dependencies and the completed-proof audit pass.
   Resampling's linear exposure cost is now separated from the old quadratic
   envelope; connect these sharper stage theorems to the aggregate budget.
3. **M2d — bound:** retune power-of-two parameters only after all machine
   costs match; check the theorem target and its focused axiom audit, then
   update the scoreboard.

The current unconditional saving remains **`2^-93`**. M2a removes a primitive
integration obligation, not the quadratic charge in the running multiplier.
Targeted verification for M2a: compile `Fast/CRTGap.lean` with
`check-lean-safe.py` and `-o .lake/build/lib/lean/IntegerMultBounds/MathlibTM2/Fast/CRTGap.olean`,
then run the same guarded checker on `CRTGapCheck.lean`. Reuse existing
dependency artifacts; no full build is needed.

**Done means:** proved linear CRT swap count, reuse of the already linear
resampling exposure, exact permutation equivalence,
actual-step matching and a retuned end-to-end theorem showing the gain. This
is the first structural change after M1 and removes the tight cap on epsilon.

#### §5 — Fast simultaneous synthetic butterfly layers; Appendix A

**M3 — compact dirty controls.** Replace full K-bit slot transports by compact
control fields of width proportional to `e log p`, following the
[compact-control layout](https://github.com/CrocSwap/integer-mult-bounds/blob/0fdd7d82de03e43c9e5a1000dfbcd380d1b687d2/notes/compact-control-layout.tex).
The target node overhead is `(e log p)^tau`, removing `K^tau`.
Reuse `Compact/*` algebra, dirty-control identities and exceptional-repair
mathematics where their contracts match. Build an adapter to the live Mathlib
`Node/Basis.lean` and `Cost/LayerCost.lean` contracts rather than reviving the
retired native controller architecture.

Prove complete temporary address ranges survive every role split, arbitrary
initial temporary values are restored, and exceptional extraction, sorting,
reinsertion and cleanup are charged at each node's own volume. Add an actual
stopping branch at `e < d^beta` and price the reserved/individual axes.
The target exponents are internal
`tau+(1-beta) max(sigma-tau,0)`, leaf `sigma+beta(1-sigma)` and reservation
`max(1-c,0)`, all strictly below `lambda'`. Current `MatchSynPcs` instead
matches recursion down to level zero, so changing its recurrence on paper
would not change the executed algorithm.

**M4 — linear semantic precision and selected workspace.** The older guard
uses `d^20`; the compact intermediate guard uses `d^(5-4 beta+zeta)`; the
semantic completed-child argument supports a **linear** `C0 d` guard. Prove
completed-child norm/denominator bounds on every role, then an induction on
maximum active child width including literal scalar work and parked operands.
Match it to the actual local word-width calculation; these three published
guards are not interchangeable implementation claims.

For variable-rank recursion, prove explicit simultaneous row-stock envelopes
and bootstrap cutoff validity. The upstream selected-stock audit leaves the
selected reserve coefficients unknown. Derive them from the actual selected
compiler, leaf borrowing and call depth; the enormous recorded headrooms
cannot substitute for that proof.

**Done means:** a Mathlib layer machine with the compact/stopped cost, linear
precision and proved workspace contracts. These remove constraints preventing
large c and, later, large epsilon; neither alone removes §6's layout loss.

#### §6 — Synthetic transforms and their tape layout

**M5 — remove the multiplicative layout loss.** The existing synthetic loop
pays `p K^(tau-1)`, giving saving `epsilon c a_b`. The selected assembly prices
coordinate movement as `p^tau polylog p`, giving saving `a_b`, and uses a
balanced prefix with saving `1-epsilon` instead of `1-epsilon(1+c)`.

Trace the balanced positional transform and arbitrary-source routing contracts
behind the selected outer engine. Implement the corresponding transform
schedule, not just the cheaper analytic formula. Prove both forward and
opposite transforms, original frequency order, untouched spectators and
restoration, retaining the synthetic-character and convolution identities.
Primary integration points: `Fast/SynLay*.lean`, `Fast/SynSel.lean`,
`Cost/MatchSynLay.lean`, `Cost/MatchSynPcs.lean` and `Cost/MatchSynLoop.lean`.
Keep `epsilon(1+c)<1` as a geometric condition even after balancing; the
selected analysis does not require its gap to exceed the final saving.

**Done means:** actual transform/layout steps obey the new charge and compose
with M3–M4. This removes today's active bottleneck and is essential even with
perfect finite suppliers.

#### §7 — Exact normalized polynomial products

Keep exact signed packing, the conventional fast multiplication subroutine,
negacyclic product semantics, normalization and truncation. Recheck input word
widths, carries, product separation and the logarithmic factors under the new
parameters and supplier guard constants. Integration points include
`MathlibTM2/Fast/RingProd.lean`, `Host/SSMul.lean` and `Cost/Growth.lean`.

**Acceptance within M4/M8:** the packed-product charge is below the requested
final exponent with strict room for logarithms and exact output semantics.
No separate supplier or polynomial-product rewrite is justified yet.

#### §8 — Resampling with the permutations left in the transform

**M7a — faster Gaussian inverse, with quantitative errors.** The local
`7/8+3 epsilon/2` estimate cannot allow the selected epsilon near one.
Trace the selected phase-cell/banded inverse argument: one global rounded
matrix, bounded inverse norm, short convolutions and boundary solves. Prove
the same matrix and rounding errors used by the implementation. Existing
`NLogN/Neumann*.lean`, Gaussian and resampling lemmas are candidates for reuse;
they do not by their names establish the new banded inverse theorem.

**M7b — bulk exposure and microbox tape execution.** Build ordered core/halo
windows of that same rounded matrix, bound truncation/locality errors, retain
period cuts and show tensor errors accumulate without a volume factor. Price
sequential window emission, factor-page reuse, overlapping tapes, cropping
and final prime-box order. The inherited construction uses core length about
`p^8`, halo about `p^3` and a band with `w^2 = O(p^(1-r))` where
`alpha^2 ≍ p^r`; the exact selected contracts must be bound before porting.

The target Gaussian arithmetic saving is
`min(1-epsilon-delta, r-delta)`, with `epsilon+r<1` and
`epsilon>(1-r)/2`; bulk exposure has saving `a_b`. Reprove prime supply and
normalization when epsilon increases: a cited short-prime-interval result
must be available as a proved local theorem or replaced by a sufficient
proved construction, not introduced as a custom axiom.

Primary integration points are `Fast/ResampA*.lean`, `Fast/ResampB*.lean`,
`Mult/Sizes.lean`, `Cost/MatchResampA.lean`, `Cost/MatchResampB.lean` and the
`NLogN` analytic library. M2's cheaper routing is a useful earlier waypoint,
but does not prove the new Gaussian or bulk bounds.

**Done means:** implemented forward/inverse maps satisfy the required errors,
normalization, fixed-machine time and selected parameter bands. This is a
major analytic and execution task, not an arithmetic certificate bridge.

#### §9 — Exact integer multiplication and its cost

**M8a — seven-stage bootstrap.** The selected assembler starts at saving
`384599/10^10` and iterates
`a_j = (1-s)s + s a_(j-1)` seven times, with
`s = min(bit_endpoint,(1-beta) complex_endpoint)-10^-27` and
`beta = eta = 10^-24`. Prove each transfer theorem on machines, including
stock, cutoffs, labels and the base construction at that saving. The base
saving `0.0000384599` is itself not supplied by our present theorem: it
requires the corresponding earlier construction or an alternative proved
base strong enough for the recorded seven-stage chain. Substituting our
current tiny saving silently changes the chain and its final certificate.

**M8b — close the selected 47 inequalities and exact recovery.** With the
bootstrapped bit saving `a` and complex saving `b`, the inherited balanced
outer engine chooses `q=a(1-2 eta)`, `c=q+eta/4`,
`epsilon=(1-eta)/(1+q)`, `lambda'=1-q` and an intermediate lambda.
At the selected witness, `epsilon ≈ 0.9983273398029231` and
`c ≈ 0.0016754626768081034`. Its limiting margin is `epsilon q`,
tending to `a/(1+a)`. This replaces our
current `epsilon c a_b`; simply substituting primitive endpoints in our
existing formula cannot reproduce the selected target.

The seven selected margins are:

| Charge, by manuscript section | Selected saving |
| --- | --- |
| §6 balanced prefix | `1-epsilon` |
| §§4, 6 coordinate movement | `a` |
| §5 compact phase layer | `epsilon q` |
| §8 bulk exposure | `a` |
| §8 Gaussian arithmetic | `min(1-epsilon-delta,r-delta)` |
| §§7, 9 scalar work | `1-epsilon-delta` |
| §9 dimension | `epsilon` |

The selected constraint ledger divides into the following **47** entries.
These are acceptance obligations, not 47 completed local theorems.

| Original sections | Count | Exact constraint names in the pinned assembly |
| --- | --- | --- |
| §3 and §5 primitive/stopping ranges | 6 | `bit_positive`, `complex_above_bit`, `complex_below_one_over32`, `beta_positive`, `beta_below_one`, `leaf_saving_above_bit` |
| §5 internal/leaf recurrence | 9 | `q_positive`, `q_below_internal`, `q_below_leaf`, `lambda_above_tau`, `lambda_above_sigma`, `lambda_above_internal`, `lambda_prime_above_lambda`, `compact_leaf`, `lambda_prime_below_one` |
| §5 compact reservations | 4 | `c_positive`, `c_below_one`, `q_below_reservations`, `compact_reservations` |
| §§5, 6, 8, 9 geometry, guard and prime supply | 7 | `epsilon_positive`, `epsilon_below_one`, `guard_width`, `K_geometry`, `K_dominates_log`, `record_suffix`, `prime_interval_packing` |
| §§8, 9 Gaussian precision and normalization | 9 | `phase_local`, `phase_boundary`, `gamma_sublinear`, `cell_above_band`, `alpha_positive`, `alpha_below_one`, `alpha_below_one_fourth`, `delta_positive`, `delta_below_one_eighth` |
| §§4, 6, 8 routing/window allowances | 3 | `short_record_fallback`, `small_field_exposure`, `artificial_boundary` |
| §§3, 5 literal work and row stock | 2 | `literal_scalar_guard`, `row_product_gap` |
| §9.8 final stage absorption | 7 | The seven margin names above, each with suffix `_above_kappa`. |

For each of the 47 constraints, attach its exact rational proof to the local
semantic/cost lemma it enables: identifying a stage is not yet a proof of its
contract. In particular, satisfying a number without that lemma does
not discharge the obligation. Reuse exact product recovery, chirp correctness,
CRT algebra and carry output only after the changed precision, scaling and
permutation contracts are established. Include small-input dispatch.

**Done means:** unconditional
`MathlibTM2.MulInTime (836330098538459 / 500000000000000000)`, one fixed
finite machine, all input pairs, actual-step bounds and the existing standard
axiom set. The source record's assembly hash checks out; cold supplier replay
and all these Lean bridges remain unfinished.

#### §§10–11 — Division, square root and matrix transposition

These are downstream consequences, not inputs to multiplication's saving.
Do not put their formalization on the critical path. After M8, adapt their
reduction interfaces and encoding overhead if those corollaries are desired.

## Execution order and decision gates

1. **M1 complete:** public saving `2^-93`; exact internal margin between
   `2^-93` and `2^-92`, with the existing existential theorem preserved.
2. **M2 in progress:** complete all-fiber rotation, workspace restoration,
   width setup, generator kernels, linear schedule and distant exposure/cleanup
   checked; descriptor production and full target execution are complete. Finish
   concrete driver integration, then retune and publish
   the resulting stronger theorem. This yields a structural improvement
   without importing the large selected supplier inventory.
3. **M3–M5:** compact controls, width/stock contracts and balanced coordinate
   routing. Establish these interfaces first using the current smaller
   networks. Prove and record intermediate unconditional bounds after each
   complete integration; do not promise a numerical waypoint before costing it.
4. **M6 and M7:** port the selected suppliers and the sharper Gaussian/bulk
   pipeline against those established interfaces. Neither branch alone
   yields the goal; both feed M8. Source-contract analysis can begin earlier.
5. **M8:** prove the bootstrap base and stages, close all 47 linked obligations,
   validate exact recovery and publish the target theorem.

At every gate, record the achieved saving, the minimum remaining cost margin,
its manuscript section and the next binding lemma. A milestone can finish
without changing the bound, but must say which restriction it removed.
Retain reusable frame/rank/precision mathematics until its role is resolved.
Use only guarded Lean scripts, preserve proof limits and integrity, exclude
unrelated work, and commit/push each checked logical section. The original
planning update checked the selected bootstrap and final-margin
arithmetic against the pinned assembly. M1 now additionally has a checked
Lean machine theorem and focused axiom audit; M2–M8 remain unfinished.
