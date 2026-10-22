# Plan and progress

✅ Complete · 🟡 In progress / partially complete · ⬜ Not started.

**Bound improvement progress:** M1 ✅ · M2 ✅ · M3 🟡 · M4 ⬜ · M5 🟡 · M6 🟡 · M7 🟡 · M8 ⬜ (legacy route deferred) · M9 ⬜ · M10 ⬜ · M11 ⬜.
The completed compact multiplier proves saving `3299646951/2^46 ≈ 2^-14.3803`. With today's bit
supplier (PR97 stage 2, the opposite-bank compiler on plain frames) no route in this plan exceeds
about `2^-13.33`; going further needs a better bit supplier.
The long-term target is **unconditional `kappa = 0.0023`**, with smaller checked
machine bounds delivered along the way. Design-B is active work, not yet a public bound.

## Bound scoreboard

We measure progress by the **proved exponent saving `kappa`** in worst-case
time `O(n (log n)^(1-kappa))`. Larger saving means a smaller time exponent.

| Bound | Exponent saving `kappa` | Proved (UTC) | Status |
| --- | --- | --- | --- |
| **Current unconditional result** | **`3299646951/2^46 ≈ 2^-14.3803`** | 2026-10-21 10:10 | ✅ PR97 stage 2: the bit interchange's root runs the stage-2 supplier (`M8/Stage2Machine/Total`): the reversed family over atoms with variable-rank block children (#104's opposite-bank compiler on plain frames, stopped recursion at `tau* = 1-969/10^7`) inside the F L F wrapper, width `theta = 1/1000`. `tau = 1-96806834039/10^15` replaces `1-3734039/10^12`, about `26` times the saving. `lambda = 1-9680683/10^11`, `lambda' = 1-9680682/10^11` sit just above `tau`; the layer margin `epsilon (1-lambda')` binds, rounded down to `2^-46`. |
| **Previous full-width result** | `127238784/2^46 ≈ 2^-19.0770` | 2026-10-19 06:54 | ✅ Superseded; full-width chunks: the chunk root is `Kroot = ⌈d/2⌉` (`c = 1`), so the layout margin is `epsilon (1-tau)`. The direct-round log factor is bounded by the legacy `2^-32` chunk, so it no longer caps `c`. `lambda = 1-3734/10^9`, `lambda' = 1-3733/10^9` sit just above `tau`; the layer margin `epsilon (1-lambda')` binds, rounded down to `2^-46`. |
| **Previous PR97 seven-eighths result** | `111364923/2^46 ≈ 2^-19.2693` | 2026-10-19 01:42 | ✅ Superseded; PR 6: the bit interchange runs PR97's two-stage partial-swap word with rank-one children on the recursive interchange machine, made generic in the bit network (`MathlibTM2/M8/`). The word needs no routes, charts, cover classes or helper hosting. `tau = 1-3734039/10^12` replaces Shared50's `1-296/10^11`, about `1261` times the saving. `lambda = 1-35/10^7`, `lambda' = 1-33/10^7`; the layout margin `epsilon c (1-tau)` binds, rounded down to `2^-46` ([note](docs/pr97-stage1/pr97-stage1.pdf)). |
| **Previous T16 seven-eighths result** | `88279/2^46 ≈ 2^-29.5702` | 2026-10-18 17:18 | ✅ Superseded; T16 node with seven-eighths-power chunks `K = ⌊d^(7/8)⌋` (`c = 7/8`, from PR 4). The binding layout margin `epsilon c (1-tau)` grows by `7/2`; `lambda = 1-28/10^10`, `lambda' = 1-23/2^33` keep the layer margin `epsilon (1-lambda')` above it. The saving is the layout margin rounded down to `2^-46`. |
| **Previous T16 result** | `25222/2^46 ≈ 2^-31.3776` | 2026-10-18 09:47 | ✅ Superseded; T16 layer node: 73 slots, 14336 data roles and 8 private centres, 1,041,408 children (`log_73 (F/NW) < 999/1000`), lowered to factors, half-integral gates, translations, slot XORs and slot phases on the layer machine. With `lambda = 1-2/10^9`, `lambda' = 1-2^-30` the layer margin `epsilon (1-lambda')` no longer binds; the saving is the layout margin `epsilon c (1-tau)` rounded down. |
| **PR 4 mixer result** | `651/2^39 ≈ 2^-29.6534` | 2026-10-18 05:03 (branch) | Proved on the `further-improvements` branch only; not adopted. Size-25 mixer supplier (`sigma = 1-25/10^10`) with `c = 7/8`, binding layer margin `epsilon (1-lambda')` at `lambda' = 1-21/2^33`. T16 replaces the mixer in the complex-supplier slot. |
| **Previous T25 result** | `14229/2^46 ≈ 2^-32.2035` | 2026-10-17 21:11 | ✅ Superseded; retune to `epsilon=31/64`, `delta=2^-7`, `lambda'=1-459/2^40`: the Schönhage–Strassen allowance is `M(p) = p^{1+2^-7}`, the resampling envelope uses the logarithmic band width `α ≤ 4 b^{ε/2^33}`, and every size relation (moduli room, `d ≤ 2^(ℓ-1)`, `d+1 ≤ ℓ`, `16 d α² ≤ b`) is re-proved from `d^64 ≤ b^31` with `d ≥ 2^192`. All-input correctness and cost bound on one fixed finite Mathlib machine. |
| **Previous T25 dimension result** | `3213/2^44 ≈ 2^-32.3512` | 2026-10-17 19:40 | ✅ Superseded; `epsilon=7/16`, `delta=2^-5`. |
| **Previous dyadic-dimension result** | `36261/2^48 ≈ 2^-32.8539` | 2026-10-17 17:29 | ✅ Superseded; `epsilon=79/256`, capped by the coarse `α ≤ 2√d` resampling bound. |
| **Previous rounded result** | `2^-33.0000` | 2026-10-17 08:08 | ✅ Rounded synthetic layers and transforms at `epsilon=9/32`. |
| **Previous dyadic result** | `2^-34` | 2026-10-15 21:00 | ✅ Superseded by rounded synthetic layers, which allow the `9/32` dimension. |
| **Previous eighth-root result** | `2^-35` | 2026-10-15 19:56 | ✅ Superseded by the audited dyadic dimension retune and fourth-root chunks. |
| **Previous dimension result** | `2^-36` | 2026-10-15 19:25 | ✅ Superseded by the audited eighth-root retune and sharper logarithmic cost estimates. |
| **Previous compact result** | `2^-37` | 2026-10-15 18:55 | ✅ Superseded by the checked sixteenth-root dimension retune. |
| **Historical M2 result** | `2^-66` | 2026-10-15 12:42 | ✅ Superseded; the current theorem improves the public saving by more than `2^36`, not a measured runtime speedup. |
| **Historical M1 result** | `2^-93` | 2026-10-15 09:37 | M2 improves the public exponent saving by `2^27`; this is not a timing speedup. |
| **Pre-M1 unconditional result** | `296 / (10^11 * 2^131)` (between `2^-160` and `2^-159`) | 2026-10-15 05:31 | Superseded by M1; the existential theorem remains compatible. |
| **Intermediate benchmark: selected community construction** | **`836330098538459 / 500000000000000000 = 0.001672660197076918`** | — | ⬜ Not yet proved here. Upstream construction is conditional; matching this saving is a benchmark, not a requirement to reproduce its older construction. |
| **Long-term target: productive helper construction** | **`23/10000 = 0.0023`** | — | ⬜ Upstream PR 4359 is conditional; requires new supplier, compiler, cover, and outer execution proofs here. |

The long-term target corresponds to a log exponent of `0.9977`.
The intermediate benchmark corresponds to `0.998327339802923082`.
These are asymptotic exponent bounds, not measured execution speedups.
Update the current-result row only after the stronger machine theorem passes
the guarded checks and axiom audit; parameter arithmetic or a finite
certificate alone does not improve the proved multiplication bound.

**Integer multiplication below `n log n` is proved.**
`IntegerMultBounds.MathlibTM2.statement` constructs a fixed finite Mathlib
machine that multiplies every input pair correctly in worst-case time
`O(n (log n)^(1-kappa))`, with positive saving
`kappa = 3299646951/2^46`. No algorithmic or runtime assumption remains.

## Completed proof

| Part of the proof | Source | Mathematics | Tape | Files |
| --- | --- | --- | --- | --- |
| [Proved Mathlib end-to-end multiplier](plan/C-mathlib-end-to-end.md) | — | ✅ 1/1 | ✅ 1/1 | 700 |

The [proof details](plan/C-mathlib-end-to-end.md) cover the numerical
algorithm, recursive layers, transforms, resampling, CRT routing, exact
recovery, fixed-machine assembly and actual step bound. All are complete.
The machine model is Mathlib's `Turing.FinTM2`, with standard binary encodings.
The Files column counts the components listed in that detail file; the full
transitive proof dependency set is larger, as recorded by the
[retention audit](docs/proof-retention.md).

At `3299646951/2^46` the checks pass: `CompletedProofCheck` (only `propext`, `Classical.choice` and
`Quot.sound`), `AxiomAudit` (90354 declarations) and `CompactControlCheck` (521 contracts).
The native-machine bridge and its `MathlibTM2Check`/`FastPathCheck` audits were removed
2026-10-18 (restore from 5e12c129).

**Corollary.** `MathlibTM2.DFT.dftInTime : DFTInTime (3299646951/2^46)`: one fixed finite machine
computes the discrete Fourier transform over every prime field `F_p`, at every length with a
primitive root of unity, in time `O(N (log N)^(1-kappa))` (`docs/dft/dft.pdf`).

## Where the bound stands

Parameters (`Cost/CompactInterimParameters.lean`): `epsilon = 31/64`, chunk root `⌈d/2⌉` (`c = 1`),
`tau = 1-96806834039/10^15` (`Parameters.tau`, the selected bit supplier's exponent),
`lambda = 1-9680683/10^11`, `lambda' = 1-9680682/10^11`, `delta = 2^-7`.

| Stage margin | Formula | Value |
| --- | --- | --- |
| Compact layer (binding) | `epsilon (1-lambda')` | `4.6891e-5 ≈ 2^-14.380`, rounded down to `kappa` |
| Chunk-exchange layout | `epsilon (1-tau)` | `4.6891e-5 ≈ 2^-14.380` |
| CRT and resampling exposure | `(1-epsilon)(1-tau)` | `4.9916e-5 ≈ 2^-14.290` |
| Gaussian resampling | `1/2 - delta - epsilon(1+2^-33)` | `2^-7 - 31/2^39 ≈ 2^-7.0` |
| Direct rounds | `epsilon (1-2^-32)` | `0.484` |
| Prefix (M5a) | `1-epsilon` | `0.516` |

**The `tau` ceiling.** `1-tau = 9.68e-5 ≈ 2^-13.33` is the saving of the bit interchange. Every
margin near the top of the table carries it. The layer margin carries it too, because
`lambda' > lambda > tau`.

- **Retuning alone** is exhausted: the layout and layer margins both sit at `epsilon (1-tau)`,
  and the exposure margin `(1-epsilon)(1-tau)` falls as `epsilon` rises.
- **Near-one dimensions** reach about `1-tau ≈ 2^-13.33`, one bit. That needs `epsilon → 1`, which
  needs M7, M5b and the bulk exposure transfer
  ([NearOne/DESIGN.md](IntegerMultBounds/MathlibTM2/NearOne/DESIGN.md) §c).
- **Beyond `2^-13.33`** a better bit supplier is necessary (M6, then M10). Upstream's selected PR589 supplier
  has bit saving `10/5769`, but its accounting does not transfer to this machine: helper hosting,
  port routes and frame changes are not free here ([pr589-hole](docs/pr589-hole/pr589-hole.pdf)).
  The cover-free suppliers and candidate improvements are ranked in the
  [PR97 note](docs/pr97-stage1/pr97-stage1.pdf): PR97 with flag-basis corner runs
  (`a_b = 6.40e-5`), and #104's opposite-bank compiler on PR97 (`9.70e-5` plain frames, now in
  the proof, and `1.24e-4` design-B frames, not yet integrated).

## Bottlenecks by manuscript section

Section numbers are the [original manuscript](plan/D-sharper-bound.md)'s printed numbers.

| Manuscript section | Progress | What limits our bound | Improvement needed |
| --- | --- | --- | --- |
| §2 Machine model and streams | 🟡 | Every new algorithm needs actual finite-machine costs and clean returned state. | Price new schedules with the existing host primitives. |
| §3 Finite networks | 🟡 | Bit saving `1-tau = 9.68e-5` (PR97 stage 2, plain frames) caps every margin. Complex: T16 at `log_73 (F/NW) < 999/1000`, in the proof. | Design-B checkpoint (M6), then productive complex jobs and delayed-cover BIT (M9–M10). |
| §4 Address interchange | 🟡 | Field moves inherit `tau`; the CRT uses linear direct routing. | Arbitrary-source coordinate routing (M5b). |
| §5 Butterfly layers; Appendix A | 🟡 | The T16 node takes the layer margin off the critical path. | General supplier closure, stopped recursion, precision and recursive stock (M3, M4), instantiated for M9. |
| **§6 Synthetic transforms/layout** | 🟡 | **The layout margin `epsilon (1-tau)` and the layer margin `epsilon (1-lambda')` bind together.** The balanced prefix (M5a) and full-width chunks are done. | M5b with `epsilon → 1` lifts the layout margin to `1-tau`. |
| §7 Exact polynomial products | ✅ | Packing widths must stay within budget. Not binding. | Revalidate under new widths. |
| §8 Resampling | 🟡 | The Gaussian margin keeps `epsilon < 1/2`. | The rest of M7: tape costs and bulk core/halo execution. |
| §9 Exact multiplication/cost | 🟡 | The exposure margin `(1-epsilon)(1-tau)`. The moduli are short-interval primes, so they no longer bound `epsilon`. | Grouped/fused bulk exposure and complete outer execution (M11); legacy M8 is deferred. |
| §§10–11 Corollaries | 🟡 | Not multiplication bottlenecks. | DFT over `F_p` done (`dftInTime`); division, square root and transposition not started. |

## Milestones

✅ means the whole deliverable is checked. M1–M8 are historical identifiers, loosely
organized by manuscript section, not a dependency order. The execution order below
controls the active queue. The [implementation plan](plan/D-sharper-bound.md) and
linked design notes contain reusable details and historical checkpoints; their older
parameter choices and route-specific completion lists are not all prerequisites for 0.0023.

| ID | Progress | Sections | Deliverable | Status |
| --- | --- | --- | --- | --- |
| M1 | ✅ | §§5, 6, 9 | Retune the existing construction. | Historical, `kappa = 2^-93`. |
| M2 | ✅ | §§4.3, 8.2, 9.3 | Direct nonadjacent CRT swaps. | Historical, `kappa = 2^-66`; the running CRT still uses it. |
| M3 | 🟡 | §5.2–5.3, App. A | Compact controls, caller integration, stopped recursion. | Compact integration complete; it is the current theorem. Stopped-recursion integration remains. |
| M4 | ⬜ | §5.4, §9.7 | Linear child-precision bound; recursive workspace and stock. | Derive constants from the actual finite template and account for simultaneous owned centers and BIT stock; feed M9–M11. |
| M5 | 🟡 | §6.2, §4 | Balanced prefix (M5a); arbitrary-source routing (M5b). | M5a done (`CompactStageGrowth.prefix_le`). M5b open ([design](IntegerMultBounds/MathlibTM2/Balanced/DESIGN.md)). |
| M6 | 🟡 | §§3–5 | Selected finite suppliers in the machine. | T16 complex supplier and the PR97 bit supplier are in the proof. Stage 2 (variable-rank children, #104's opposite-bank compiler on plain frames) is the running bit supplier: the moment gaps (`Stage2Moments`), atom adapters (`AtomSegment`, `AtomRoleSegment`), the stopped recurrence (`Rev97Ranks.rev97_closed`), the reversed family with data (`RevMachine.RevSemantics.rev97_family_spec`), the F L F wrapper and width selection (`Stage2Machine.Bound.uniform_bound`), seamed in by `Stage2Machine.Total`. Design-B frames (`1.24e-4` supplier saving) are active: scalar semantics, the full backward-weight recurrence, extensive geometry checks and auxiliary/target frame chains are checked. Source coverage/order and exact source traces are checked; source-chain nesting, boundary transitions and node/cost integration remain. Use the checkpoint below. PR589 bit side checked under upstream's idealization (`M6/Bit*`, outside the root); it does not run on this machine ([design](IntegerMultBounds/MathlibTM2/M6/DESIGN.md)). |
| M7 | 🟡 | §§8, 9.2, 9.7 | Faster rounded Gaussian inverse, prime supply, bulk execution. | Prime supply done (`primes_in_window`, `primeSrc_good`). Rounded inverse composed (`rounded_inverse`); chirped forward map approximated (`chirpA_approx`). Tape costs and bulk execution remain ([design](IntegerMultBounds/MathlibTM2/NearOne/DESIGN.md)); align new work with M11's fused, support-local outer contracts before implementing an older schedule. |
| M8 | ⬜ | §9.1–9.8 | Legacy selected bootstrap and 47 inequalities. | Deferred as a route-specific package. Reuse applicable transfer lemmas; reproducing its seven stages or PR589 supplier is not required for M11. |
| M9 | ⬜ | New supplier/compiler | Productive mixed jobs compiled into a finite uniform supplier. | Prove arbitrary-input endpoints, ownership, complements, integer batching and chronological execution; instantiate the p3 complex controller at uniform saving `0.002304`. Depends on the supplier closure and precision/stock work in M3–M4. |
| M10 | ⬜ | New BIT supplier | Delayed ambient cover and ordinary BIT saving above `0.0027`. | Use M9's mixed-job construction with projector covariance, common weights, modular matchers, priced cover routing and bad-class fallback; raise the atom exponent and prove the new stock bound. Reuse generic stopped-recurrence and wrapper results. |
| M11 | ⬜ | New outer assembly | Unconditional fixed-machine theorem at `kappa = 0.0023`. | Combine M9–M10 with M4, M5b and the adapted M7 work: grouped/fused execution, global support-local phases, boundary matrix costs, new sizing and every outer cost matched to actual execution. |

## Execution order and decision gates

**Current design-B checkpoint (independent of routing).** The structural adjoint,
pending-use and combined-boundary lemmas are generic in the DAG or operation list;
they are useful beyond the concrete design-B tables. The full backward-weight
recurrence, auxiliary/target frame chains, source coverage/order and exact source traces
are now checked. Connect the remaining source-wire traces to their signed frame chains.
Current details are in [M8/DESIGN.md §16](IntegerMultBounds/MathlibTM2/M8/DESIGN.md#16-design-b-frames).

**Then assess the remaining design-B integration.** Continue through boundary transitions,
node semantics, exact rank/cost linkage, supplier replacement and retuning if these
fit the existing recursive machine. The full design-B target is
`4222422970/2^46 ≈ 0.0000600042`, about 28% above today's bound; it remains a projection
until the actual implemented histogram and machine theorem are checked. If integration
requires another major construction, reassess before expanding the scope. Do not pursue
further design-B-specific optimization. Its final concrete supplier can later be replaced;
its generic compiler/frame proofs survive. Design-B is not a prerequisite for M9–M11.

**Define the new contracts before further old-route integration.** Pin the M9 mixed-job
interface and M11 outer execution requirements, then direct M3–M5 and M7 work toward them.
Keep generic stopped recursion, completed-child precision, owned storage, coordinate
routing, analytic identities and exact recovery. Do not finish an older scanner, reserve,
Gaussian schedule or numerical bootstrap solely to check off a historical milestone.
The older PR589 machine integration and exact M8 seven-stage/47-inequality package are
optional alternatives, not the active critical path.

**Develop suppliers and outer execution as separate work streams.** M9 supplies the
finite mixed-to-uniform construction shared with M10; M10 supplies the stronger ordinary
BIT bound. M4's bounds must close for those actual templates. M5b and the adapted M7 work
supply M11's routing and grouped/fused execution. Preserve the current multiplier as a
working instance while introducing the needed general interfaces.

**Integrate smaller wins whenever all affected costs close.** Design-B is the immediate
candidate. Later routing, resampling and supplier improvements may yield intermediate
bounds before M11 is complete; each must include every affected execution and cost
contract. With today's supplier the near-one route is limited by its approximately
`0.000096807` saving. With the new complex saving but today's dimension, the layer
margin alone is only `0.001116`: reaching 0.0023 needs both work streams. These are
planning margins, not promised intermediate machine theorems. Reaching or exceeding
`0.001672660197076918` is a useful benchmark by whichever proved route reaches it first.

After each successful integration, record the proved saving, binding margin and guarded
checks/axiom audit. Component certificates and parameter arithmetic do not move the scoreboard.
The current numerical saving already exceeds the old bootstrap base `0.0000384599`;
whether it supplies a particular bootstrap interface still requires an explicit theorem.

## Routing work packages (M5b)

Routing is now an active work stream alongside the design-B checkpoint. R1–R4 are
local work-package labels in dependency order, not replacements for M1–M11. They
must provide the global support and spectator contracts required by M11, not only
the old layout's cheaper numerical bound. Implementation notes and the next concrete
obligation are in [Routing/DESIGN.md](IntegerMultBounds/MathlibTM2/Routing/DESIGN.md).

| Package | Status | Deliverable and acceptance gate | Additional Lean, estimate |
| --- | --- | --- | --- |
| R1 selective updates | 🟡 | Ideal arbitrary-source coordinate shear, preserved sources/spectators, global bijectivity and arbitrary borrowed-control restoration; then bind the packed modular gadget on its good set. Logical/packed endpoints, coordinate decoding, physical target-bit identities and spectator density checked. Ordered scattered-source gathering has host execution, cleanup and cost. Self-reading upper target bits and their physical source coordinates are proved. Active-target masks, arbitrary source ordering, field moves and full rotation binding remain. | 2–3k |
| R2 exact repair | ⬜ | Flag, extract, key, sort and reinsert exceptional records. Reuse `Compact/RepairPipeline` mathematics, but prove the actual scan programs, clean scratch and cost from the bad-set density. Depends on R1's packed good-set contract. | 3–5k |
| R3 complete router | ⬜ | Matching/reservoir partition, permutation decomposition, descriptor generation and short-record fallback. Compose R1–R2 into a full arbitrary-coordinate routing program, with all borrowed fields restored. | 3–5k |
| R4 integration and support | ⬜ | Forward/inverse layout replacement and cost matching; preserve reserved coordinates and a complete untouched suffix for M11's grouped phases. Supplies S4's movement interface. | 3–6k |

R1 checkpoint: `Routing/Shear` and `PackedShear` prove the logical and packed
endpoints, arbitrary borrowed-field restoration, target upper-bit preservation,
and exceptional-set/repair identities. `Coordinates.program_decode` identifies the
packed endpoint with the requested coordinate shear; `PhysicalBits.program_physical`
identifies the actual radix-two target bits. `Density.encoded_repair_density` retains
the complete source/spectator tensor without changing the exceptional fraction.
`SourceGather.sourceOffset_exec` implements gathering and spreading **in increasing
source order**, restores gathering scratch, and charges `8 W + 8 n G + 2 n + 18`
host steps. `packed_read_eq` identifies its offset with the packed gadget's source
value. Source/mask registers are inputs to this call, so mask setup remains charged
at the future caller; arbitrary source ordering is not silently supplied by a mask.
`SelfRead` now loads from actual intermediate upper target bits, proves agreement
with the frozen-source program, and preserves the exceptional set; `SourceBits`
identifies arbitrary ordered physical upper-bit sources. No copied source field is
assumed in this extension. The new checks peak below 1.2 GiB. R1 is still open:
add active-target masks (including unselected digit low bits as sources), bind
arbitrary source ordering,
field placement/interchanges, mask setup, all modular rotations and cleanup to a
complete priced host execution. Kappa is unchanged.

Estimated routing total: **11–19k additional or substantially revised Lean lines**,
rounded to 10–20k for planning; excludes generated data and Python. Existing layout,
CRT-control, rotation and sorting primitives are reused. R1's logical identity is
not a tape implementation: source gathering, packed loads, guards, repair and their
costs must be proved before the router can improve a machine bound. Do not introduce
a free arbitrary-source read or a zero-initialized borrowed-control assumption.

## Resampling work packages (M7 and M11)

These packages prioritize shared arithmetic and the new fused schedule. The older
[NearOne design](IntegerMultBounds/MathlibTM2/NearOne/DESIGN.md) remains a mathematics
index, but its status and estimates are historical: `Mult/ShortConv` and `Mult/ChirpRing`
are absent from the current checkout, despite being listed there as completed.
Locate reusable versions in history or reconstruct those bridges before claiming S1
complete. The existing chirped-forward and phase-cell inverse/error theorems remain.

| Package | Status | Deliverable and acceptance gate | Additional Lean, estimate |
| --- | --- | --- | --- |
| S1 shared short convolution | ⬜ | Pad and pack blocks, invoke the existing ring-product stage, extract coefficients, and establish exact register effects, rounding error, cost and scratch restoration. Shared by S2 and S3. | 1–3k |
| S2 fast forward map | 🟡 math / ⬜ machine | Implement the chirped-correlation formula using S1, with executable coefficient tables, overlapping input windows and a proved forward-resampling contract. | 3–5k |
| S3 fast inverse map | 🟡 math / ⬜ machine | Cell-interior products, boundary preparation/solve, coupling and recovery, with precision and actual line costs. Reuse the phase-cell mathematics and band primitives; fix the interface to S4–S5 before implementing a legacy whole-axis schedule. | 6–10k |
| S4 grouped/fused execution | ⬜ | Ordered core/halo neighborhoods, overlap/cropping, reusable setup, error composition and full-tensor support. Combine S2–S3 with R4 so exposure is not repaid per axis. Preserve reserved chunks and restore layouts before subsequent phases. | 8–16k |
| S5 boundary work | ⬜ | Fast boundary matrix operations required by the new parameter regime, including numerical stability, coefficient widths and actual tape costs. Specify this interface with S3–S4; the old band solve alone does not establish it. | 4–10k |
| S6 outer integration | ⬜ | New sizing and precision, both resampling directions, bulk CRT/exposure and every changed cost matched into the final machine. Depends on R4, S4–S5 and M4; closes M11 with M9–M10. | 3–6k |

Estimated resampling/outer-integration total: **25–50k additional or substantially
revised Lean lines**, excluding R1–R4, M9–M10 and generated data. This is a lower-confidence
scope estimate, especially for fused execution and boundary work, not a delivery-time
estimate. The rows partition the intended work; shared helpers should be proved once.
S1 is the smallest independent implementation milestone. Neither S1 nor R1 alone
raises kappa; integrate a new public bound only when all affected costs close.

## Long-term source and proof obligations

The new direction follows [PR 4359](https://github.com/CrocSwap/integer-mult-bounds/pull/4359),
pinned for this assessment to `da637c87c89482bc4c86be36bd0071b3d400dbed`:

- [Finite precompilation](https://github.com/zxv/integer-mult-bounds/blob/da637c87c89482bc4c86be36bd0071b3d400dbed/research/kappa-rebuild/architecture/FINITE-PRECOMPILATION.md): autonomous productive jobs, paid complementary axes, exact integer batch matching and an acyclic execution schedule.
- [Finite-template closure](https://github.com/zxv/integer-mult-bounds/blob/da637c87c89482bc4c86be36bd0071b3d400dbed/research/kappa-rebuild/transfer-audit/FINITE-TEMPLATE-CLOSURE.md): fresh linear semantic precision and actual simultaneous storage, including uncredited owned centers.
- [Outer transfer audit](https://github.com/zxv/integer-mult-bounds/blob/da637c87c89482bc4c86be36bd0071b3d400dbed/research/kappa-rebuild/transfer-audit/OUTER-TRANSFER-AUDIT.md): delayed BIT cover, changed atom width and reserves, global support-local scheduling and the nine outer charges.

These are conditional written arguments and replay evidence, not Lean proofs. Prove the
compiler structurally for arbitrary finite data and instantiate the local certificates last;
do not materialize the astronomical winning uniform word. Rank counts alone do not prove
native adapters, arbitrary-input semantics or ownership. Cover routing must preserve one
common external weight and pay fallback classes; reserves must include simultaneous stock.

The old outer ledger cannot be retuned to the new target: Gaussian resampling restricts
its dimension exponent to below one half, and its exposure saving collapses near one.
M11 needs the grouped/fused and support-local outer construction at dimension exponent
`0.99999`, including boundary matrix execution/error bounds and deferred reserved axes.
The upstream minimum outer saving is `0.00230197698`, leaving only `0.00000197698`
above the target; every charge must be justified by the implemented machine.

The older selected construction remains a conditional benchmark. Its
[selected record](https://github.com/CrocSwap/integer-mult-bounds/blob/0fdd7d82de03e43c9e5a1000dfbcd380d1b687d2/certificates/selected-result.json)
and [pinned source evidence](docs/sharper-bound-source.json) are retained for provenance,
not as a requirement to implement its entire route.

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
