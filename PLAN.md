# Plan and progress

✅ Complete · 🟡 In progress / partially complete · ⬜ Not started.

**Bound improvement progress:** M1 ✅ · M2 ✅ · M3 🟡 · M4 ⬜ · M5 🟡 · M6 🟡 · M7 🟡 · M8 ⬜.
The completed compact multiplier proves saving `127238784/2^46 ≈ 2^-19.0770`. With today's bit
supplier (PR97, rank-one children) no route in this plan exceeds about `2^-18.0`; going further
needs a better bit supplier.

## Bound scoreboard

We measure progress by the **proved exponent saving `kappa`** in worst-case
time `O(n (log n)^(1-kappa))`. Larger saving means a smaller time exponent.

| Bound | Exponent saving `kappa` | Proved (UTC) | Status |
| --- | --- | --- | --- |
| **Current unconditional result** | **`127238784/2^46 ≈ 2^-19.0770`** | 2026-10-19 06:54 | ✅ Full-width chunks: the chunk root is `Kroot = ⌈d/2⌉` (`c = 1`), so the layout margin is `epsilon (1-tau)`. The direct-round log factor is bounded by the legacy `2^-32` chunk, so it no longer caps `c`. `lambda = 1-3734/10^9`, `lambda' = 1-3733/10^9` sit just above `tau`; the layer margin `epsilon (1-lambda')` binds, rounded down to `2^-46`. |
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
| **Goal: match the selected community construction** | **`836330098538459 / 500000000000000000 = 0.001672660197076918`** | — | ⬜ Not yet proved here. Upstream construction is conditional; our goal is an unconditional machine theorem at this exact saving. |

The goal corresponds to a log exponent of `0.998327339802923082`.
These are asymptotic exponent bounds, not measured execution speedups.
Update the current-result row only after the stronger machine theorem passes
the guarded checks and axiom audit; parameter arithmetic or a finite
certificate alone does not improve the proved multiplication bound.

**Integer multiplication below `n log n` is proved.**
`IntegerMultBounds.MathlibTM2.statement` constructs a fixed finite Mathlib
machine that multiplies every input pair correctly in worst-case time
`O(n (log n)^(1-kappa))`, with positive saving
`kappa = 127238784/2^46`. No algorithmic or runtime assumption remains.

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

At `127238784/2^46` the checks pass: `CompletedProofCheck` (only `propext`, `Classical.choice` and
`Quot.sound`), `AxiomAudit` (100026 declarations) and `CompactControlCheck` (552 contracts).
The native-machine bridge and its `MathlibTM2Check`/`FastPathCheck` audits were removed
2026-10-18 (restore from 5e12c129).

**Corollary.** `MathlibTM2.DFT.dftInTime : DFTInTime (127238784/2^46)`: one fixed finite machine
computes the discrete Fourier transform over every prime field `F_p`, at every length with a
primitive root of unity, in time `O(N (log N)^(1-kappa))` (`docs/dft/dft.pdf`).

## Where the bound stands

Parameters (`Cost/CompactInterimParameters.lean`): `epsilon = 31/64`, chunk root `⌈d/2⌉` (`c = 1`),
`tau = 1-3734039/10^12` (`Parameters.tau`, the selected bit supplier's exponent),
`lambda = 1-3734/10^9`, `lambda' = 1-3733/10^9`, `delta = 2^-7`.

| Stage margin | Formula | Value |
| --- | --- | --- |
| Compact layer (binding) | `epsilon (1-lambda')` | `1.8082e-6 ≈ 2^-19.077`, rounded down to `kappa` |
| Chunk-exchange layout | `epsilon (1-tau)` | `1.8087e-6 ≈ 2^-19.077` |
| CRT and resampling exposure | `(1-epsilon)(1-tau)` | `1.9254e-6 ≈ 2^-18.986` |
| Gaussian resampling | `1/2 - delta - epsilon(1+2^-33)` | `2^-7 - 31/2^39 ≈ 2^-7.0` |
| Direct rounds | `epsilon (1-2^-32)` | `0.484` |
| Prefix (M5a) | `1-epsilon` | `0.516` |

**The `tau` ceiling.** `1-tau = 3.73e-6 ≈ 2^-18.03` is the saving of the bit interchange. Every
margin near the top of the table carries it. The layer margin carries it too, because
`lambda' > lambda > tau`.

- **Retuning alone** is exhausted: the layout and layer margins both sit at `epsilon (1-tau)`,
  and the exposure margin `(1-epsilon)(1-tau)` falls as `epsilon` rises.
- **Near-one dimensions** reach about `1-tau ≈ 2^-18.0`, one bit. That needs `epsilon → 1`, which
  needs M7, M5b and the bulk exposure transfer
  ([NearOne/DESIGN.md](IntegerMultBounds/MathlibTM2/NearOne/DESIGN.md) §c).
- **Beyond `2^-18.0`** only a better bit supplier helps (M6). Upstream's selected PR589 supplier
  has bit saving `10/5769`, but its accounting does not transfer to this machine: helper hosting,
  port routes and frame changes are not free here ([pr589-hole](docs/pr589-hole/pr589-hole.pdf)).
  The cover-free suppliers that do run here are ranked in the
  [PR97 note](docs/pr97-stage1/pr97-stage1.pdf): PR97 with flag-basis corner runs
  (`a_b = 6.40e-5`), and #104's opposite-bank compiler on PR97 (`9.70e-5` plain frames,
  `1.24e-4` design-B frames, about `2^-14.6` and `2^-14.2`).

## Bottlenecks by manuscript section

Section numbers are the [original manuscript](plan/D-sharper-bound.md)'s printed numbers.

| Manuscript section | Progress | What limits our bound | Improvement needed |
| --- | --- | --- | --- |
| §2 Machine model and streams | 🟡 | Every new algorithm needs actual finite-machine costs and clean returned state. | Price new schedules with the existing host primitives. |
| §3 Finite networks | 🟡 | Bit saving `1-tau = 3.73e-6` (PR97, rank-one children) caps every margin. Complex: T16 at `log_73 (F/NW) < 999/1000`, in the proof. | Variable-rank bit children: PR97 corner runs, then #104's opposite-bank compiler (M6). |
| §4 Address interchange | 🟡 | Field moves inherit `tau`; the CRT uses linear direct routing. | Arbitrary-source coordinate routing (M5b). |
| §5 Butterfly layers; Appendix A | 🟡 | The T16 node takes the layer margin off the critical path. | Stopped recursion, precision and recursive stock (M3, M4). |
| **§6 Synthetic transforms/layout** | 🟡 | **The layout margin `epsilon (1-tau)` and the layer margin `epsilon (1-lambda')` bind together.** The balanced prefix (M5a) and full-width chunks are done. | M5b with `epsilon → 1` lifts the layout margin to `1-tau`. |
| §7 Exact polynomial products | ✅ | Packing widths must stay within budget. Not binding. | Revalidate under new widths. |
| §8 Resampling | 🟡 | The Gaussian margin keeps `epsilon < 1/2`. | The rest of M7: tape costs and bulk core/halo execution. |
| §9 Exact multiplication/cost | 🟡 | The exposure margin `(1-epsilon)(1-tau)`. The moduli are short-interval primes, so they no longer bound `epsilon`. | Bulk exposure transfer; the M8 bootstrap. |
| §§10–11 Corollaries | 🟡 | Not multiplication bottlenecks. | DFT over `F_p` done (`dftInTime`); division, square root and transposition not started. |

## Milestones

✅ means the whole deliverable is checked. Details are in the
[implementation plan](plan/D-sharper-bound.md) and its milestone-detail section.

| ID | Progress | Sections | Deliverable | Status |
| --- | --- | --- | --- | --- |
| M1 | ✅ | §§5, 6, 9 | Retune the existing construction. | Historical, `kappa = 2^-93`. |
| M2 | ✅ | §§4.3, 8.2, 9.3 | Direct nonadjacent CRT swaps. | Historical, `kappa = 2^-66`; the running CRT still uses it. |
| M3 | 🟡 | §5.2–5.3, App. A | Compact controls, caller integration, stopped recursion. | Compact integration complete; it is the current theorem. Stopped-recursion integration remains. |
| M4 | ⬜ | §5.4, §9.7 | Linear child-precision bound; recursive workspace and stock. | Planned. |
| M5 | 🟡 | §6.2, §4 | Balanced prefix (M5a); arbitrary-source routing (M5b). | M5a done (`CompactStageGrowth.prefix_le`). M5b open ([design](IntegerMultBounds/MathlibTM2/Balanced/DESIGN.md)). |
| M6 | 🟡 | §§3–5 | Selected finite suppliers in the machine. | T16 complex supplier and the cover-free PR97 bit supplier (rank-one children, `MathlibTM2/M8/`) done and in the proof. Variable-rank bit children and #104's opposite-bank compiler remain; groundwork (`GenericBasis`, `ReversedExchange`, `StoppedRecurrence`, the `Stage2Moments` gaps) is checked outside the root. PR589 bit side checked under upstream's idealization (`M6/Bit*`, outside the root); it does not run on this machine ([design](IntegerMultBounds/MathlibTM2/M6/DESIGN.md)). |
| M7 | 🟡 | §§8, 9.2, 9.7 | Faster rounded Gaussian inverse, prime supply, bulk execution. | Prime supply done (`primes_in_window`, `primeSrc_good`). Rounded inverse composed (`rounded_inverse`); chirped forward map approximated (`chirpA_approx`). Tape costs and bulk core/halo execution remain ([design](IntegerMultBounds/MathlibTM2/NearOne/DESIGN.md)). |
| M8 | ⬜ | §9.1–9.8 | Bootstrap stages linked to all 47 target inequalities. | Planned. Goal: saving `0.001672660197076918`. |

## Next steps

1. **A bit supplier with a larger saving.** It is the only lever beyond `2^-18.0`. Stage 2 of the
   PR97 note: variable-rank block children over atoms, then #104's opposite-bank compiler on plain
   frames (`a* = 9.69e-5`, about `2^-14.6`).
2. **Near-one dimensions** (one bit with today's suppliers): the rest of M7, M5b and the bulk
   exposure transfer.
3. **M3 stopped recursion and M4.** M8 needs them; they do not change `kappa` today.

The bootstrap base saving `0.0000384599` must itself be proved or replaced by a sufficiently
strong proved base; our current theorem does not supply it. After each integration, record the
achieved saving, the binding margin and its manuscript section.

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
