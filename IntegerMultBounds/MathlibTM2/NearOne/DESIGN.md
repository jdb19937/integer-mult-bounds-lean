# Near-one dimensions: what still pins ε ≤ 1/2

The selected route (plan `plan/D-sharper-bound.md`, §§8–9, M8b) runs at a dimension exponent
`ε` close to `1` (`ε = (1-η)/(1+q)`, about `0.998` at the selected witness): its binding margin
is the compact layer `εq`, so moving `ε` from `31/64` to near `1` doubles the saving for any
supplier. The moduli no longer limit `ε` (`Primes/DESIGN.md`) and the prefix margin is `1 - ε`
(`Balanced/DESIGN.md`, M5a). This note covers what remains:

* (a) the sizing, which no longer uses `d² ≤ b`;
* (b) the remaining M7 items, the faster rounded Gaussian inverse and its execution;
* (c) the exposure margin `(1 - ε)(1 - τ)`;
* (d) staged estimates.

Notation: `b = ⌈log₂ n⌉`, `p = 6b`, `d = ⌊b^ε⌋` (`d^64 ≤ b^31` at `ε = 31/64`), `ℓ ≈ b/d`
(`b ≤ 2dℓ`, `3dℓ ≤ p`), `K` the compact chunk, `a_b = 1 - τ = 296/10^11`,
`a_c = 1 - σ = 418/10^12`, `1 - λ' = 21/2^33`, `δ = 2^-7`.

## (a) The sizing without `d² ≤ b`

At `ε > 1/2` the fact `d² ≤ b` is false, and so is every fact equivalent to it: `d ≤ ℓ` means
`d² ≲ b`, since `ℓ ≈ b/d`. `Mult/Sizes.lean` no longer states either; its sizing rests on two
facts valid for every `ε < 1`, `d^64 ≤ b^31` (`d_pow_le`) and `b^33 ≤ (2ℓ)^64` (`b_pow_le_ℓ`,
from `b ≤ 2dℓ`), and on the regime facts below.

**The regime.** `Big n : 2 ≤ n ∧ 2^192 + bigDim ≤ d n`. `bigDim` is `d` at the threshold of the
eventual bundle `BigFacts` plus one, so `d` monotone (`d_mono`) turns every bundled eventual fact
into a deterministic `Big.*` fact (`bigFacts_of_bigDim_le`). The bundle:

| fact | statement | consumers |
| --- | --- | --- |
| prime supply | `PrimeSupply n` (including `4 ≤ ℓ`) | `Big.good`, `Big.srcLen_eq`, `Big.four_le_ℓ`, `Big.two_le_ℓ` |
| chunk room | `2^8 d^7 < ℓ^8` (`Big.chunk_room`) | `CompactSizes.two_Kroot_lt_ℓ`, hence `K_eq_unif`, `mod_K_succ_le`, `K_succ_le_ℓ`; `Big.K_succ_le_ℓ` for the legacy chunk |
| Gaussian width room | `64 d (⌈log₂ p⌉ + 3) ≤ b` | `Big.sixteen_d_alpha_sq_le_b` (through `α² < 4u`), `Big.four_gamma_le_b`, `Big.gamma_le_real`, `Big.band_budget`, `SmallGapSizes.uSG_mul_d_le` |
| dimension below the axis | `d ≤ 2^(ℓ-1)` (`Big.d_le_two_pow_pred_ℓ`) | `DistWidth.ds_d_le_r`, `ds_d_mul_r_le`, `ds_lay_widths`, `DistCost.ds_sum_t`, `DistCostSrc.ds_r_le_T` |
| precision below the axis | `8p ≤ r` (`Big.eight_p_le_r`) | `PrepA.pre_p_le_s` |

Facts that follow without the bundle: `d ≤ b` (`d_le_b`), `F d ≤ b` for `F^64 ≤ b^33`
(`mul_d_le_b`; `Big.eight_d_le_b`, `CompactCallerOverheadR.compactCallerR_eventually_width`),
`ℓ → ∞` (`tendsto_ℓ`), `p^C ≤ r` eventually (`eventually_pow_p_le_r`, hence
`MatchSynPipe.mr_b_pow_le_r`), the prime supply with `d^33 ≤ (2ℓ)^31 ≤ (ℓ - 1)^62`.

The exponent sum of the compact caller's reservation pieces is at most `D (m + G)`
(`synE_zero_le_radix`: the lowest base-`m` digit is below `m`, every other level scale is `G`), so
the working width needs only `(cG + G + m + 30) d ≤ b`.

**What stays tied to the exponents.**

* The proofs of the bundle (`eventually_chunk_room`, `eventually_gauss_room`, the prime supply's
  `B = 2`) and of `b_pow_le_ℓ`, `d_pow_le_ℓ` use the numbers `64`, `31`, `33`. For `ε = N/M` they
  become `d^M ≤ b^N`, `b^(M-N) ≤ (2ℓ)^M`, with the same structure.
* The chunk room encodes the chunk exponent `7/8`: it holds eventually exactly when
  `(7/8) ε < 1 - ε`, i.e. `ε < 8/15`. Near one the chunk exponent `c` must satisfy
  `εc < 1 - ε`; with `c → 0` the chunk exchanges cost `ε c a_b`, which makes M5b's routing
  (margin `a_b`) necessary (`Balanced/DESIGN.md`).
* `b_lt_d_succ_pow` (`b < (d+1)^8`, needs `ε ≥ 1/8`) and its users `Big.alphaU_le_d`, `clog_p_le`,
  `CompactCallerGuardPower` (`cExp · upperPower`).
* The machine computes `d = iroot 64 (b^31)`: `ParamProg.pm_s3`,
  `Fast/CompactDyadicParamStageCore.lean`, `Fast/CompactDyadicDimension.lean`,
  `Mult/CompactDyadicRootRoom.lean`.
* `DistWidth.parameter_width_small_r` uses `d^64 ≤ b^31` numerically for `b ≤ 2 → d = 1`.
* The real-exponent envelopes (`CompactStageGrowth`, `CompactInterim`) rewrite with
  `epsilon_eq`.

## (b) M7: the faster Gaussian inverse and its execution

**Status** (`PLAN.md`, M7 row; plan §8, M7a/M7b). Kenny's last substantive M7 commit is
`8b9f9194` (2026-10-16 18:14, "Small Gaussian width"). Remaining, quoted from the plan: "Rounded
boundary factorization, boundary ordering, tape costs and bulk execution remain; these must remove
the Gaussian restriction and support near-one dimensions."

**Checked pieces on the main route** (they serve the banded `B̃₀` of the present multiplier,
`Mult/BandSpec`, `ConcreteB0`, `Fast/BandFits`): `NLogN/PhaseCellFactorization`
(`smallgap_factorization`), `PhaseCellMatrix`, `PhaseCellOperator` (operator error `2^(-45p)`),
`PhaseCellSharpInverse` (inverses `4p`, rounded `8p`), `PhaseCellBoundary` (margin `1/(8p)`),
`PhaseCellBandSolve`, `PhaseCellFold`, `PhaseCellFoldSolve`, `PhaseCellPerturb`,
`PhaseCellMachMatrix`, and the `Schur*`, `Row*`, `Band`, `Tail*`, `Scan`, `Intervals` support.

**Checked pieces of the phase-cell inverse, off the main route:**

* `ToeplitzInverse` (`gohberg_semencul`), `ToeplitzDominant`, `PhaseCellToeplitz`
  (`block_inverse`), `ToeplitzApply`, `ToeplitzRounded` (`rounded_apply`), `ToeplitzScaled`;
* `PhaseCellInteriorSolve` (`cell_solve`), `PhaseCellRoundedCell`, `PhaseCellInteriorCover`,
  `PhaseCellWeightRange`;
* `SchurIdentify` (`schurOp_eq_run`), `SchurBlockSolve` (`four_step`), `SchurBlockError`,
  `PhaseCellBoundaryLU` (`rounded_boundary`).

`PhaseCellFourStep` and `PhaseCellBandFill` are imported by no module and not by the root, so the
default build does not check them.

**The remaining items and what each builds on:**

1. **Rounded boundary factorization** (`NLogN/SchurPerturbSolve.lean`,
   `PhaseCellRoundedSchur.lean`, `PhaseCellRoundedInterior.lean`, `PhaseCellRoundedInverse.lean`).
   The reduced boundary matrix has the Schur complement entries `A_ij - A_iI R(A_Ij)`
   (`run_entry`). The computed boundary matrix takes these entries on a band containing the
   support of the exact one from computed interior responses within `eR`, with one rounding
   `η`, and is zero elsewhere; each row is within `|B| (η + eR)` of the exact one (`rounded_schur_rows`). The
   machine-faithful solve `bandSolveG` of a computed matrix within row mass `ε` of a dominant
   one adds `ε` to the backward error of the factors (`bandSolveG_perturbed_error`), so the
   boundary values are within `e₃ = 2^16 p³ N (N η + eR + θ) (1 + ρ)` of the exact Schur
   solution for `N ≥ |B|` and `2^13 p² N (N η + eR + θ) ≤ 1` (`rounded_schur_solve`, in any
   elimination order); the backward route needs no forward bounds on the factors, so the factor
   hypotheses of `rounded_boundary` are not used. Valid rounded cell runs on every cell
   interval give the interior errors `η + 64 s η V + 2(η + C η)` (`rounded_interior`, from
   `rounded_cell` and `interior_cover`), and `rounded_inverse` composes the five stages through
   `rounded_four_step`: boundary values within `e₃ + 8p (e₁ + e₂)`, interior values within
   `e₅ + 8p (e₄ + e₃ + 8p (e₁ + e₂))`, with `ρ = (1 + 8p) β + e₁ + e₂` for `|b| ≤ β`.
2. **Boundary ordering** (`NLogN/PhaseCellBoundaryOrder.lean`). The boundary `univ \ I` has at
   most `2w (t - s + 1)` vertices (`boundary_card`: a non-interior vertex lies within `w` of an
   array end or of one of the at most `t - s` cell starts). In physical rank order every coupling
   of the boundary system lies in the bordered band `RankRel B (4w)`: ranks within `4w`, or a
   vertex among the last `4w` ranks for the wrap-around entries (`schur_rankRel`). The band is
   closed under fill, so every exact or rounded LU factor entry in that order stays in it
   (`boundary_factors`, `boundary_factors_r`), and a row outside the last `4w` ranks meets at most
   `12w + 1` boundary vertices (`rankRel_row_card`).
3. **Tape costs.** The phase-cell line replaces the banded line of `B̃₀`. It plugs into the
   existing interface `Mult/ConcreteB0.concrete_resampB₀_specX`: any real line solver of
   `realMatrix` within `e` on right-hand sides at most `1/2` gives the pipeline interface of
   `B̃₀`. Its per-line cost is `O(t p^(1+δ) (1 + w²/d))` against the banded line's
   `O(t w p^(1+δ))` (source: `downstream-phase-cell-inverse.md` of the pinned CrocSwap
   references), which turns the tensor exponent `ε + δ + (1 - r)/2` into
   `max(ε + δ, 1 - r + δ)`. Three parts:
   * **b3a, the concrete solve** (math only; `NLogN/PhaseCellBoundaryFold.lean`,
     `PhaseCellConcreteInterior.lean`, `PhaseCellConcreteSolve.lean`). The boundary system is a
     cyclic band of half width `4w` in boundary rank (`schur_cycRel`); the folded boundary order
     `bFoldOrder` makes it a plain band of half width `8w + 1` closed under fill
     (`cycRel_foldBRel`, `boundary_factors_fold`), the format of `Fast/BandLine`. The cell
     interval of an interior vertex runs between the extreme interior vertices of its cell
     (`cell_interval`); the concrete cell runs round every stage once (`cellRunOf`, valid by
     `cellRunOf_valid`, scaled inputs at most `(C + 1) 2^(8p+2)` since the similarity weights lie
     in `[2^-(8p+1), 1]`), and `pcInterior_error` bounds the interior solve. `pcSolve` composes
     the cell runs, the two rounded couplings, the machine solve `bandSolveG` with the rules
     `machMul`, `newtonR` (Newton at `β = 1/(32p)`) of the computed boundary matrix in folded
     order, and the recovery; it is within `2^(8p+46) p⁷ s² η` of the exact solution for
     `|b| ≤ 1/2` and `2^(8p+46) p⁷ s² η ≤ 1/2` (`pcSolve_error`). Remaining: the `B̃₀` interface
     through `concrete_resampB₀_specX`, and the precision `P ≥ 9p + 46 + 7 log₂ p + 2 log₂ s`
     in place of the banded line's `5p`.
   * **b3b, the machines.** A per-axis loader (the `prep` of the generic driver `rsbAllG`):
     cell and boundary masks from the phase generator (`PhaseCellScan`), reciprocal weights,
     Gohberg–Semencul generators per cell length, coupling tables, the computed boundary matrix
     and its folded factor tables by the existing factor machine (`Fast/BandFactor`). A line
     machine: split the line into cells, per cell four triangular Toeplitz products as negacyclic
     products of size at least `2L` on the vendored ring product (`Fast/RingProd`), the coupling
     scans, the boundary solve by the passes of `Fast/BandLine` on the boundary records, the
     second interior pass, and the merge.
   * **b3c, the costs.** The line cost `O(t p^(1+δ) (1 + w²/d))` plus a polynomial setup per
     axis, matched into `rsbAllCostG` as `Cost/MatchBandB.lean` does for the banded line.
4. **Bulk execution (M7b).** Ordered core/halo windows of the same rounded matrix
   (core `L = 2^⌈8 log₂ p⌉`, halo `A = 4096 p³`, Neumann depth `J = 512 p²`, locality error
   below `2^(-16p)`), period cuts kept in every window, tensor errors in row norm without a volume
   factor, then the tape transfer: source halos fit `L ≥ 64 d A`, target halos of total volume
   below `2T`, alternating overlap tapes, factor-page reuse, cropping after each axis, final
   prime-box order. Nothing exists yet.
5. **The forward map.** `totResamp` charges the `Ã` window of `2m + 1 ≤ 4α√p` lines per
   output (`Cost/MatchResampA.lean`); with `α² ≍ p^r` this grows with `r`. The selected route
   replaces it by a chirped-correlation forward map in `O(M(p))` per output (plan, the cap
   paragraph). Without it the Gaussian margin stays below `1/2 - ε`.
6. **Integration.** `Fast/ResampA*`, `Fast/ResampB*`, `Mult/Sizes`, `Cost/MatchResampA`,
   `Cost/MatchResampB`; the Gaussian conjunct of `exp_facts`
   (`ε + ε c₀/2 + (1/2 + δ) ≤ 1 - κ`, from `totResamp = d T √p α M(p)`) becomes
   `min(1 - ε - δ, r - δ)` with `α² ≍ p^r`, `ε + r < 1`, `ε > (1 - r)/2`. The `√p α` window of
   `Ã` is the bottleneck of `totResamp`; the banded `B̃₀` is overcharged by about `α²`.

## (c) The exposure margin

**Where it comes from.** `exp_facts`' conjunct `ε(1-τ) + τ ≤ 1 - κ`, i.e.
`κ ≤ (1 - ε)(1 - τ)`, pays `totDirectCRT = T p d (1 + ℓ^τ)` (`Cost/DirectScale.lean`) through
`d ℓ^τ = d^(1-τ) (dℓ)^τ ≤ 2 b^(ε(1-τ)+τ)` (`Cost/DirectGrowth.lean`). The charge is `d`
exposures of an `ℓ`-bit axis field at `ℓ^τ` each:

* the direct CRT routing with distant exposure (`Cost/CRTDirectFull`, `CRTDirectMachine`,
  `CRTControlTarget`);
* the `2(d - 1)` last-axis interchanges of `Ã` (`Cost/MatchResampA.lean`) and of the banded
  `B̃₀` (`Cost/MatchBandB.lean`, `mt_band_stage_le_linear`).

At `ε → 1` it tends to zero.

**What delivers the margin `a_b`.** The selected bulk tape transfer
(`notes/structured-bulk-assembly.tex` of the pinned CrocSwap revision, "Bulk locality and fixed
tapes") costs `O(Tp [p^τ polylog p + d polylog p + d p^δ + w² p^δ + d w² p^δ / L]) + n^(o(1))`.
Its exposure moves one short field at a time with temporary binary padding, so the movement
costs `p^τ polylog p` once for all axes. It needs:

* M7b's core/halo windows (item 4 above), which make every axis a short field;
* M5b's arbitrary-source coordinate routing (`Balanced/DESIGN.md`, cost `V p^τ polylog p`) for the
  field movement;
* the direct CRT routing, kept as it is.

The other terms are `d polylog p` (margin `1 - ε`) and `p^δ` terms (margins `1 - ε - δ` and
`r - δ`).

**Which margins bind near one.**

| margin | today, `ε = 31/64` | today's suppliers, `ε → 1` | selected suppliers |
| --- | --- | --- | --- |
| compact layer `ε(1 - λ')` | `1.18·10^-9` (binds) | `→ 2.44·10^-9` | `ε q`, binds (`g`) |
| chunk exchanges `ε c a_b` | `1.25·10^-9` | `≤ (1 - ε) a_b` without M5b; `a_b` with M5b | `a_b` |
| exposure | `(1 - ε) a_b = 1.53·10^-9` | `→ 0`; `a_b` with bulk exposure | `a_b` |
| Gaussian | `1/2 - δ - ε - εc₀/2 = 7.8·10^-3` | `min(1 - ε - δ, r - δ)` with M7 | same |
| prefix | `1 - ε = 0.52` (M5a) | `1 - ε` | `1 - ε(1 + c)` or `1 - ε` |
| scalar, dimension | `1 - ε - δ`, `ε` | same | same |

With today's suppliers the near-one route is worth about one bit: the layer margin goes from
`ε(1 - λ') = 2^-29.65` to `(1 - λ') ε` at `ε ≈ 0.99`, about `2^-28.6`, provided M7, the bulk
exposure, M5b and (a) are in place. Without M5b and bulk exposure the best compromise is
`ε ≈ a_b/(a_b + 1 - λ') ≈ 0.55`, worth about `0.2` bits. With the selected suppliers the
selected assembly has all seven margins at or above `g = εq`: about `1.25·10^-5` (`2^-16.3`)
in `notes/structured-bulk-assembly.tex`, and `a/(1 + a)` with the bootstrapped `a` of M8
(`2^-9.2`), against `ε c a ≈ 2^-10.4` on the present layout.

## (d) Staged estimates

Conservative, agent time, on the shared lock and the 24 GB machine.

| stage | content | lines | time |
| --- | --- | --- | --- |
| a1 | `Big` from the eventual bundle `BigFacts`; `d_le_b`, `b_pow_le_ℓ`, `mul_d_le_b` | 350 | done |
| a2 | consumers of `d ≤ ℓ`, `d ≤ 2ℓ`, `b ≤ 4ℓ²`, `F d² ≤ b` (the `Dist*` width lemmas now take `Big`) | 200 changed | done |
| a3 | Gaussian and small-gap widths from the width room | 60 | done |
| a4 | the `synE` exponent sum, linear in `D` | 40 | done |
| a5 | the chunk exponent as a parameter with `εc < 1 - ε` | 150–300 | 3–6 days |
| a6 | the machine dimension `iroot M (b^N)`, its root rooms, and the exponent arithmetic of the bundle for a general `ε = N/M` | 600–1200 | 2–3 weeks |
| b1 | rounded boundary factorization | 668 | done |
| b2 | boundary ordering | 457 | done |
| b3 | tape machines and costs for the inverse: b3a concrete solve, b3b machines, b3c costs | 1k + 5–9k + 1–2k | 3–5 months |
| b4 | bulk core/halo execution and tape transfer (M7b) | 6–12k | 3–6 months |
| b5 | the chirped-correlation forward map for `Ã` | 2–4k | 1–2 months |
| b6 | integration into `ResampA/B`, `MatchResampA/B`, the Gaussian conjunct | 2–4k | 1–2 months |
| c | bulk exposure on b4 and M5b (M5b: 9–15k, 3–5 months, `Balanced/DESIGN.md`) | 1–2k beyond b4 and M5b | 3–6 weeks |
| r | the retune to a near-one `ε` | 1–2k | 2–4 weeks |

a1–a4 are done: no proof uses `d² ≤ b`. a5 and a6 belong to the retune. (b), (c) and M5b are
the bulk of the work, about a year of agent time together.
