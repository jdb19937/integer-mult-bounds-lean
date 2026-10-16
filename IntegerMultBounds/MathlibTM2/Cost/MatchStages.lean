module

public import IntegerMultBounds.MathlibTM2.Cost.MatchParam
public import IntegerMultBounds.MathlibTM2.Cost.MatchCRT
public import IntegerMultBounds.MathlibTM2.Cost.MatchResampA
public import IntegerMultBounds.MathlibTM2.Cost.MatchResampB
public import IntegerMultBounds.MathlibTM2.Cost.MatchChirp
public import IntegerMultBounds.MathlibTM2.Cost.MatchConv
public import IntegerMultBounds.MathlibTM2.Cost.MatchRound
public import IntegerMultBounds.MathlibTM2.Cost.MatchLayout

/-!
# Cost matching of the stage machines against `totBound`

Each finished stage machine of the fast multiplier has an eventual bound
`∀ᶠ n in atTop, cost ≤ C · term n` against terms of `Cost/Total.totBound`, with `C` depending
only on the fixed constants: the stack count `Tm` of the host, the interchange bank size `t₀`,
the alphabet, the vendored constants (`swapConst`, `costC cA cB cC0`, `ssMulConst`) and the width
ratios `w ≤ cw p` (coefficients), `W ≤ cW p` (table words), `m ≤ cm p` (rounding operands).
`Cost/MatchBase` holds the shared comparisons (`mt_poly_r_le_T`: `A b^k r ≤ T` eventually;
`mt_cmul_le`: one product at width `w` is `O(M(p))`; `mt_swap_le`: the vendored interchange).

| stage | machine theorem | matching theorem | term |
|---|---|---|---|
| F1 input | `readInput_exec` | `mt_input_le` | `n` |
| F2 parameters | `pmParams_exec` | `mt_pm_stage_le` | `n + B^C` (`C ≥ 4`) |
| F3 digits | `digitRecords_exec` | `mt_digit_le` | `n` |
| F4, F9 CRT | `crtForward_runs`, `crtInverse_runs` | `mt_crt_le`, `mt_crt_le_pre` | `totCRT` |
| `Ã` with loader | `rsaStage_exec` | `mt_rsa_stage_le` | `totResamp + totCRT + T p` |
| `B̃₀` with loader | `bandStage_exec` | `mt_band_stage_le_linear` | `totResamp + totDirectCRT + T p` |
| chirp kernel | `ldChirpStage_exec` | `mt_ch_kernel_le` | `T M(p)` |
| chirp products, twists | `cst_chirpMulKeep_runs` | `mt_ch_chirpMul_le` | `T M(p)` |
| conjugation, `× 2^γ` | `cst_conj_runs`, `cst_conjKeep_runs`, `cst_scale_runs` | `mt_ch_conj_le`, `mt_ch_conjKeep_le`, `mt_ch_scale_le` | `T p` |
| convolution box (`cF = cO = 0`) | `cvBox_convBox` | `mt_cv_box_le`, `mt_cv_box_le_conv` | `T M(p) + T p grLogLog (r p)` |
| layout `L` | `ldLayGenStage_exec` | `mt_lay_stage_le`, `mt_lay_stage_le_conv` | `T p (d K + p K^{τ-1})` |
| F7 pointwise | `cst_point_runs` | `mt_ch_point_le` | `T M(p)` |
| F10 rounding | `roundStage_exec`, `rndSquare_exec` | `mt_rnd_stage_le`, `mt_rnd_square_le` | `S M(p)` |
| F11 carries, output | `carryOut_exec` | `mt_carry_le` | `n` |

Terms beyond the intended ones:

* The resamplings `Ã`, `B̃₀` interchange each axis with the last one: `2 (d - 1)` interchanges of
  volume `3 T w` at `swapConst V ℓ^τ` steps, `Θ(d T p ℓ^τ)` in all. This is not
  `O(totResamp)`: the ratio `ℓ^τ / (p^{1/2+δ} α)` grows like `B^{1/8} / d^{3/2}`
  (`ℓ ≈ B/d`, `α ≈ (12 d² B)^{1/4}`, `d ≈ B^ε`). It is at most `totCRT = T p d² (1 + ℓ^τ)`.
* The layout writer needs `(N + 1)^N < 2^W` for `N = log₂ T`, so its word size is
  `W ≳ B log B`; `mt_lay_stage_le` takes `W ≤ cW p²`. The writer costs `poly(B)` steps,
  inside `T p`.
-/

@[expose] public section

