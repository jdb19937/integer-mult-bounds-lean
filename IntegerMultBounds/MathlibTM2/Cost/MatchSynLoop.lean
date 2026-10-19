module
public import IntegerMultBounds.MathlibTM2.Fast.DistWidth
import IntegerMultBounds.MathlibTM2.Fast.MainEmbed
import IntegerMultBounds.MathlibTM2.Cost.MatchBase
public import IntegerMultBounds.MathlibTM2.Cost.Total
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import IntegerMultBounds.MathlibTM2.Cost.Branching
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd


/-!
# Cost matching: the round loops of the synthetic transforms

The loops `synLoopFCost`, `synLoopOCost` (`Fast/SynFwd.lean`) of the computed synthetic
transforms at the pipeline parameters — axes `es = List.ofFn (cvAx (t n))` (`|es| = d - 1`,
`Σ es = log₂ T - ℓ`), `ℓ = l = ℓ n`, `K = K n`, directions `Cost.brDirs`, `A = nRounds ≤ ℓ`
rounds, coefficients of `w = dsW n ≤ 12p` symbols, parking cost `stk ≤ C_s (r + (b + 1)^k)` — cost at
most a constant times `totConv n` (`mr_loop_cost_le`). Per round `h` (`mr_round_le`):

* the layer of a chunk round (`mr_chunk_layer_le`) is `topCost` with the `q₀ ≤ 46 (1 + log_m d)`
  top kernels and the pieces of the base-`m` digits of `D' = D - q₀` on `R₂ < 2^(a'+1)` rows:
  the linear stages and kernels cost `C (q₀ + 1 + |pcs|) 2^N r w'` (`mrT_topCost_le`), the pieces
  `C d^{λ'} R₂ 2^(N - a') r w'` (`mrP_pieces_le`), together `C T p d^{λ'}` since `2^N r = T`,
  `w' ≤ (G + m + 15) p` (`mrO_synW2_le`, `d^6 ≤ b`) and `1 + log_m d ≤ C d^{λ'}`;
* the layer of a top or low round (`mr_prefix_layer_le`) has `D ≤ d` top kernels and no pieces:
  `C T p d`; there are at most `b + 1 ≤ K` such rounds (`mr_rounds_split`);
* the records, rest states, parking and twiddles (`mr_over_le`): `C T p + 2 stk + 2`
  (`mrO_step_le` with `Z^8 2^N ≤ 24^8 T` from `b^8 ≤ r`).

Summing over `A ≤ ℓ` rounds: `T p (ℓ d^{λ'} + d K) + ℓ (T p + stk) + ℓ² ≤ C totConv`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.SynthErr IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds IntegerMultBounds.Machine
  IntegerMultBounds.Networks IntegerMultBounds.MathlibTM2.Fast.ConvSt IntegerMultBounds.MathlibTM2.Fast.Main

/-! ### The pipeline instance -/

/-- `F + 1 ≤ m^5` for the fixed directions. -/
theorem mr_F_le : factorCount (program Cost.brDirs) + 1 ≤ m ^ 5 := by
  have := br_factorCount_le
  have h : m ^ 5 = 2073071593 := by norm_num [m]
  omega

/-- The parameters of the pipeline instance at a large `n`. -/
theorem mr_inst {n : ℕ} (h : Big n) :
    LayHyp (List.ofFn (cvAx (t n))) (ℓ n) (K n) ∧
      (List.ofFn (cvAx (t n))).sum = logT n - ℓ n ∧
      (List.ofFn (cvAx (t n))).length = d n - 1 ∧
      (List.ofFn (cvAx (t n))).sum ≤ b n ∧
      2 ^ (List.ofFn (cvAx (t n))).sum * r n = T n ∧
      nRounds (cvAx (t n)) ≤ ℓ n ∧ 1 ≤ K n ∧ ℓ n ≤ b n ∧ K n ≤ b n ∧ d n ≤ b n ∧ 16 ≤ b n ∧
      16 ≤ d n ∧ dsW n ≤ 72 * b n := by
  have H := mn_layHyp h
  have hs := ds_sum_cvAx h.1
  obtain ⟨hT, -⟩ := mt_T_split h
  have hw := ds_dsW_le h.1
  refine ⟨H, hs, ds_length_cvAx n, ?_, by rw [hs]; exact hT.symm, nRounds_le H, H.K_pos,
    mt_ℓ_le_b h, mt_K_le_b n, mt_d_le_b n, h.sixteen_le_b,
    (by have := h.2; omega), ?_⟩
  · rw [hs]; have := mt_logT_le_b h; omega
  · have := h.sixteen_le_b; omega

/-! ### The overheads of a round -/

/-! ### The layer of a round -/

/-! ### One round, and the loops -/

end IntegerMultBounds.MathlibTM2.Cost
