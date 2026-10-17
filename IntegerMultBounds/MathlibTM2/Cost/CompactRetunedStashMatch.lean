module

import IntegerMultBounds.MathlibTM2.Fast.DistSynCost
public import IntegerMultBounds.MathlibTM2.Fast.CompactDistWires
import IntegerMultBounds.MathlibTM2.Cost.MatchBase
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Actual retuned round costs: compact bulk and explicit direct boundary rounds. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Mult.Sizes
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.ConvSt
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node Filter Mult.SynthErr
noncomputable section

theorem compactRetuned_stash_le : ∀ᶠ n in atTop,
    synStashCostW (compactDsyV₀ n) synXS ≤ 2 * r n + 800 * (b n + 1) ^ 2 := by
  filter_upwards [eventually_big] with n hbig
  have hn := hbig.1
  have H := compactDs_layHyp hbig
  dsimp only [dsyEs] at H
  obtain ⟨hN, hℓ, hK, hD, hw, -⟩ := dsy_sizes hbig
  have hK : Mult.CompactSizes.K n≤b n+2 := ((Mult.CompactSizes.K_le_d n).trans (mt_d_le_b n)).trans (Nat.le_add_right _ _)
  have hb : layB (ℓ n) (Mult.CompactSizes.K n) ≤ ℓ n := le_trans (Nat.mod_le _ _) (Nat.sub_le _ _)
  have hLg : (layLongs (List.ofFn (cvAx (t n))) (ℓ n)).length ≤ (List.ofFn (cvAx (t n))).sum := by
    have := lay_sum H; omega
  have hrec := dsy_length_topRec_le (A := bdA) H
  have hpos := dsy_length_twPosReg (A := bdA) (List.ofFn (cvAx (t n))).sum
    (twPosL (layPerm (List.ofFn (cvAx (t n))) (ℓ n) (Mult.CompactSizes.K n))) (fun k hk => (twPosL_lt _ k hk).le)
  have hnr := dsy_nRounds_le n
  simp only [synXS, synStashCostW, compactDsyV₀, dsyEs, List.length_replicate, List.length_nil]
  rw [hpos]
  simp only [dsyEs] at hN hD
  set M := b n + 2 with hM
  have hM1 : M ≤ 2 * (b n + 1) := by omega
  have hM : M * M ≤ 4 * (b n + 1) ^ 2 := by
    calc M * M ≤ (2 * (b n + 1)) * (2 * (b n + 1)) := Nat.mul_le_mul hM1 hM1
      _ = 4 * (b n + 1) ^ 2 := by ring
  have hM' : M ≤ 4 * (b n + 1) ^ 2 := by nlinarith
  have hNN : (List.ofFn (cvAx (t n))).sum * (List.ofFn (cvAx (t n))).sum ≤ 4 * (b n + 1) ^ 2 :=
    le_trans (Nat.mul_le_mul hN hN) hM
  have hDℓ : (List.ofFn (cvAx (t n))).length * (ℓ n + 1) ≤ 8 * (b n + 1) ^ 2 := by
    calc (List.ofFn (cvAx (t n))).length * (ℓ n + 1) ≤ M * (M + 1) :=
          Nat.mul_le_mul hD (by omega)
      _ ≤ M * (2 * M) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (M * M) := by ring
      _ ≤ 8 * (b n + 1) ^ 2 := by omega
  omega

theorem compactRetuned_finStash : ∀ᶠ n in atTop,
    synStashCostW (compactDsyV₀ n) synXS + 6*nRounds (cvAx (t n))+6≤806*(r n+(b n+1)^2) := by
  filter_upwards [compactRetuned_stash_le,eventually_big] with n hs hbig
  have h1 := dsy_nRounds_le n
  have h2 := mt_ℓ_le_b hbig
  have h3 : b n+1≤(b n+1)^2 := by
    rw [pow_two]; exact Nat.le_mul_of_pos_right _ (by omega)
  omega

end
end IntegerMultBounds.MathlibTM2.Cost
