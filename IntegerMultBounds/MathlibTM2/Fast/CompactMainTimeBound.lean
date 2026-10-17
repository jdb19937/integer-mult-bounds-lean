module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainTimeGlue
import IntegerMultBounds.MathlibTM2.Cost.MatchBase
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Fixed normalization overhead and the final asymptotic bridge for compact main costs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.MathlibTM2 Filter Asymptotics
open IntegerMultBounds.MathlibTM2.Cost IntegerMultBounds.MathlibTM2.Mult.Sizes
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

/-- The unchanged main stages absorb any fixed number of normalization steps. -/
theorem compactMain_runs_add_const {runs : ℕ → ℕ} {Cr : ℝ}
    (hR : ∀ᶠ n in atTop, (runs n : ℝ) ≤
      Cr * (totDirectCRT n + totResamp n + CompactTotal.conv n +
        (T n : ℝ) * totMp n + (T n : ℝ) * p n)) (extra : ℕ) :
    ∀ᶠ n in atTop, ((runs n + extra : ℕ) : ℝ) ≤
      (Cr + extra) * (totDirectCRT n + totResamp n + CompactTotal.conv n +
        (T n : ℝ) * totMp n + (T n : ℝ) * p n) := by
  filter_upwards [hR, eventually_big] with n hn h
  have hcrt := mt_directCRT_nonneg n
  have hres := mt_resamp_nonneg n
  have hconv := CompactTotal.conv_nonneg h
  have hmp := mt_Tmp_nonneg n
  have hp : 1 ≤ p n := by have := h.sixteen_le_b; unfold p; omega
  have hT : 1 ≤ T n := by
    have := h.S_lt_T
    omega
  have hTp : (1 : ℝ) ≤ (T n : ℝ) * p n := by exact_mod_cast (show 1 ≤ T n * p n from (Nat.mul_le_mul hT hp))
  have hsum : (1 : ℝ) ≤ totDirectCRT n + totResamp n + CompactTotal.conv n +
      (T n : ℝ) * totMp n + (T n : ℝ) * p n := by linarith
  have he := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg extra : (0 : ℝ) ≤ extra)
  push_cast
  nlinarith

/-- Conditional only on the actual source-cost match; includes expanded-host cleanup. -/
theorem compactMain_time_isBigO {K : ℕ} {Lb : LProc → MnPr (prime + K)} {w : ℕ → ℕ}
    {σ : ℕ → LReg SXReg → List (Fin (prime + K + 4))} (D : MnDist K Lb w σ)
    (runs : ℕ → ℕ) (host c extra : ℕ) {Cr : ℝ}
    (hR : ∀ᶠ n in atTop, (runs n : ℝ) ≤
      Cr * (totDirectCRT n + totResamp n + CompactTotal.conv n +
        (T n : ℝ) * totMp n + (T n : ℝ) * p n)) :
    (fun n => (compactMainTime D (fun n => runs n + extra) host c n : ℝ)) =O[atTop]
      fun n : ℕ => (n : ℝ) * Real.log n ^ (1 - CompactTotal.kappa) := by
  obtain ⟨C, hC⟩ := compactMain_time_le_of_runs D (fun n => runs n + extra) host c
    (compactMain_runs_add_const hR extra)
  exact CompactTotal.htime C hC

end
end IntegerMultBounds.MathlibTM2.Fast.Main
