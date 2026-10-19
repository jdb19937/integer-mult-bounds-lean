module

import IntegerMultBounds.MathlibTM2.Cost.CRTControl
import IntegerMultBounds.MathlibTM2.Fast.CRTControlScan
public import IntegerMultBounds.MathlibTM2.Fast.CRTControl
public import IntegerMultBounds.MathlibTM2.Fast.TableVM
public import IntegerMultBounds.MathlibTM2.Mult.Sizes
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Absorbing the executable CRT descriptor scan cost

The budget below is the actual scanner contract, including four-word loading,
thirteen table-interpreter atoms per descriptor, loop tests, and descriptor
tape restoration. A descriptor count at most `L` and binary word width at
most `3*L+1` give a cubic polynomial. The pipeline fiber bound absorbs this
cost over every axis into `2^19*T` eventually.

Unary offset materialization and data rotation are not included here.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter
  IntegerMultBounds.MathlibTM2.Fast TableVM

/-- The explicit bound of `crtControlScan_runs` with the concrete packet
loader and thirteen-atom arithmetic kernel. -/
def crtControlScanCost (len W w : ℕ) : ℕ :=
  len * ((48 * W + 56 + 13 * tblC W w) + 2) + 2 + (8 * len * W + 2)

/-- The actual descriptor scan budget is bounded by a cubic in total address
width. This includes the empty descriptor list and zero address width. -/
theorem crtControlScanCost_le_polynomial {len L W w : ℕ}
    (hlen : len ≤ L) (hW : W ≤ 3 * L + 1) (hw : w ≤ W) :
    crtControlScanCost len W w ≤ 2 ^ 15 * (L + 1) ^ 3 := by
  have hwidth : W + 4 ≤ 5 * (L + 1) := by omega
  have hpow : (W + 4) ^ 2 ≤ 25 * (L + 1) ^ 2 := by
    calc
      (W + 4) ^ 2 ≤ (5 * (L + 1)) ^ 2 := Nat.pow_le_pow_left hwidth 2
      _ = 25 * (L + 1) ^ 2 := by ring
  have hmono : 2 ^ 10 * len * (W + 4) ^ 2 ≤
      2 ^ 10 * (L + 1) * (25 * (L + 1) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (hlen.trans (Nat.le_succ L))) hpow
  have hcube : 1 ≤ (L + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  calc
    crtControlScanCost len W w ≤ 2 ^ 10 * len * (W + 4) ^ 2 + 4 :=
      crtControlScan_cost_le len W w hw
    _ ≤ 2 ^ 10 * (L + 1) * (25 * (L + 1) ^ 2) + 4 := Nat.add_le_add_right hmono 4
    _ = 25600 * (L + 1) ^ 3 + 4 := by ring
    _ ≤ 2 ^ 15 * (L + 1) ^ 3 := by norm_num; omega

/-- Uniform pipeline bound for the executable descriptor scan, including
restoration, once on every fiber of every axis. Descriptor counts and binary
widths may differ by axis. -/
theorem crtControlScanCost_pipeline_le :
    ∀ᶠ n in atTop, ∀ a len W w : Fin (d n) → ℕ,
      (∀ i, a i ≤ logT n) →
      (∀ i, a i = ℓ n ∨ a i = ℓ n - 1) →
      (∀ i, len i ≤ logT n) → (∀ i, W i ≤ 3 * logT n + 1) →
      (∀ i, w i ≤ W i) →
      (∑ i, 2 ^ (logT n - a i) * crtControlScanCost (len i) (W i) (w i)) ≤
        2 ^ 19 * T n := by
  filter_upwards [crtControl_polynomial_pipeline_le (2 ^ 15) 3] with n h a len W w ha hw hlen hW hn
  have hcost := h a (fun i => crtControlScanCost (len i) (W i) (w i)) ha hw
    (fun i => crtControlScanCost_le_polynomial (hlen i) (hW i) (hn i))
  exact hcost

/-- One descriptor per physical axis; positive axis widths bound the
number of descriptors by the address width of that physical prefix. -/
theorem crtControlFields_length_le_width {d : ℕ} (a s : Fin d → ℕ) (i : ℕ)
    (pre : List (Fin d)) (hpos : ∀ j ∈ pre, 1 ≤ a j) :
    (crtControlFields a s i pre).length ≤ crtW a pre := by
  induction pre with
  | nil => simp [crtControlFields]
  | cons j pre ih =>
    have hj := hpos j (by simp)
    have ht := ih (fun k hk => hpos k (by simp [hk]))
    simp only [crtControlFields, List.length_cons, crtW_cons]
    omega

/-- Positive widths and a prefix-address bound discharge the descriptor
count hypothesis in the concrete polynomial scan estimate. -/
theorem crtControlFields_scanCost_le_polynomial {d L W w : ℕ}
    (a s : Fin d → ℕ) (i : ℕ) (pre : List (Fin d))
    (hpos : ∀ j ∈ pre, 1 ≤ a j) (hpre : crtW a pre ≤ L)
    (hW : W ≤ 3 * L + 1) (hw : w ≤ W) :
    crtControlScanCost (crtControlFields a s i pre).length W w ≤ 2 ^ 15 * (L + 1) ^ 3 :=
  crtControlScanCost_le_polynomial ((crtControlFields_length_le_width a s i pre hpos).trans hpre)
    hW hw

end IntegerMultBounds.MathlibTM2.Cost
