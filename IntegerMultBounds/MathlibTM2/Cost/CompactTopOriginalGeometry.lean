module
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopRows
import IntegerMultBounds.MathlibTM2.Fast.SynRecB
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
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
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal


/-! Pay unary row padding from actual selected address bits. The reserved row
axes bound the divisor, and three further address bits pay the division budget. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.LayerMachine
noncomputable section

theorem compactUnaryPaddingBudget_volume (x k R₂ n rw : ℕ)
    (hx : 1≤x) (hk : k≤x) (hrows : x≤R₂)
    (hbits : 4*(k+1)≤2^n) (hrw : 1≤rw) :
    (x+k+1)*(k+1)≤R₂*2^n*rw := by
  calc
    (x+k+1)*(k+1)≤(4*x)*(k+1) := Nat.mul_le_mul_right _ (by omega)
    _ = x*(4*(k+1)) := by ring
    _ ≤ x*2^n := Nat.mul_le_mul_left _ hbits
    _ ≤ R₂*2^n := Nat.mul_le_mul_right _ hrows
    _ ≤ R₂*2^n*rw := Nat.le_mul_of_pos_right _ (by omega)

/-- Actual reserved row axes suffice to charge the numerator/divisor work to
the padded stream, provided the remaining address has three further bits. -/
theorem compactTopOriginal_division_volume (d K R a n r w : ℕ)
    (hK : 0<K) (hR : 0<R) (hr : 0<r) (hw : 0<w)
    (ha : CompactGlobalRowPadding.rowAxes NW m d*K≤a)
    (hn : CompactGlobalRowPadding.rowAxes NW m d*K+3≤n) :
    (2^a*R+NW^CompactGlobalRowPadding.depth m d+1)*
      (NW^CompactGlobalRowPadding.depth m d+1)≤compactTopRows d R a*2^n*(r*w) := by
  let k := NW^CompactGlobalRowPadding.depth m d
  have hk : 1≤k := pow_pos NW_pos _
  have hdiv := CompactGlobalRowPadding.divisor_le_original NW m d K hK
  change k≤2^(CompactGlobalRowPadding.rowAxes NW m d*K) at hdiv
  have hpower := Nat.pow_le_pow_right (by decide : 0<2) hn
  have h8 : 8*k≤2^n := calc
    8*k≤8*2^(CompactGlobalRowPadding.rowAxes NW m d*K) := Nat.mul_le_mul_left _ hdiv
    _ = 2^(CompactGlobalRowPadding.rowAxes NW m d*K+3) := by rw [pow_add]; ring
    _ ≤ 2^n := hpower
  have hstock : k≤2^a*R := by
    simpa only [Nat.mul_comm] using compactTopRows_divisor_le hK hR ha
  have hrows : 2^a*R≤compactTopRows d R a := by
    simpa only [Nat.mul_comm] using (compactTopRows_bounds hK hR ha).1
  exact compactUnaryPaddingBudget_volume (2^a*R) k (compactTopRows d R a) n (r*w)
    (Nat.mul_pos (pow_pos (by decide : 0<2) a) hR) hstock hrows (by omega)
    (Nat.mul_pos hr hw)

end
end IntegerMultBounds.MathlibTM2.Cost
