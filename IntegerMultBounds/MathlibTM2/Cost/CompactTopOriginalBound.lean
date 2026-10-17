module

public import IntegerMultBounds.MathlibTM2.Fast.CompactTopOriginal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Concrete configuration construction costs. Unary division is charged to its
actual numerator times divisor; serialization and restoration are linear. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.LayerMachine
open CompactGadgetReservationCapacity
noncomputable section

theorem compactTopConfigFieldsCost_linear (W a D q E R R₂ aT Kq o : ℕ) :
    compactTopConfigFieldsCost W a D q E R R₂ aT Kq o ≤
      128*(W+a+D+q+E+R+R₂+aT+Kq+o+1) := by
  have := Nat.div_le_self (D+1) 2
  unfold compactTopConfigFieldsCost
  omega

theorem compactTopConfigWriteCost_linear (W a D q E R R₂ aT Kq o : ℕ) :
    compactTopConfigWriteCost W a D q E R R₂ aT Kq o ≤
      256*(W+a+D+q+E+R+R₂+aT+Kq+o+1) := by
  have := compactTopConfigFieldsCost_linear W a D q E R R₂ aT Kq o
  have := Nat.div_le_self (D+1) 2
  unfold compactTopConfigWriteCost
  omega

/-- Runtime ceiling division and the subsequent multiplication both pay their
actual unary operands. This includes erasing the quotient. -/
theorem compactTopConfigPaddingCost_bound (x k : ℕ) (hk : 0<k) :
    compactTopConfigPaddingCost x k ≤ 64*(x+k+1)*(k+1) := by
  have hsub : x+k-1≤x+k := Nat.sub_le _ _
  have hrem : (x+k-1)%k≤k := (Nat.mod_lt _ hk).le
  have hquot : chunks x k≤x+k := (Nat.div_le_self _ _).trans hsub
  have hmul : chunks x k*k≤x+k := by
    have h := (Compact.Layout.ceiling_chunks x k hk).2
    change chunks x k*k<x+k at h
    exact h.le
  have hprod := Nat.mul_le_mul_right k hsub
  unfold compactTopConfigPaddingCost compactCeilCost synDivModCost synMulRCost
  nlinarith

/-- Row-stock construction is linear in its explicit unary division budget,
plus the size of its input/output tapes. -/
theorem compactTopConfigRowsAfterCost_bound (a R k : ℕ) (hk : 0<k) :
    compactTopConfigRowsAfterCost a R k ≤
      128*((2^a*R+k+1)*(k+1)+a+R+Compact.Layout.paddedRows (2^a*R) k+1) := by
  have hpad := compactTopConfigPaddingCost_bound (2^a*R) k hk
  rw [Nat.mul_assoc] at hpad
  have hstock : 2^a*R≤(2^a*R+k+1)*(k+1) := by nlinarith
  have hk' : k≤(2^a*R+k+1)*(k+1) :=
    (Nat.le_mul_of_pos_right k (by omega : 0<k+1)).trans
      (Nat.mul_le_mul_right (k+1) (by omega : k≤2^a*R+k+1))
  unfold compactTopConfigRowsAfterCost
  omega

/-- All original-adapter work except the separately computed row stock is
linear in the actual header fields, including literal input restoration. -/
theorem compactTopOriginalAdapterCost_bound (d g W a D q E R aT K o : ℕ) :
    compactTopOriginalAdapterCost d g W a D q E R aT K o ≤
      compactTopConfigRowsCost d a R+
        512*(g+W+a+D+q+E+R+compactTopRows d R a+aT+K*q+o+1) := by
  have := compactTopConfigWriteCost_linear W a D q E R (compactTopRows d R a) aT (K*q) o
  unfold compactTopOriginalAdapterCost compactTopConfigCost
  omega

end
end IntegerMultBounds.MathlibTM2.Cost
