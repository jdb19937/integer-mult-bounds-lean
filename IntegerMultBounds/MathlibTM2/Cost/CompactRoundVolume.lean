module

public import IntegerMultBounds.MathlibTM2.Fast.CompactTopRows
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! The actual padded working array differs from the original stream volume
by at most a fixed dyadic factor when the caller pays its precision shift. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
noncomputable section

theorem compactTopWorkingVolume_bounds (d K R a n r W shift D N : ℕ)
    (hK : 0<K) (hR : 0<R)
    (ha : CompactGlobalRowPadding.rowAxes NW m d*K≤a)
    (hN : n+a=N) (hwidth : shift+D≤W) :
    R*2^N*(r*W)≤compactTopRows d R a*2^n*(r*(W+shift+D)) ∧
      compactTopRows d R a*2^n*(r*(W+shift+D))≤4*(R*2^N*(r*W)) := by
  obtain ⟨hrows,_,hrows',_⟩ := compactTopRows_bounds hK hR ha
  have hworking : W≤W+shift+D := by omega
  have hworking' : W+shift+D≤2*W := by omega
  constructor
  · calc
      R*2^N*(r*W) = (R*2^a)*2^n*(r*W) := by rw [←hN,pow_add]; ring
      _ ≤ compactTopRows d R a*2^n*(r*(W+shift+D)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ hrows) (Nat.mul_le_mul_left r hworking)
  · calc
      compactTopRows d R a*2^n*(r*(W+shift+D))≤
          (2*(R*2^a))*2^n*(r*(2*W)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ hrows') (Nat.mul_le_mul_left r hworking')
      _ = 4*(R*2^N*(r*W)) := by rw [←hN,pow_add]; ring

end
end IntegerMultBounds.MathlibTM2.Cost
