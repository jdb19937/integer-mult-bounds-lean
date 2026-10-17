module

public import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedCallerTopCost
public import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedCallerSlack
public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerUniformOverhead
public import IntegerMultBounds.MathlibTM2.Cost.CompactRoundVolume
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformLayerContract
public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerSelectedRows

/-! Matching the actual retuned hybrid chunk cost to its original stream volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
open CompactGadgetReservationCapacity Filter
noncomputable section

/-- Fixed coefficient for the actual compact round, including all setup passes. -/
def compactRetunedRoundCoeff (ds : ComplexFramedExecution.Directions) : ℝ :=
  4*(32768+compactRetunedTopCoeff 1 ds)

private theorem mergeBound (overhead top V B stash : ℕ) (C P : ℝ)
    (ho : overhead≤32768*V+2*stash) (ht : (top:ℝ)≤C*(V:ℝ)*P)
    (hV : V≤4*B) (hC : 0≤C) (hP : 1≤P) :
    ((overhead+top:ℕ):ℝ)≤4*(32768+C)*(B:ℝ)*P+2*(stash:ℝ) := by
  have hoR : (overhead:ℝ)≤32768*(V:ℝ)+2*(stash:ℝ) := by exact_mod_cast ho
  have hVR : (V:ℝ)≤4*(B:ℝ) := by exact_mod_cast hV
  have hVP : (V:ℝ)≤(V:ℝ)*P := by nlinarith [Nat.cast_nonneg (α:=ℝ) V]
  have hmul := mul_le_mul_of_nonneg_right hVR (mul_nonneg (by linarith : 0≤32768+C) (by linarith : 0≤P))
  rw [Nat.cast_add]
  nlinarith only [hoR,ht,hVP,hmul]

end
end IntegerMultBounds.MathlibTM2.Cost
