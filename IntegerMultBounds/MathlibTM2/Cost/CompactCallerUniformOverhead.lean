module
public import IntegerMultBounds.MathlibTM2.Cost.CompactSynLayerOverheadRuntime
public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerUniformBudget
public import IntegerMultBounds.MathlibTM2.Mult.CompactSizes
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopReady

/-! Eventual absorption of actual complete compact-round overhead. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast CompactGadgetReservationCapacity Filter
noncomputable section

private theorem callerAddressGeometry (N K D o qrow : ℕ)
    (hq : qrow≤D) (haddress : o+K*D≤N) :
    qrow*K≤N-(o+K*(D-qrow)) ∧ o+K*(D-qrow)≤N := by
  have he : K*(D-qrow)+qrow*K=K*D := by
    rw [Nat.mul_comm qrow K,←Nat.mul_add,Nat.sub_add_cancel hq]
  omega

end
end IntegerMultBounds.MathlibTM2.Cost
