module

public import IntegerMultBounds.MathlibTM2.M8.Local.SlotAssignmentB.Facts
public import IntegerMultBounds.MathlibTM2.M8.Local.SlotAssignment
public import IntegerMultBounds.MathlibTM2.M8.Local.WitnessOrderB

/-! The checked local slot equations identify the actual compiler frontier. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open Local

private theorem pivotSlot_eq (n : Nat) :
    SlotAssignmentB.pivotSlot n (SlotAssignmentB.argument n) = SlotAssignmentB.slotOf (dagB.pivotUse n) := by
  cases h : (recAt n).link with
  | none => simp [SlotAssignmentB.pivotSlot, records_get, h, Dag.pivotUse, dagB, dag, SlotAssignmentB.slotOf]
  | some L => cases ho : L.operand <;>
      simp [SlotAssignmentB.pivotSlot, records_get, h, Dag.pivotUse, dagB, dag, SlotAssignmentB.slotOf, ho]

/-- The finite table satisfies the compiler's allocation and donor-link equations. -/
theorem slotAssignmentB : Dag.SlotAssignment dagB slotsBefore SlotAssignmentB.slotOf where
  free n hn i hi := by
    change n < nodeCount at hn
    have hi' : i < (bAt n).2.length := by simpa only [dagB_freeUses_eq n hn] using hi
    simp only [dagB_freeUses_eq n hn]
    have h := SlotAssignmentB.free_assignment n hn i hi'
    simpa only [SlotAssignmentB.expectedSlot, pivotSlot_eq, show dagB.v = leafCount from rfl] using h
  linked n o t pos hl := by
    change ((recAt n).link.map fun L => (L.operand, L.user, L.pos)) = some (o, t, pos) at hl
    cases hL : (recAt n).link with
    | none => simp [hL] at hl
    | some L =>
      have he : (L.operand, L.user, L.pos) = (o, t, pos) := by simpa [hL] using hl
      cases he
      have hn := (dagB_valid.link_donor n L.operand L.user L.pos (by simp [dagB, dag, hL])).2
      have h := SlotAssignmentB.linked_assignment n hn L hL
      simpa only [SlotAssignmentB.slotOf] using h

/-- Every internal gate argument is the slot named by the checked table. -/
theorem argument_slotB (n : Nat) (hv : leafCount ≤ n) (hn : n < nodeCount) (pos : Bool) :
    (dagB.compileTo n).pend (.gate n pos) = SlotAssignmentB.slotOf (.gate n pos) := by
  exact slotAssignmentB.compileTo_pending dagB_valid
    (fun k hk => (dagB_compileTo_next k (Nat.le_of_lt hk)).symm) n (Nat.le_of_lt hn) _
    (dagB.pending_arg dagB_valid hv hn pos)

/-- The same table identifies every final root slot, including linked roots. -/
theorem root_slotB (j : Nat) (hj : j < rootCount) :
    dagB.compile.pend (.root j) = SlotAssignmentB.slotOf (.root j) := by
  have h := slotAssignmentB.compileTo_pending dagB_valid
    (fun k hk => (dagB_compileTo_next k (Nat.le_of_lt hk)).symm) dagB.N (Nat.le_refl _) (.root j)
    (dagB.root_pending dagB_valid hj)
  simpa only [Dag.compile] using h

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
