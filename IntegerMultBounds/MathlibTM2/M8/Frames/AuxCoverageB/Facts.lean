module

public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checked

/-! Soundness of canonical auxiliary-chain membership checks. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB
noncomputable section
open Local

theorem slot_parts (s : Nat) (hs : s < GeometryB.slotCount) :
    chainIndex s < GeometryB.slotCount ∧
    AssignmentB.sigmaLabel s ∈ SignedFull.chainAt (chainIndex s) ∧
    AssignmentB.startLabel s ∈ SignedFull.chainAt (chainIndex s) ∧
    Signed.Frame.one ∈ SignedFull.chainAt (chainIndex s) := by
  have h := slotOk_at s hs
  unfold slotOk at h
  simpa only [chainIndex, Bool.and_eq_true, List.contains_iff_mem, Nat.blt_eq, and_assoc] using h

private theorem node_parts (n : Nat) (hv : leafCount ≤ n) (hn : n < nodeCount) :
    contains (SlotAssignmentB.argument n).1 (AssignmentB.nodeLabel n) = true ∧
    contains (SlotAssignmentB.argument n).2 (AssignmentB.nodeLabel n) = true ∧
    (List.range ((bAt n).2.length - 1)).all (fun i =>
      contains (SlotAssignmentB.pivotSlot n (SlotAssignmentB.argument n))
        (AssignmentB.startLabel (slotsBefore n + i))) = true := by
  have h := nodeOk_at n hn
  change nodeOk n (SlotAssignmentB.argument n) = true at h
  unfold nodeOk at h
  rw [ite_eq_right (Nat.not_lt.mpr hv)] at h
  simpa only [Bool.and_eq_true, and_assoc] using h

theorem node_mem (n : Nat) (hv : leafCount ≤ n) (hn : n < nodeCount) (pos : Bool) :
    AssignmentB.nodeLabel n ∈
      SignedFull.chainAt (chainIndex (SlotAssignmentB.slotOf (.gate n pos))) := by
  have h := node_parts n hv hn
  cases pos
  · exact List.contains_iff_mem.mp h.1
  · exact List.contains_iff_mem.mp h.2.1

theorem copy_mem (n : Nat) (hv : leafCount ≤ n) (hn : n < nodeCount)
    (f : Nat) (hf : f ∈ List.range' (slotsBefore n) ((bAt n).2.length - 1)) :
    AssignmentB.startLabel f ∈
      SignedFull.chainAt (chainIndex (SlotAssignmentB.pivotSlot n (SlotAssignmentB.argument n))) := by
  obtain ⟨i, hi, he⟩ := List.mem_range'.mp hf
  simp only [one_mul] at he
  subst f
  exact List.contains_iff_mem.mp (List.all_eq_true.mp (node_parts n hv hn).2.2 i
    (List.mem_range.mpr hi))

theorem root_parts (j : Nat) (hj : j < rootCount) :
    let w := GeometryB.endpointTree.get 8192 j
    w.1 = chainIndex (SlotAssignmentB.slotOf (.root j)) ∧
    Signed.Frame.negative w.2 ∈ SignedFull.chainAt w.1 ∧
    (SignedFull.bankEntry w.2).basis.length = 1 := by
  have h := rootOk_at j hj
  unfold rootOk at h
  simpa only [Bool.and_eq_true, Nat.beq_eq, List.contains_iff_mem, and_assoc] using h

end
end IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB
