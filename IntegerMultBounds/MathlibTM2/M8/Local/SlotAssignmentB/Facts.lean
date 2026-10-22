module

public import IntegerMultBounds.MathlibTM2.M8.Local.SlotAssignmentB.Checked

/-! Soundness of the local slot-allocation and donor-link checks. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local.SlotAssignmentB
noncomputable section

/-- A structural all-check gives the proposed slot of every free use by its local index. -/
theorem freeSlotsOk_get (n p : Nat) : ∀ (us : List Use) (i : Nat), freeSlotsOk n p i us = true →
    ∀ j (hj : j < us.length), slotOf us[j] = expectedSlot n p (i + j)
  | [], _, _, j, hj => by simp at hj
  | u :: us, i, h, 0, _ => by
    have h := Nat.beq_eq.mp (Bool.and_eq_true_iff.mp h).1
    simpa only [List.getElem_cons_zero, Nat.add_zero] using h
  | u :: us, i, h, j + 1, hj => by
    have hj' : j < us.length := by simpa using hj
    have ht := freeSlotsOk_get n p us (i + 1) (Bool.and_eq_true_iff.mp h).2 j hj'
    simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1] using ht

theorem free_assignment (n : Nat) (hn : n < nodeCount) (i : Nat) (hi : i < (bAt n).2.length) :
    slotOf ((bAt n).2[i]) = expectedSlot n (pivotSlot n (argument n)) i := by
  have h := nodeOk_at n hn
  unfold nodeOk at h
  have hf := freeSlotsOk_get n _ _ 0 (Bool.and_eq_true_iff.mp h).1 i hi
  simpa only [Nat.zero_add] using hf

theorem linked_assignment (n : Nat) (hn : n < nodeCount) (L : Link)
    (hl : (records.get width n).link = some L) :
    slotOf (.gate L.user L.pos) = if L.operand then (argument n).2 else (argument n).1 := by
  have h := nodeOk_at n hn
  unfold nodeOk at h
  have h := (Bool.and_eq_true_iff.mp h).2
  rw [hl] at h
  exact Nat.beq_eq.mp h

end
end IntegerMultBounds.MathlibTM2.M8.Local.SlotAssignmentB
