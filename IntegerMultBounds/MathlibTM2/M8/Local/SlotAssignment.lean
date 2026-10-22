module

public import IntegerMultBounds.MathlibTM2.M8.Local.PendingWeightsB

/-! Local allocation equations determine every pending compiler slot, including inherited slots. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local.Dag
noncomputable section
open Classical

/-- The unlinked operand becomes the result's pivot; an ordinary addition keeps the left slot. -/
def pivotUse (D : Dag) (n : Nat) : Use :=
  .gate n (match D.link n with | none => false | some (o, _, _) => !o)

/-- A proposed slot assignment is checked only at allocations and donor links. -/
structure SlotAssignment (D : Dag) (count : Nat → Nat) (slot : Use → Nat) : Prop where
  free : ∀ n, n < D.N → ∀ i, (hi : i < (D.freeUses n).length) →
    slot (D.freeUses n)[i] = if n < D.v then count n + i
      else if i = 0 then slot (D.pivotUse n) else count n + (i - 1)
  linked : ∀ n o t pos, D.link n = some (o, t, pos) →
    slot (.gate t pos) = slot (.gate n o)

namespace SlotAssignment
variable {D : Dag} {count : Nat → Nat} {slot : Use → Nat}

/-- Every newly served use receives its proposed slot. -/
theorem step_free (hs : SlotAssignment D count slot) (n : Nat) (hn : n < D.N)
    (st : State) (hc : st.next = count n)
    (ha : D.v ≤ n → ∀ pos, st.pend (.gate n pos) = slot (.gate n pos))
    (u : Use) (hu : u ∈ D.freeUses n) : (D.step st n).pend u = slot u := by
  let i := (D.freeUses n).idxOf u
  have hi : i < (D.freeUses n).length := List.idxOf_lt_length_iff.mpr hu
  have he : (D.freeUses n)[i] = u := List.getElem_idxOf hi
  rw [← he, hs.free n hn i hi]
  by_cases hv : n < D.v
  · rw [ite_eq_left hv]
    unfold Dag.step
    rw [ite_eq_left hv, FrameFlow.serve_pend_index _ _ _ _ (D.freeUses_nodup n) i hi]
    change (if i = 0 then st.next else st.next + 1 + (i - 1)) = count n + i
    split_ifs <;> omega
  · rw [ite_eq_right hv]
    have ha := ha (Nat.le_of_not_gt hv)
    cases hl : D.link n with
    | none =>
      simp only [Dag.step, hv, ite_false, hl, pivotUse]
      rw [FrameFlow.serve_pend_index _ _ _ _ (D.freeUses_nodup n) i hi]
      simp only [ha, hc]
    | some l =>
      obtain ⟨o, t, pos⟩ := l
      cases o <;>
        simp only [Dag.step, hv, ite_false, hl, pivotUse, Bool.not_false, Bool.not_true, Bool.false_eq_true] <;>
        rw [FrameFlow.serve_pend_index _ _ _ _ (D.freeUses_nodup n) i hi] <;>
        simp only [State.assign_next, ha, hc, ite_true]

/-- A donor's linked use inherits the operand slot named by the same table. -/
theorem step_linked (hs : SlotAssignment D count slot) (hv : D.Valid)
    (n : Nat) (hn : n < D.N) (st : State) (o : Bool) (t : Nat) (pos : Bool)
    (hl : D.link n = some (o, t, pos))
    (ha : ∀ b, st.pend (.gate n b) = slot (.gate n b)) :
    (D.step st n).pend (.gate t pos) = slot (.gate t pos) := by
  have hleaf := (hv.link_donor n o t pos hl).1
  have hnot : Use.gate t pos ∉ D.freeUses n := by
    intro hu
    have hf := (D.mem_freeUses.mp hu).2
    have hb : D.linkedB (.gate t pos) = true := (D.linkedB_iff _).mpr
      ⟨n, hn, by simp [Dag.linkUse, hl]⟩
    rw [hb] at hf
    cases hf
  unfold Dag.step
  rw [ite_eq_right (Nat.not_lt.mpr hleaf), hl, FrameFlow.serve_pend_other _ _ _ _ _ hnot]
  simp only [State.assign_pend, Function.update_self]
  cases o <;> simpa only [Bool.false_eq_true, ite_false, ite_true] using
    (ha _).trans (hs.linked n _ t pos hl).symm

/-- Local slot equations determine the complete pending frontier of every compiler prefix. -/
theorem compileTo_pending (hs : SlotAssignment D count slot) (hv : D.Valid)
    (hc : ∀ n < D.N, count n = (D.compileTo n).next) :
    ∀ k, k ≤ D.N → ∀ u, D.Pending k u → (D.compileTo k).pend u = slot u := by
  intro k
  induction k with
  | zero =>
    intro _ u hu
    rcases hu.2 with ⟨n, hn, _⟩ | ⟨n, hn, _⟩ <;> omega
  | succ k ih =>
    intro hk u hu
    have hkN : k < D.N := by omega
    have he : D.compileTo (k + 1) = D.step (D.compileTo k) k := by
      simp only [Dag.compileTo, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [he]
    have ha : D.v ≤ k → ∀ pos, (D.compileTo k).pend (.gate k pos) = slot (.gate k pos) :=
      fun hleaf pos => ih (by omega) _ (D.pending_arg hv hleaf hkN pos)
    rcases (D.pending_succ_iff hv k u).mp hu with ⟨hp, _⟩ | hf | hl
    · rw [FrameFlow.step_pend_after_source D hv _ k hkN u (FrameFlow.pending_src_lt D hv hp)]
      exact ih (by omega) u hp
    · exact hs.step_free k hkN _ (hc k hkN).symm ha u hf
    · obtain ⟨o, t, pos, hlink, rfl⟩ := D.linkUse_eq.mp hl
      exact hs.step_linked hv k hkN _ o t pos hlink (ha (hv.link_donor k o t pos hlink).1)

end SlotAssignment
end
end IntegerMultBounds.MathlibTM2.M8.Local.Dag
