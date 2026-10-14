module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedDormantFrameInvariant

/-! Completion frames are captured from clean literal stack tails. Actual
updates outside the saved slots retain settled frames, including the live
denominator update made by each scalar event. Intermediate nested saves use
Holds; settling a recursive child still requires its balanced restoration. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexSourceReadySettledFrames
noncomputable section
open CompactComplexSourceReadyReachedDormantFrameInvariant
open SharedPlacementAlphabet (setTape)
variable {s : ℕ}

/-- The actual call list and fixed origin determine the entire saved-PC word
and head, including the older stack restored after a nested return. -/
theorem saved_calls_unique {origin head head' : ℤ}
    {calls : List Networks.ComplexRecursiveCallSchema.Call} {f f' : ℤ → Fin 6}
    (h : CompactComplexSourceReadySavedCallHistory.Associated origin calls f head)
    (h' : CompactComplexSourceReadySavedCallHistory.Associated origin calls f' head') :
    f=f' ∧ head=head' := by
  induction h generalizing f' head' with
  | empty => cases h'; exact ⟨rfl,rfl⟩
  | push older call ih =>
    cases h' with
    | push older' =>
      obtain ⟨rfl,rfl⟩ := ih older'
      exact ⟨rfl,rfl⟩

/-- Capturing the real post-save bank starts a settled frame whenever its
stack tails are clean above their actual heads. -/
theorem captured_settled (snapshot : Snapshot s)
    (hstorage : ∀ i,protectedSlots snapshot.headerStack snapshot.liveStack snapshot.pcStack i →
      ∀ z,snapshot.storage.head i≤z → snapshot.storage.tape i z=blank)
    (haux : ∀ z,snapshot.aux.head 0≤z → snapshot.aux.tape 0 z=blank) :
    Settled snapshot snapshot.storage snapshot.aux :=
  ⟨captured snapshot,fun _ _ => rfl,hstorage,hstorage,rfl,haux,haux⟩

/-- Exact individual physical ports suffice; unrelated storage and the
auxiliary clock may change freely. No whole-bank equality is required. -/
theorem settled_of_port_eq {snapshot : Snapshot s}
    {storage storage' : Tapes (10+s) 2} {aux aux' : Tapes 2 2}
    (h : Settled snapshot storage aux)
    (hstorage : ∀ i,protectedSlots snapshot.headerStack snapshot.liveStack snapshot.pcStack i →
      storage'.head i=storage.head i ∧ storage'.tape i=storage.tape i)
    (haux : aux'.head 0=aux.head 0 ∧ aux'.tape 0=aux.tape 0) :
    Settled snapshot storage' aux' := by
  refine ⟨?_,?_,?_,h.reference_clean,?_,?_,h.aux_reference_clean⟩
  · refine ⟨?_,?_,?_⟩
    · intro i hi
      rw [(hstorage i hi).1,(hstorage i hi).2]
      exact h.preserved.1 i hi
    · rw [haux.1]
      exact h.preserved.2.1
    · rw [haux.2]
      exact h.preserved.2.2
  · intro i hi
    exact (hstorage i hi).1.trans (h.storage_heads i hi)
  · intro i hi z hz
    rw [(hstorage i hi).2]
    exact h.storage_clean i hi z hz
  · exact haux.1.trans h.aux_head
  · intro z hz
    rw [haux.2]
    exact h.aux_clean z hz

/-- Every unprotected physical storage update preserves all completion
fields, not just the lower saved prefixes. -/
theorem storage_update_settled {snapshot : Snapshot s}
    {storage : Tapes (10+s) 2} {aux : Tapes 2 2}
    (h : Settled snapshot storage aux) (i : Fin (10+s))
    (hi : ¬protectedSlots snapshot.headerStack snapshot.liveStack snapshot.pcStack i)
    (f : ℤ → Fin 6) (p : ℤ) :
    Settled snapshot (setTape storage i f p) aux := by
  apply settled_of_port_eq h
  · intro j hj
    have hne : j≠i := by intro he; subst j; exact hi hj
    simp only [setTape,Function.update_of_ne hne,and_self]
  · exact ⟨rfl,rfl⟩

/-- The genuine scalar endpoint updates only the common live denominator
and therefore keeps every settled ancestor frame. -/
theorem scalar_storage_settled {snapshot : Snapshot s}
    {storage : Tapes (10+s) 2} {aux : Tapes 2 2}
    (h : Settled snapshot storage aux) (n : ℕ) :
    Settled snapshot (CompactComplexScalarCallerEndpoint.storageOutput (by omega) storage n) aux := by
  apply storage_update_settled h
  intro hi
  exact protected_ne_live _ _ _ _ hi rfl

/-- Original corrected-source initialization changes only target8 on the
stored controller frame, retaining every captured ancestor stack. -/
theorem corrected_entry_storage_settled {snapshot : Snapshot s}
    {storage : Tapes (10+s) 2} {aux : Tapes 2 2}
    (h : Settled snapshot storage aux) (target : ℕ) :
    Settled snapshot (CompactComplexCorrectedEntryGeometryReadiness.storage storage target) aux := by
  apply settled_of_port_eq h
  · intro i hi
    apply CompactComplexCorrectedEntryGeometryReadiness.storage_other
    rcases hi with rfl|rfl|rfl|rfl <;> simp only [Fin.val_natAdd] <;> omega
  · exact ⟨rfl,rfl⟩

/-- Settled fields give usable clean tails at the current physical heads. -/
theorem storage_clean_current {snapshot : Snapshot s}
    {storage : Tapes (10+s) 2} {aux : Tapes 2 2}
    (h : Settled snapshot storage aux) (i : Fin (10+s))
    (hi : protectedSlots snapshot.headerStack snapshot.liveStack snapshot.pcStack i) :
    ∀ z,storage.head i≤z → storage.tape i z=blank := by
  rw [h.storage_heads i hi]
  exact h.storage_clean i hi

end
end IntegerMultBounds.Machine.CompactComplexSourceReadySettledFrames
