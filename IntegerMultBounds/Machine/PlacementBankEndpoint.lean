module

public import IntegerMultBounds.Machine.PlacementBank
public import IntegerMultBounds.Machine.SharedPlacementAlphabet

/-! A small active projection and unchanged complementary tapes determine a
placed program's exact whole-bank endpoint. This avoids expanding a large
chosen tape permutation when composing certified local machine procedures. -/

@[expose] public section
namespace IntegerMultBounds.Machine.InjectivePlacement
variable {activeCount extraCount tapeCount alphabet : ℕ}

/-- Prove a complete-bank replacement by checking only the active output and
literal retention of all other heads/cells. No transition or runtime claim is
assumed or changed; this is the endpoint algebra of the existing placement. -/
theorem replace_eq (slots : Fin activeCount → Fin tapeCount) (slotsInjective : Function.Injective slots)
    (bankSize : activeCount+extraCount=tapeCount) (before expected : Tapes tapeCount alphabet)
    (localOutput : Tapes activeCount alphabet)
    (activeExpected : Placement.active (placement slots slotsInjective bankSize) expected=localOutput)
    (otherExpected : ∀ slot,(∀ index,slots index≠slot) → expected.head slot=before.head slot ∧ expected.tape slot=before.tape slot) :
    Placement.replace (placement slots slotsInjective bankSize) before localOutput=expected := by
  rw [active_bank] at activeExpected
  apply Placement.Tapes.ext'
  · intro slot
    by_cases isActive : ∃ index,slots index=slot
    · obtain ⟨index,rfl⟩ := isActive
      rw [replace_head_slot]
      exact (congrArg (fun bank => bank.head index) activeExpected).symm
    · have outside : ∀ index,slots index≠slot := fun index equal => isActive ⟨index,equal⟩
      rw [replace_head_other _ _ _ _ _ _ outside]
      exact (otherExpected slot outside).1.symm
  · intro slot
    by_cases isActive : ∃ index,slots index=slot
    · obtain ⟨index,rfl⟩ := isActive
      rw [replace_tape_slot]
      exact (congrArg (fun bank => bank.tape index) activeExpected).symm
    · have outside : ∀ index,slots index≠slot := fun index equal => isActive ⟨index,equal⟩
      rw [replace_tape_other _ _ _ _ _ _ outside]
      exact (otherExpected slot outside).2.symm


/-- Replacing an active projection with one updated tape updates exactly the
corresponding whole-bank tape, retaining every other head and cell. -/
theorem replace_set (slots : Fin activeCount → Fin tapeCount) (slotsInjective : Function.Injective slots)
    (bankSize : activeCount+extraCount=tapeCount) (before : Tapes tapeCount alphabet)
    (index : Fin activeCount) (tape : ℤ → Fin (alphabet+4)) (head : ℤ) :
    Placement.replace (placement slots slotsInjective bankSize) before
      (SharedPlacementAlphabet.setTape (Placement.active (placement slots slotsInjective bankSize) before) index tape head)=
      SharedPlacementAlphabet.setTape before (slots index) tape head := by
  apply replace_eq
  · rw [active_bank,active_bank]
    apply Placement.Tapes.ext'
    · intro selected
      simp [SharedPlacementAlphabet.setTape,Function.update_apply,slotsInjective.eq_iff]
    · intro selected
      simp [SharedPlacementAlphabet.setTape,Function.update_apply,slotsInjective.eq_iff]
  · intro selected outside
    have different : selected≠slots index := (outside index).symm
    simp [SharedPlacementAlphabet.setTape,Function.update_of_ne different]

end IntegerMultBounds.Machine.InjectivePlacement
