module

public import IntegerMultBounds.Schoenhage.Relabel

/-! Shared full-bank algebra for placement and cleanup. These rules describe
endpoints only; executable routines still supply their checked run and cost. -/
@[expose] public section
namespace IntegerMultBounds.Schoenhage.TapeBank

theorem place_update {small large : ℕ} {slots : Fin small → Fin large}
    (injective : Function.Injective slots) (bank : Fin large → WTape)
    (localBank : Fin small → WTape) (slot : Fin small) (value : WTape) :
    upd bank slots (Function.update localBank slot value) =
      Function.update (upd bank slots localBank) (slots slot) value := by
  funext tape
  by_cases selected : ∃ index, slots index = tape
  · obtain ⟨index, rfl⟩ := selected
    rw [upd_slot bank injective]
    by_cases same : index = slot
    · subst index; simp
    · rw [Function.update_of_ne same,
        Function.update_of_ne (fun equal => same (injective equal)), upd_slot bank injective]
  · push Not at selected
    rw [upd_other bank slots _ tape selected,
      Function.update_of_ne (fun equal => selected slot equal.symm), upd_other bank slots _ tape selected]

theorem place_self {small large : ℕ} {slots : Fin small → Fin large}
    (injective : Function.Injective slots) (bank : Fin large → WTape) :
    upd bank slots (bank ∘ slots) = bank := by
  funext tape
  by_cases selected : ∃ index, slots index = tape
  · obtain ⟨index, rfl⟩ := selected
    rw [upd_slot bank injective]; rfl
  · push Not at selected
    rw [upd_other bank slots _ tape selected]

/-- Arbitrary local endpoints, including multiple changed tapes, lift without
changing the bound and preserve the entire complementary bank. -/
theorem runs_place {alphabet small large : ℕ} (slots : Fin small → Fin large)
    (injective : Function.Injective slots) {command : Cmd alphabet small}
    {bank : Fin large → WTape} {localOutput : Fin small → WTape} {bound : ℕ}
    (localRun : Runs command (bank ∘ slots) (· = localOutput) bound) :
    Runs (command.map slots injective) bank (· = upd bank slots localOutput) bound := by
  refine (localRun.map slots injective bank rfl).mono (fun finalBank facts => ?_) le_rfl
  funext tape
  by_cases selected : ∃ index, slots index = tape
  · obtain ⟨index, rfl⟩ := selected
    rw [upd_slot bank injective]
    exact congrFun facts.1 index
  · push Not at selected
    rw [facts.2 tape selected, upd_other bank slots _ tape selected]

/-- Clear exactly the listed tapes; every other whole word tape is retained. -/
def cleared {tapes : ℕ} (slots : List (Fin tapes)) (bank : Fin tapes → WTape) : Fin tapes → WTape :=
  fun tape => if tape ∈ slots then emp else bank tape

theorem cleared_cons {tapes : ℕ} (slot : Fin tapes) (rest : List (Fin tapes))
    (bank : Fin tapes → WTape) :
    cleared (slot :: rest) bank = cleared rest (Function.update bank slot emp) := by
  funext tape
  by_cases same : tape = slot <;> by_cases member : tape ∈ rest <;>
    simp [cleared, same, member]

/-- Turn any finite sequence of clears into a named whole-bank mask. Duplicates
are allowed for endpoint semantics; this theorem makes no runtime claim. -/
theorem clear_fold {tapes : ℕ} (slots : List (Fin tapes)) (bank : Fin tapes → WTape) :
    slots.foldl (fun current slot => Function.update current slot emp) bank = cleared slots bank := by
  induction slots generalizing bank with
  | nil => rfl
  | cons slot rest inductionHypothesis =>
    rw [List.foldl_cons, inductionHypothesis, ← cleared_cons]

theorem cleared_all {tapes : ℕ} (slots : List (Fin tapes))
    (covers : ∀ tape, tape ∈ slots) (bank : Fin tapes → WTape) :
    cleared slots bank = fun _ => emp := by
  funext tape
  simp [cleared, covers tape]

end IntegerMultBounds.Schoenhage.TapeBank
