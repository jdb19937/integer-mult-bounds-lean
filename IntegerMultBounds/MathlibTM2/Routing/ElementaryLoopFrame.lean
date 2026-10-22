module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryLoopData

/-! # Exact final configuration cursor, archive and stream of the elementary loop -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast

noncomputable def elementaryLoopRecords {n : ℕ} (rows : ℕ) :
    List (ElementaryInstruction n) → List (List α) → List (List α)
  | [], l => l
  | d :: ds, l => elementaryLoopRecords rows ds (moveRecs (d.rank rows) l)

/-- Every configuration is consumed and archived; all unrelated registers are
restored, including the shared counters and mutable metadata bank. -/
theorem elementaryLoopBank_eq {t₀ T n A : ℕ}
    (R : Fin T → List (Fin (A + 4))) (rg : LayReg t₀ → Fin T) (config saved : Fin T)
    (hcs : config ≠ saved) (hconfig : config ≠ rg .str) (hsaved : saved ≠ rg .str)
    (rows : ℕ) (ds : List (ElementaryInstruction n)) (l : List (List (Fin (A + 4))))
    (hinput : R config = elementaryFrames ds) (hstream : R (rg .str) = l.flatten) :
    elementaryLoopBank R rg config saved rows ds l =
      Function.update (Function.update (Function.update R config [])
        saved ((elementaryFrames ds).reverse ++ R saved)) (rg .str) (elementaryLoopRecords rows ds l).flatten := by
  induction ds generalizing R l with
  | nil =>
    simp only [elementaryFrames] at hinput
    simp only [elementaryLoopBank, elementaryFrames, elementaryLoopRecords,
      List.reverse_nil, List.nil_append]
    rw [← hinput, Function.update_eq_self]
    rw [Function.update_eq_self, ← hstream, Function.update_eq_self]
  | cons d ds ih =>
    rw [elementaryLoopBank, ih]
    · funext j
      by_cases hj : j = config <;> by_cases ha : j = saved <;> by_cases ht : j = rg .str <;>
        simp_all [elementaryStepBank, elementaryFrames, elementaryLoopRecords,
          List.reverse_append, List.append_assoc]
    · simp [elementaryStepBank, Function.update_of_ne hconfig, Function.update_of_ne hcs]
    · simp [elementaryStepBank]

noncomputable def elementaryInstructionsRank {n : ℕ} (rows : ℕ) :
    List (ElementaryInstruction n) → Equiv.Perm (Fin (rows * 2 ^ n))
  | [] => Equiv.refl _
  | d :: ds => (d.rank rows).trans (elementaryInstructionsRank rows ds)

private theorem moveRecs_identity {α : Type*} {M : ℕ} (l : List (List α)) (hl : l.length = M) :
    moveRecs (Equiv.refl (Fin M)) l = l := by
  apply List.ext_getElem (by simp [length_moveRecs, hl])
  intro j h₁ h₂
  simp [moveRecs, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]

/-- The loop's full output stream is one exact rank permutation. -/
theorem elementaryLoopRecords_eq {α : Type*} {n : ℕ} (rows : ℕ)
    (ds : List (ElementaryInstruction n)) (l : List (List α)) (hl : l.length = rows * 2 ^ n) :
    elementaryLoopRecords rows ds l = moveRecs (elementaryInstructionsRank rows ds) l := by
  induction ds generalizing l with
  | nil => exact (moveRecs_identity l hl).symm
  | cons d ds ih =>
    rw [elementaryLoopRecords, ih _ (length_moveRecs _ _), elementaryInstructionsRank,
      moveRecs_trans _ _ l hl]

end IntegerMultBounds.MathlibTM2.Routing
