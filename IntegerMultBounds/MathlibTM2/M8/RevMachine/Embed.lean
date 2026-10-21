module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Graph
public import IntegerMultBounds.Machine.PlacementBank

/-!
# Placing a block on the common bank

Every block of the reversed family is a fixed program on its own small bank, placed on the
common bank by an injective map of tapes into the common tapes and `p` private blank tapes
(`place`). One theorem serves every block (`place_runs`): if the small bank is read off the
common bank before, the small program's exact contract gives the common bank after, wherever the
small bank is written back, and every common tape outside the image is kept.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.Embed

noncomputable section
open IntegerMultBounds.Machine
open SharedBankStageInput (raw)

variable {t s q a p u : ℕ}

/-- The block of a small program placed by `slot` on the common bank and `p` private tapes. -/
def place (M : Program s q a) (slot : Fin s → Fin (t+p)) (hinj : Function.Injective slot)
    (hsize : s + u = t + p) : Graph.Block t a :=
  SharedBankFamily.ofProgram (s := p) (Placement.placed M (InjectivePlacement.placement slot hinj hsize))

@[simp] theorem raw_left (x : Tapes t a) (j : Fin t) :
    (raw x (t+p)).head (Fin.castAdd p j) = x.head j ∧ (raw x (t+p)).tape (Fin.castAdd p j) = x.tape j := by
  simp [raw]

@[simp] theorem raw_right (x : Tapes t a) (j : Fin p) :
    (raw x (t+p)).head (Fin.natAdd t j) = 0 ∧ (raw x (t+p)).tape (Fin.natAdd t j) = fun _ => blank := by
  simp [raw]

/-- **The placed block's run.** -/
theorem place_runs {M : Program s q a} {X X' : Tapes s a} {B : ℕ}
    (h : HoareTime M (fun w => w = X) (fun w => w = X') B)
    (slot : Fin s → Fin (t+p)) (hinj : Function.Injective slot) (hsize : s + u = t + p)
    (x y : Tapes t a)
    (hin : ∀ i, (raw x (t+p)).head (slot i) = X.head i ∧ (raw x (t+p)).tape (slot i) = X.tape i)
    (hout : ∀ i, (raw y (t+p)).head (slot i) = X'.head i ∧ (raw y (t+p)).tape (slot i) = X'.tape i)
    (hkeep : ∀ j : Fin t, (∀ i, slot i ≠ Fin.castAdd p j) → y.head j = x.head j ∧ y.tape j = x.tape j) :
    HoareTime (place M slot hinj hsize).program (fun w => w = raw x (place M slot hinj hsize).tapes)
      (fun w => w = raw y (place M slot hinj hsize).tapes) B := by
  change HoareTime (Placement.placed M (InjectivePlacement.placement slot hinj hsize))
    (fun w => w = raw x (t+p)) (fun w => w = raw y (t+p)) B
  refine InjectivePlacement.hoare_exact h slot hinj hsize _ _ ?_ ?_
  · rw [InjectivePlacement.active_bank]
    apply congrArg₂ Tapes.mk <;> funext i
    · exact (hin i).1
    · exact (hin i).2
  · apply Placement.Tapes.ext'
    · intro z
      by_cases hz : ∃ i, slot i = z
      · obtain ⟨i, rfl⟩ := hz
        rw [InjectivePlacement.replace_head_slot, (hout i).1]
      · push Not at hz
        rw [InjectivePlacement.replace_head_other _ _ _ _ _ _ hz]
        refine Fin.addCases (fun j hz => ?_) (fun j _ => ?_) z hz
        · rw [(raw_left x j).1, (raw_left y j).1, (hkeep j hz).1]
        · rw [(raw_right x j).1, (raw_right y j).1]
    · intro z
      by_cases hz : ∃ i, slot i = z
      · obtain ⟨i, rfl⟩ := hz
        rw [InjectivePlacement.replace_tape_slot, (hout i).2]
      · push Not at hz
        rw [InjectivePlacement.replace_tape_other _ _ _ _ _ _ hz]
        refine Fin.addCases (fun j hz => ?_) (fun j _ => ?_) z hz
        · rw [(raw_left x j).2, (raw_left y j).2, (hkeep j hz).2]
        · rw [(raw_right x j).2, (raw_right y j).2]

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.Embed
