module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Core
public import IntegerMultBounds.Machine.SharedBankFamilyExact

/-!
# Padding the core's pieces

Each piece of the core runs on a bank of its own tapes, the common bank padded with blank private
tapes. Padding a piece to more tapes keeps its steps (`pad_step`), so all the pieces run on one
tape count.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Pad

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor)
open SharedBankStageInput (raw)
open SharedBankFamily (padProgram)
open SharedBankFamilyExact (atState)
open Core (Phase)

variable {k t n s : ℕ}

theorem eq_atState (c : Config t s prime) : c = atState c.tapes c.state := by
  cases c; rfl

/-- **Padding keeps a step.** -/
theorem pad_step {M : Program t s prime} (h : t ≤ n) (hkt : k ≤ t)
    {B : Descriptor → (ℕ → ZMod 2) → Tapes k prime} {u u' : Descriptor}
    {P : (ℕ → ZMod 2) → (ℕ → ZMod 2) → Prop} {c : ℕ}
    (hM : Phase M (fun u X => raw (B u X) t) u u' P c) :
    Phase (padProgram M h) (fun u X => raw (B u X) n) u u' P c := by
  intro X z hz
  subst hz
  obtain ⟨j, d, hj, hr, hh, Y, hY, hd⟩ := hM X _ rfl
  rw [eq_atState d, hd] at hr hh
  refine ⟨j, atState (raw (B u' Y) n) d.state, hj, ?_, SharedBankFamilyExact.pad_halt M h hkt _ _ hh, Y, hY, rfl⟩
  exact SharedBankFamilyExact.pad_run M h hkt _ _ M.start _ j hr

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Pad
