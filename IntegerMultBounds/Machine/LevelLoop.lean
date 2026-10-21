module

public import IntegerMultBounds.Machine.CountedLoopReuseAlphabet
public import IntegerMultBounds.Machine.FamilyPlacementAlphabet
public import IntegerMultBounds.Machine.CounterSteps

/-!
# Level loops

A level loop runs a body at levels `0, …, f - 2` and a last stage at level `f - 1`, with the
count `f - 1` as a runtime descriptor on the counted loop's control tapes. The body takes level
`l` to level `l + 1`, typically one stage and the counter steps to the next level; the last
stage needs no counter steps (`level_hoare`).
-/

@[expose] public section

namespace IntegerMultBounds.Machine.LevelLoop
open FlatCoordinateSchedule (bits)
noncomputable section
variable {t s s' a : ℕ}

/-- The body at every level but the last, then the last stage. -/
def program (B : Program t s a) (S : Program t s' a) :=
  seq (CountedLoopReuseAlphabet.program B) (extend S 2)

/-- The loop bank: the level bank and the count `f - 1`. -/
def bank (v : Tapes t a) (f : ℕ) : Tapes (t+2) a :=
  CountedLoopReuseAlphabet.bank v CountedLoopReuseAlphabet.empty
    (CountedLoopReuseAlphabet.binary (bits (f-1))) 1 1

/-- **The level loop.** -/
theorem level_hoare (B : Program t s a) (S : Program t s' a) (f : ℕ)
    (v : ℕ → Tapes t a) (w : Tapes t a) (c c' : ℕ)
    (hbody : ∀ l, l + 1 < f → HoareTime B (fun x => x = v l) (fun x => x = v (l+1)) c)
    (hlast : HoareTime S (fun x => x = v (f-1)) (fun x => x = w) c') :
    HoareTime (program B S) (fun x => x = bank (v 0) f) (fun x => x = bank w f)
      ((f-1)*c + 6*(f-1) + 7*(bits (f-1)).length + 16 + 1 + c') := by
  have hl := CountedLoopReuseAlphabet.loop_hoare B (bits (f-1)) (f-1) v (fun _ => c)
    (FlatCoordinateSchedule.bits_value _) (fun i hi => hbody i (by omega))
  have he := FamilyPlacementAlphabet.extend_hoare hlast
    (CountedLoopReuseAlphabet.controls (a := a) CountedLoopReuseAlphabet.empty
      (CountedLoopReuseAlphabet.binary (bits (f-1))) 1 1)
  have h := hl.seq he
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at h
  exact h

end
end IntegerMultBounds.Machine.LevelLoop
