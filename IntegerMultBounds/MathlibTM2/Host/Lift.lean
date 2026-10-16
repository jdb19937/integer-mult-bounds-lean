module

public import IntegerMultBounds.MathlibTM2.Host.Core

/-!
# Running smaller multitape programs on the host

The host simulates programs with a fixed state count `Q`. A program with `q ≤ Q` states runs
unchanged after its states are embedded in `Fin Q` (`liftQ`); the extra states halt at once and
are never reached. Contracts transfer with the same bound (`HoareTime.liftQ`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.Machine

variable {t q Q a : ℕ}

/-- Embed a program's states into `Fin Q`. -/
def liftQ (M : Program t q a) (h : q ≤ Q) : Program t Q a where
  tapes_pos := M.tapes_pos
  start := Fin.castLE h M.start
  transition := fun s symbols =>
    if hs : s.val < q then
      (M.transition ⟨s.val, hs⟩ symbols).map fun p => (Fin.castLE h p.1, p.2)
    else none

lemma liftQ_step (M : Program t q a) (h : q ≤ Q) (c : Config t q a) :
    step (liftQ M h) (c.mapState (Fin.castLE h)) = (step M c).map (Config.mapState (Fin.castLE h)) := by
  unfold step
  simp only [liftQ, Config.mapState, Fin.val_castLE, c.state.isLt, dite_eq_left]
  cases M.transition c.state (fun i => c.tape i (c.head i)) <;> rfl

lemma liftQ_run (M : Program t q a) (h : q ≤ Q) :
    ∀ (k : ℕ) (c : Config t q a),
      run (liftQ M h) k (c.mapState (Fin.castLE h)) = (run M k c).map (Config.mapState (Fin.castLE h)) := by
  intro k
  induction k with
  | zero => intro c; rfl
  | succ k ih =>
      intro c
      simp only [run, liftQ_step]
      cases step M c with
      | none => rfl
      | some c' => exact ih c'

/-- Contracts transfer to the lifted program with the same bound. -/
theorem HoareTime.liftQ {M : Program t q a} (h : q ≤ Q) {pre post : TapePred t a} {k : ℕ}
    (hM : HoareTime M pre post k) : HoareTime (IntegerMultBounds.MathlibTM2.Host.liftQ M h) pre post k := by
  intro v hv
  obtain ⟨kk, c, hk, hrun, hstep, hpost⟩ := hM v hv
  refine ⟨kk, c.mapState (Fin.castLE h), hk, ?_, ?_, hpost⟩
  · have := liftQ_run M h kk (v.start M)
    rw [hrun] at this
    exact this
  · rw [liftQ_step, hstep]; rfl

end IntegerMultBounds.MathlibTM2.Host
