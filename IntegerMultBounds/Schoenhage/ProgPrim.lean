module

public import IntegerMultBounds.Schoenhage.Cmd

/-! Any literal program as a word-program primitive. A program becomes a
finite-state machine on its own numbered states with the same transitions
(`FMachine.ofProgram`), whose runs are the program's runs (`frun_ofProgram`),
so a contract of the program on encoded banks is a contract of the machine
(`hoare_ofProgram`). `Prim.ofProgram` packages a program with an abstract
effect on word tapes as a primitive; word programs can then call proven
machines of any size. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine

variable {t q a : ℕ}

/-- A program as a finite-state machine on its numbered states. -/
def FMachine.ofProgram (M : Program t q a) : FMachine t a where
  S := Fin q
  start := M.start
  δ := M.transition

/-- The machine configuration of a program configuration. -/
def toCfg {M : Program t q a} (c : Config t q a) : (FMachine.ofProgram M).Cfg := ⟨c.state, ⟨c.head, c.tape⟩⟩

theorem fstep_ofProgram (M : Program t q a) (c : Config t q a) :
    (FMachine.ofProgram M).fstep (toCfg c) = (step M c).map toCfg := by
  unfold FMachine.fstep step toCfg
  simp only [FMachine.ofProgram]
  cases M.transition c.state (fun i => c.tape i (c.head i)) with
  | none => rfl
  | some p => rfl

theorem frun_ofProgram (M : Program t q a) (k : ℕ) (c : Config t q a) :
    (FMachine.ofProgram M).frun k (toCfg c) = (run M k c).map toCfg := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    simp only [FMachine.frun, run, fstep_ofProgram]
    cases step M c with
    | none => rfl
    | some d => simp [ih]

/-- A program's contract is a contract of its finite-state machine. -/
theorem hoare_ofProgram (M : Program t q a) (ht : 0 < t) {pre post : TapePred t a} {b : ℕ}
    (h : HoareTime M pre post b) : HoareTime ((FMachine.ofProgram M).toProgram ht) pre post b := by
  apply FMachine.hoare
  intro v hv
  obtain ⟨k, c, hk, hr, hh, hp⟩ := h v hv
  refine ⟨k, toCfg c, hk, ?_, ?_, hp⟩
  · have := frun_ofProgram M k (v.start M)
    rw [hr] at this
    exact this
  · rw [fstep_ofProgram, hh]; rfl

/-- A program with an abstract effect on word tapes, as a primitive. -/
noncomputable def Prim.ofProgram (M : Program t q a) (ht : 0 < t) (pre : (Fin t → WTape) → Prop)
    (sem : (Fin t → WTape) → (Fin t → WTape)) (cost : (Fin t → WTape) → ℕ)
    (h : ∀ σ, pre σ → HoareTime M (· = enc σ) (· = enc (sem σ)) (cost σ)) : Prim a where
  s := t
  hs := ht
  M := FMachine.ofProgram M
  pre := pre
  sem := sem
  cost := cost
  spec σ hσ := hoare_ofProgram M ht (h σ hσ)

end IntegerMultBounds.Schoenhage
