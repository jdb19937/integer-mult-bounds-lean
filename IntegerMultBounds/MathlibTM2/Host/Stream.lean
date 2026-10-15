module

public import IntegerMultBounds.MathlibTM2.Host.Core

/-!
# Stream loops on host stacks

Right stacks `R i` of the host serve as list registers over the alphabet `Fin (A + 4)`. Each loop
below is proved by induction on the list it consumes, with an exact step count and an exact
effect on the stacks it touches; all other stacks and the `user` registers are unchanged.

Popping a register and pushing onto another reverses the moved list.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2

set_option linter.unusedSimpArgs false

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-- Record in `flag` whether register `i` is nonempty. -/
def peekR (i : Fin T) : Act T Q A U :=
  .peek (.rt i) (fun v o => { v with flag := o.isSome }) .done

lemma peekR_run (i : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    (peekR i : Act T Q A U).run (mk v S) = mk { v with flag := (S.R i).head?.isSome } S := rfl

/-- Repeat `b` while register `i` is nonempty. -/
def whileR (i : Fin T) (b : Act T Q A U) : Pr P T Q A U :=
  .seq (.act (peekR i)) (.loop (·.flag) (.act b))

/-- One step of `moveR`: pop register `i`, push its image under `f` onto register `j`. -/
def moveStep (i j : Fin T) (f : Fin (A + 4) → Fin (A + 4)) : Act T Q A U :=
  .pop (.rt i) (fun v o => { v with sym := o })
    (.push (.rt j) (fun v => f (v.sym.getD blank)) (peekR i))

/-- Move register `i` onto register `j`, mapping each symbol by `f`. -/
def moveR (i j : Fin T) (f : Fin (A + 4) → Fin (A + 4)) : Pr P T Q A U :=
  whileR i (moveStep i j f)

/-- Registers after moving `l` from `i` onto `j`. -/
def movedR (R : Fin T → List (Fin (A + 4))) (i j : Fin T) (f : Fin (A + 4) → Fin (A + 4))
    (l : List (Fin (A + 4))) : Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update R i []) j ((l.map f).reverse ++ R j)

theorem moveR_loop (i j : Fin T) (hij : i ≠ j) (f : Fin (A + 4) → Fin (A + 4)) :
    ∀ (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      S.R i = l → v.flag = l.head?.isSome →
      ∃ v', v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (moveStep i j f))) (mk v S) (2 * l.length + 1)
          (mk v' { S with R := movedR S.R i j f l }) := by
  intro l
  induction l with
  | nil =>
      intro v S hS hf
      refine ⟨v, rfl, ?_⟩
      have : ({ S with R := movedR S.R i j f [] } : Stacks T A) = S := by
        cases S with
        | mk inp out L R =>
          simp only at hS
          congr 1
          funext k
          by_cases hk : k = j
          · subst hk; simp [movedR]
          · by_cases hk' : k = i
            · subst hk'; simp [movedR, hk, hS]
            · simp [movedR, hk, hk']
      rw [this]
      exact .loop_false (by simpa using hf)
  | cons e rest ih =>
      intro v S hS hf
      obtain ⟨v', hu, he⟩ := ih { v with sym := some e, flag := rest.head?.isSome }
        { S with R := Function.update (Function.update S.R i rest) j (f e :: S.R j) }
        (by simp [Function.update_of_ne hij]) rfl
      refine ⟨v', hu, ?_⟩
      have hrun : (moveStep i j f : Act T Q A U).run (mk v S) =
          mk { v with sym := some e, flag := rest.head?.isSome }
            { S with R := Function.update (Function.update S.R i rest) j (f e :: S.R j) } := by
        simp [moveStep, peekR, Action.run, hS, update_rt, Function.update_of_ne hij,
          Function.update_of_ne hij.symm]
      refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (moveStep i j f) (mk v S)) he) (by simp; ring) ?_
      congr 2
      funext k
      by_cases hk : k = j
      · subst hk; simp [movedR, Function.update_of_ne hij.symm]
      · by_cases hk' : k = i
        · subst hk'; simp [movedR, hk]
        · simp [movedR, hk, hk']

theorem moveR_exec (i j : Fin T) (hij : i ≠ j) (f : Fin (A + 4) → Fin (A + 4)) (v : HS T Q A U)
    (S : Stacks T A) :
    ∃ v', v'.user = v.user ∧
      Exec body (moveR i j f) (mk v S) (2 * (S.R i).length + 2)
        (mk v' { S with R := movedR S.R i j f (S.R i) }) := by
  obtain ⟨v', hu, he⟩ := moveR_loop body i j hij f (S.R i) { v with flag := (S.R i).head?.isSome } S
    rfl rfl
  exact ⟨v', hu, Exec.cast (Exec.seq (peekR_run i v S ▸ Exec.act (body := body) (peekR i) (mk v S)) he)
    (by ring) rfl⟩

end IntegerMultBounds.MathlibTM2.Host
