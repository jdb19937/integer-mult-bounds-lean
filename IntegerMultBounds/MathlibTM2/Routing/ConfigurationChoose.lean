module

public import IntegerMultBounds.MathlibTM2.Routing.MetadataJob

/-!
# Select a live metadata source by unary tape nonemptiness

This is the source-renaming branch of the elementary compiler: at coordinate
zero use the target coordinate; otherwise retain the source coordinate. Only the
chosen word is copied, and the gate, both source words and scratch are restored.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def configurationChooseProgram (gate live zero dst tmp work : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR gate)) (.cond (·.flag) (bcopy live dst tmp work) (bcopy zero dst tmp work))

/-- Runtime source selection with a complete bank frame and exact copying cost. -/
theorem configurationChoose_exec (body : P → Pr P T Q A U) (gate live zero dst tmp work : Fin T)
    (hlive : [live, dst, tmp, work].Nodup) (hzero : [zero, dst, tmp, work].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (hdst : S.R dst = []) (htmp : S.R tmp = []) (hwork : S.R work = []) :
    let chosen := if (S.R gate).head?.isSome then live else zero
    ∃ v', v'.user = v.user ∧
      Exec body (configurationChooseProgram gate live zero dst tmp work) (mk v S)
        (6 * (S.R chosen).length + 8) (mk v' { S with R := Function.update S.R dst (S.R chosen) }) := by
  let v₀ := { v with flag := (S.R gate).head?.isSome }
  have hp : (peekR gate : Act T Q A U).run (mk v S) = mk v₀ S := rfl
  cases hg : (S.R gate).head?.isSome with
  | false =>
    obtain ⟨v', hu, he⟩ := bcopy_exec body hzero v₀ S htmp hwork
    refine ⟨v', hu, ?_⟩
    simp only [Bool.false_eq_true, reduceIte]
    rw [hdst, List.append_nil] at he
    exact Exec.cast (Exec.seq (hp ▸ Exec.act (body := body) (peekR gate) (mk v S))
      (Exec.cond_false (f := (·.flag)) hg he)) (by omega) rfl
  | true =>
    obtain ⟨v', hu, he⟩ := bcopy_exec body hlive v₀ S htmp hwork
    refine ⟨v', hu, ?_⟩
    simp only [reduceIte]
    rw [hdst, List.append_nil] at he
    exact Exec.cast (Exec.seq (hp ▸ Exec.act (body := body) (peekR gate) (mk v S))
      (Exec.cond_true (f := (·.flag)) hg he)) (by omega) rfl

end IntegerMultBounds.MathlibTM2.Routing
