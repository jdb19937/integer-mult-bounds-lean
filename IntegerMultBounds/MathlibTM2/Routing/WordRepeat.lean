module

public import IntegerMultBounds.MathlibTM2.Routing.WordRepeatLoop

/-! Uniform word repetition with complete input and scratch restoration.
The count is the length of a tape, not an unrolled program parameter. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

def wordRepeatProgram {T Q A : ℕ} {P U : Type} (src saved block dst tmp work : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR src))
    (.seq (.loop (·.flag) (wordRepeatStepProgram src saved block dst tmp work)) (moveR saved src id))

theorem wordRepeat_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (src saved block dst tmp work : Fin T)
    (hreg : [src, saved, block, dst, tmp, work].Nodup)
    (input word : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = input) (hblock : S.R block = word)
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ input.length * (6 * word.length + 11) + 4 ∧
      Exec body (wordRepeatProgram src saved block dst tmp work) (mk v S) m
        (mk v' { S with R := Function.update S.R dst (wordCopies word input.length ++ S.R dst) }) := by
  have hn := hreg
  regs_ne hn
  let v₁ := { v with flag := input.head?.isSome }
  have hp : (peekR src : Act T Q A U).run (mk v S) = mk v₁ S := by
    simp only [peekR_run, hsrc]; rfl
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := wordRepeatLoop_exec body src saved block dst tmp work hreg
    input word v₁ S hsrc hblock htmp hwork rfl
  let S₂ : Stacks T A := { S with R := wordRepeatBank S.R src saved dst input word }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body saved src (Ne.symm ‹src ≠ saved›) id v₂ S₂
  have hs₂ : S₂.R saved = input.reverse := by simp [S₂, wordRepeatBank, ‹saved ≠ dst›, hsaved]
  have hf : movedR S₂.R saved src id (S₂.R saved) =
      Function.update S.R dst (wordCopies word input.length ++ S.R dst) := by
    rw [hs₂]
    funext j
    by_cases hj : j = src
    · subst j; simp [movedR, S₂, wordRepeatBank, ‹src ≠ saved›, ‹src ≠ dst›, hsaved, hsrc]
    · by_cases hk : j = saved
      · subst j; simp [movedR, (Ne.symm ‹src ≠ saved›), ‹saved ≠ dst›, hsaved]
      · by_cases hd : j = dst
        · subst j; simp [movedR, S₂, wordRepeatBank, hj, hk]
        · simp [movedR, S₂, wordRepeatBank, hj, hk, hd]
  rw [hf, hs₂, List.length_reverse] at he₃
  refine ⟨v₃, 1 + (m₂ + (2 * input.length + 2)), hu₃.trans hu₂, ?_,
    Exec.seq (hp ▸ Exec.act (body := body) (peekR src) (mk v S)) (Exec.seq he₂ he₃)⟩
  simp only [Nat.mul_add] at hm₂ ⊢
  omega

end IntegerMultBounds.MathlibTM2.Routing
