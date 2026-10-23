module

public import IntegerMultBounds.MathlibTM2.Routing.MetadataJob

/-! One fixed iteration of counted word repetition. A count symbol is archived,
a supplied block is copied, and the remaining count is tested. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

def wordRepeatArchive {T Q A : ℕ} {U : Type} (src saved : Fin T) : Act T Q A U :=
  .pop (.rt src) (fun v x => { v with sym := x })
    (.push (.rt saved) (fun v => v.sym.getD blank) .done)

def wordRepeatStepProgram {T Q A : ℕ} {P U : Type} (src saved block dst tmp work : Fin T) : Pr P T Q A U :=
  .seq (.act (wordRepeatArchive src saved)) (.seq (bcopy block dst tmp work) (.act (peekR src)))

def wordRepeatStepBank {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (src saved dst : Fin T) (x : Fin (A + 4)) (rest word : List (Fin (A + 4))) :=
  Function.update (Function.update (Function.update R src rest) saved (x :: R saved)) dst (word ++ R dst)

theorem wordRepeatStep_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (src saved block dst tmp work : Fin T)
    (hreg : [src, saved, block, dst, tmp, work].Nodup)
    (x : Fin (A + 4)) (rest word : List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = x :: rest)
    (hblock : S.R block = word) (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ v', v'.user = v.user ∧ v'.flag = rest.head?.isSome ∧
      Exec body (wordRepeatStepProgram src saved block dst tmp work) (mk v S) (6 * word.length + 8)
        (mk v' { S with R := wordRepeatStepBank S.R src saved dst x rest word }) := by
  have hn := hreg
  regs_ne hn
  let v₁ := { v with sym := some x }
  let S₁ : Stacks T A := { S with R := Function.update (Function.update S.R src rest) saved (x :: S.R saved) }
  have hp : (wordRepeatArchive src saved : Act T Q A U).run (mk v S) = mk v₁ S₁ := by
    simp [wordRepeatArchive, Action.run, update_rt, hsrc, S₁, v₁, (Ne.symm ‹src ≠ saved›)]
  obtain ⟨v₂, hu₂, he₂⟩ := bcopy_exec body (a := block) (c := dst) (t₁ := tmp) (t₂ := work)
    (by regs_nodup) v₁ S₁
    (by simp [S₁, (Ne.symm ‹src ≠ tmp›), (Ne.symm ‹saved ≠ tmp›), htmp])
    (by simp [S₁, (Ne.symm ‹src ≠ work›), (Ne.symm ‹saved ≠ work›), hwork])
  have hblock₁ : S₁.R block = word := by simp [S₁, (Ne.symm ‹src ≠ block›), (Ne.symm ‹saved ≠ block›), hblock]
  have hdst₁ : S₁.R dst = S.R dst := by simp [S₁, (Ne.symm ‹src ≠ dst›), (Ne.symm ‹saved ≠ dst›)]
  rw [hblock₁, hdst₁] at he₂
  let S₂ : Stacks T A := { S with R := wordRepeatStepBank S.R src saved dst x rest word }
  have hsrc₂ : S₂.R src = rest := by simp [S₂, wordRepeatStepBank, ‹src ≠ dst›, ‹src ≠ saved›]
  let v₃ := { v₂ with flag := rest.head?.isSome }
  have hpeek : (peekR src : Act T Q A U).run (mk v₂ S₂) = mk v₃ S₂ := by
    simp only [peekR_run, hsrc₂]; rfl
  refine ⟨v₃, hu₂, rfl, ?_⟩
  exact Exec.cast (Exec.seq (hp ▸ Exec.act (body := body) _ (mk v S))
    (Exec.seq he₂ (hpeek ▸ Exec.act (body := body) (peekR src) (mk v₂ S₂)))) (by omega) rfl

end IntegerMultBounds.MathlibTM2.Routing
