module

public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! Restore a cursor from a saved forward copy, erasing both the advanced cursor
and the saved copy. The two copy tapes and every other tape are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def sparseCursorRestoreProgram (cursor saved tmp work : Fin T) : Pr P T Q A U :=
  .seq (bclear cursor) (.seq (bcopy saved cursor tmp work) (bclear saved))

theorem sparseCursorRestore_exec (body : P → Pr P T Q A U)
    (cursor saved tmp work : Fin T) (hreg : [cursor, saved, tmp, work].Nodup)
    (L cursorValue savedValue : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hcursor : S.R cursor = binSyms L cursorValue) (hsaved : S.R saved = binSyms L savedValue)
    (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (sparseCursorRestoreProgram cursor saved tmp work) (mk v S) (10 * L + 10)
        (mk v' { S with R := Function.update (Function.update S.R cursor (binSyms L savedValue)) saved [] }) := by
  have hn := hreg
  regs_ne hn
  obtain ⟨v₁, hu₁, _, he₁⟩ := bclear_exec body cursor v S
  rw [hcursor, length_binSyms] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R cursor [] }
  obtain ⟨v₂, hu₂, he₂⟩ := bcopy_exec body (a := saved) (c := cursor) (t₁ := tmp) (t₂ := work)
    (by regs_nodup) v₁ S₁
    (by simp [S₁, Ne.symm ‹cursor ≠ tmp›, htmp]) (by simp [S₁, Ne.symm ‹cursor ≠ work›, hwork])
  have hs : S₁.R saved = binSyms L savedValue := by simp [S₁, Ne.symm ‹cursor ≠ saved›, hsaved]
  have hf : Function.update S₁.R cursor (S₁.R saved ++ S₁.R cursor) = Function.update S.R cursor (binSyms L savedValue) := by
    simp [S₁, Ne.symm ‹cursor ≠ saved›, hsaved]
  rw [hf, hs, length_binSyms] at he₂
  let S₂ : Stacks T A := { S with R := Function.update S.R cursor (binSyms L savedValue) }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body saved v₂ S₂
  have hs₂ : S₂.R saved = binSyms L savedValue := by simp [S₂, Ne.symm ‹cursor ≠ saved›, hsaved]
  rw [hs₂, length_binSyms] at he₃
  refine ⟨v₃, hu₃.trans (hu₂.trans hu₁), ?_⟩
  have he := Exec.seq he₁ (Exec.seq he₂ he₃)
  convert he using 1 <;> first | omega | rfl

end IntegerMultBounds.MathlibTM2.Routing
