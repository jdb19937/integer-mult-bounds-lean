module

public import IntegerMultBounds.MathlibTM2.Routing.SelectorGap

/-! Emit one sparse run: absent selectors followed by a live entry. Both binary
operands, the reusable zero frame and scratch survive. The code is independent
of the gap size and selector value; sparse-input traversal is a separate loop. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A M : ℕ} {P U : Type}

def selectorEntryProgram (src count saved block entry dst work tmp ctmp : Fin T) : Pr P T Q A U :=
  .seq (configurationWrite dst tmp ctmp [entry])
    (binaryWordRepeatProgram src count saved block dst work tmp ctmp)

theorem selectorEntry_exec (body : P → Pr P T Q A U)
    (src count saved block entry dst work tmp ctmp : Fin T)
    (hreg : [src, count, saved, block, entry, dst, work, tmp, ctmp].Nodup)
    (Lg gap L : ℕ) (hgap : gap < 2 ^ Lg) (q : Fin (M + 1))
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = binSyms Lg gap)
    (hentry : S.R entry = binSyms L q.val)
    (hblock : S.R block = binSyms L 0 ++ [separator])
    (hcount : S.R count = []) (hsaved : S.R saved = []) (hwork : S.R work = [])
    (htmp : S.R tmp = []) (hctmp : S.R ctmp = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (6 * L + 8) + binaryWordRepeatCost Lg gap (L + 1) ∧
      Exec body (selectorEntryProgram src count saved block entry dst work tmp ctmp)
        (mk v S) steps
        (mk v' { S with R := Function.update S.R dst (descriptorSelectorFrames L (List.replicate gap 0 ++ [q]) ++ S.R dst) }) := by
  have hn := hreg
  regs_ne hn
  obtain ⟨v₁, hu₁, he₁⟩ := descriptorSelectorWrite_exec body dst tmp ctmp (by regs_nodup)
    [entry] [q] L (by intro x hx; simp only [List.mem_singleton] at hx; subst x; exact ⟨‹entry ≠ dst›, ‹entry ≠ tmp›, ‹entry ≠ ctmp›⟩)
    v S (by simp [hentry]) htmp hctmp
  let word : List (Fin (A + 4)) := descriptorSelectorFrames L [q]
  let S₁ : Stacks T A := { S with R := Function.update S.R dst (word ++ S.R dst) }
  obtain ⟨v₂, n₂, hu₂, ht₂, he₂⟩ := selectorGap_exec body src count saved block dst work tmp ctmp
    (by regs_nodup) Lg gap L hgap M v₁ S₁
    (by simp [S₁, ‹src ≠ dst›, hsrc]) (by simp [S₁, ‹block ≠ dst›, hblock])
    (by simp [S₁, ‹count ≠ dst›, hcount]) (by simp [S₁, ‹saved ≠ dst›, hsaved])
    (by simp [S₁, Ne.symm ‹dst ≠ work›, hwork])
    (by simp [S₁, Ne.symm ‹dst ≠ tmp›, htmp]) (by simp [S₁, Ne.symm ‹dst ≠ ctmp›, hctmp])
  have hf : Function.update S₁.R dst (descriptorSelectorFrames L (List.replicate gap (0 : Fin (M + 1))) ++ S₁.R dst) =
      Function.update S.R dst (descriptorSelectorFrames L (List.replicate gap 0 ++ [q]) ++ S.R dst) := by
    simp [S₁, word, descriptorSelectorFrames_append, List.append_assoc]
  rw [hf] at he₂
  have he₁' : Exec body (configurationWrite dst tmp ctmp [entry]) (mk v S) (6 * L + 8) (mk v₁ S₁) := by
    convert he₁ using 1; simp
  exact ⟨v₂, (6 * L + 8) + n₂, hu₂.trans hu₁, by omega, Exec.seq he₁' he₂⟩

end IntegerMultBounds.MathlibTM2.Routing
