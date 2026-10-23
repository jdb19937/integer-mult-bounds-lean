module

public import IntegerMultBounds.MathlibTM2.Routing.BinarySelectorZeroFrame
public import IntegerMultBounds.MathlibTM2.Routing.SelectorGap

/-! Generate the absent-selector frame, emit a binary-sized gap, and erase the
frame. Only the accumulating selector output changes; every phase is charged. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def generatedSelectorGapProgram (rg : BinaryZeroReg → Fin T)
    (src count saved block dst work tmp ctmp : Fin T) : Pr P T Q A U :=
  .seq (binarySelectorZeroFrameProgram rg)
    (.seq (binaryWordRepeatProgram src count saved block dst work tmp ctmp) (bclear block))

theorem generatedSelectorGap_exec (body : P → Pr P T Q A U)
    (rg : BinaryZeroReg → Fin T) (hrg : Function.Injective rg)
    (src count saved block dst work tmp ctmp : Fin T)
    (hreg : [src, count, saved, block, dst, work, tmp, ctmp].Nodup)
    (hblockReg : rg .dst = block)
    (Lw Lg gap L W : ℕ) (hL : L < 2 ^ Lw) (hgap : gap < 2 ^ Lg)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg .width) = binSyms Lw L) (hunary : S.R (rg .unary) = [])
    (hscratch : ∀ i, S.R (rg (.scratch i)) = [])
    (hsrc : S.R src = binSyms Lg gap) (hblock : S.R block = [])
    (hcount : S.R count = []) (hsaved : S.R saved = []) (hwork : S.R work = [])
    (htmp : S.R tmp = []) (hctmp : S.R ctmp = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (Lw * (4 * L + 11) + 8 * L + 13) +
        binaryWordRepeatCost Lg gap (L + 1) + (2 * (L + 1) + 2) ∧
      Exec body (generatedSelectorGapProgram rg src count saved block dst work tmp ctmp)
        (mk v S) steps
        (mk v' { S with R := Function.update S.R dst (descriptorSelectorFrames L (List.replicate gap (0 : Fin (W + 1))) ++ S.R dst) }) := by
  have hn := hreg
  regs_ne hn
  obtain ⟨v₁, n₁, hu₁, ht₁, he₁⟩ := binarySelectorZeroFrame_exec body rg hrg Lw L hL v S hwidth hunary hscratch
  rw [hblockReg, hblock] at he₁
  let frame : List (Fin (A + 4)) := binSyms L 0 ++ [separator]
  let S₁ : Stacks T A := { S with R := Function.update S.R block frame }
  obtain ⟨v₂, n₂, hu₂, ht₂, he₂⟩ := selectorGap_exec body src count saved block dst work tmp ctmp
    hreg Lg gap L hgap W v₁ S₁
    (by simp [S₁, ‹src ≠ block›, hsrc]) (by simp [S₁, frame])
    (by simp [S₁, ‹count ≠ block›, hcount]) (by simp [S₁, ‹saved ≠ block›, hsaved])
    (by simp [S₁, Ne.symm ‹block ≠ work›, hwork])
    (by simp [S₁, Ne.symm ‹block ≠ tmp›, htmp]) (by simp [S₁, Ne.symm ‹block ≠ ctmp›, hctmp])
  let out := descriptorSelectorFrames (A := A) L (List.replicate gap (0 : Fin (W + 1))) ++ S.R dst
  have hd : S₁.R dst = S.R dst := by simp [S₁, Ne.symm ‹block ≠ dst›]
  rw [hd] at he₂
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst out }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body block v₂ S₂
  have hb : S₂.R block = frame := by simp [S₂, S₁, ‹block ≠ dst›]
  have hf : Function.update S₂.R block [] = Function.update S.R dst out := by
    funext j
    by_cases hj : j = block
    · subst j; simp [‹block ≠ dst›, hblock]
    · by_cases hd : j = dst
      · subst j; simp [S₂, S₁, hj]
      · simp [S₂, S₁, hj, hd]
  rw [hf, hb] at he₃
  have hlen : frame.length = L + 1 := by simp [frame]
  rw [hlen] at he₃
  exact ⟨v₃, n₁ + (n₂ + (2 * (L + 1) + 2)), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
