module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryPhaseBlock
public import IntegerMultBounds.MathlibTM2.Routing.BinaryWordRepeat

/-! Generate and repeat phase-mask blocks from binary dimensions, then
erase the generated block. Only the accumulating output tape changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks

def binaryPhaseRepeatProgram {T Q A : ℕ} {P U : Type}
    (rg : PhaseBlockReg → Fin T) (rp : Fin 4 → Fin T) : Pr P T Q A U :=
  .seq (binaryPhaseBlockProgram rg)
    (.seq (binaryWordRepeatProgram (rp 0) (rp 1) (rp 2) (rg .dst) (rp 3) (rg .work) (rg (.scratch 0)) (rg (.scratch 1)))
      (bclear (rg .dst)))

theorem binaryPhaseRepeat_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (rg : PhaseBlockReg → Fin T) (hrg : Function.Injective rg)
    (rp : Fin 4 → Fin T) (hrp : Function.Injective rp) (hsep : ∀ i r, rp i ≠ rg r)
    (L Ln K G n : ℕ) (hK : K < 2 ^ L) (hG : 0 < G) (hGK : G + 1 < K) (hn : n < 2 ^ Ln)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg .width) = binSyms L K) (hrun : S.R (rg .run) = binSyms L G)
    (hblank : ∀ r, r ≠ .width → r ≠ .run → S.R (rg r) = [])
    (hcount : S.R (rp 0) = binSyms Ln n) (hunary : S.R (rp 1) = []) (hsaved : S.R (rp 2) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ binaryPhaseBlockCost L K G + binaryWordRepeatCost Ln n K + (2 * K + 2) ∧
      Exec body (binaryPhaseRepeatProgram rg rp) (mk v S) m
        (mk v' { S with R := Function.update S.R (rp 3) (wordCopies (binSyms K (phaseBlockValue G)) n ++ S.R (rp 3)) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := binaryPhaseBlock_exec body rg hrg L K G hK hG hGK v S hwidth hrun hblank
  let word : List (Fin (A + 4)) := binSyms K (phaseBlockValue G)
  let S₁ : Stacks T A := { S with R := Function.update S.R (rg .dst) word }
  have hregs : [rp 0, rp 1, rp 2, rg .dst, rp 3, rg .work, rg (.scratch 0), rg (.scratch 1)].Nodup := by
    simp [List.nodup_cons, hrp.eq_iff, hrg.eq_iff, hsep, Ne.symm]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := binaryWordRepeat_exec body (rp 0) (rp 1) (rp 2) (rg .dst) (rp 3)
    (rg .work) (rg (.scratch 0)) (rg (.scratch 1)) hregs Ln n hn word v₁ S₁
    (by simp [S₁, hsep, hcount]) (by simp [S₁]) (by simp [S₁, hsep, hunary])
    (by simp [S₁, hsep, hsaved])
    (by simp [S₁, hrg.eq_iff, hblank .work (by simp) (by simp)])
    (by simp [S₁, hrg.eq_iff, hblank (.scratch 0) (by simp) (by simp)])
    (by simp [S₁, hrg.eq_iff, hblank (.scratch 1) (by simp) (by simp)])
  have ho₁ : S₁.R (rp 3) = S.R (rp 3) := by simp [S₁, hsep]
  rw [ho₁] at he₂
  simp only [word, length_binSyms] at hm₂
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rp 3) (wordCopies word n ++ S.R (rp 3)) }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body (rg .dst) v₂ S₂
  have hd₂ : S₂.R (rg .dst) = word := by simp [S₂, S₁, (hsep 3 .dst).symm]
  have hf : Function.update S₂.R (rg .dst) [] = Function.update S.R (rp 3) (wordCopies word n ++ S.R (rp 3)) := by
    funext j
    by_cases hj : j = rg .dst
    · subst j; simp [(hsep 3 .dst).symm, hblank .dst (by simp) (by simp)]
    · by_cases ho : j = rp 3
      · subst j; simp [S₂, hj]
      · simp [S₂, S₁, hj, ho]
  rw [hf, hd₂] at he₃
  simp only [word, length_binSyms] at he₃
  exact ⟨v₃, m₁ + (m₂ + (2 * K + 2)), hu₃.trans (hu₂.trans hu₁), by omega, Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
