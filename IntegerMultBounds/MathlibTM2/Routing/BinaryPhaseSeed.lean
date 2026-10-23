module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryPhaseRepeat

/-! Seed the high boundary mark before emitting the repeated phase blocks.
The boundary is part of the executed output, including when the count is zero. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

def binaryPhaseSeedProgram {T Q A : ℕ} {P U : Type}
    (rg : PhaseBlockReg → Fin T) (rp : Fin 4 → Fin T) : Pr P T Q A U :=
  .seq (.act (.push (.rt (rp 3)) (fun _ => bitSymbol true) .done)) (binaryPhaseRepeatProgram rg rp)

theorem binaryPhaseSeed_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (rg : PhaseBlockReg → Fin T) (hrg : Function.Injective rg)
    (rp : Fin 4 → Fin T) (hrp : Function.Injective rp) (hsep : ∀ i r, rp i ≠ rg r)
    (L Ln K G n : ℕ) (hK : K < 2 ^ L) (hG : 0 < G) (hGK : G + 1 < K) (hn : n < 2 ^ Ln)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg .width) = binSyms L K) (hrun : S.R (rg .run) = binSyms L G)
    (hblank : ∀ r, r ≠ .width → r ≠ .run → S.R (rg r) = [])
    (hcount : S.R (rp 0) = binSyms Ln n) (hunary : S.R (rp 1) = []) (hsaved : S.R (rp 2) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 1 + binaryPhaseBlockCost L K G + binaryWordRepeatCost Ln n K + (2 * K + 2) ∧
      Exec body (binaryPhaseSeedProgram rg rp) (mk v S) m
        (mk v' { S with R := Function.update S.R (rp 3) (wordCopies (binSyms K (phaseBlockValue G)) n ++ bitSymbol true :: S.R (rp 3)) }) := by
  let seed : Act T Q A U := .push (.rt (rp 3)) (fun _ => bitSymbol true) .done
  let S₁ : Stacks T A := { S with R := Function.update S.R (rp 3) (bitSymbol true :: S.R (rp 3)) }
  have hp : seed.run (mk v S) = mk v S₁ := by simp [seed, Action.run, update_rt, S₁]
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := binaryPhaseRepeat_exec body rg hrg rp hrp hsep L Ln K G n
    hK hG hGK hn v S₁
    (by simp [S₁, (hsep 3 .width).symm, hwidth])
    (by simp [S₁, (hsep 3 .run).symm, hrun])
    (by intro r hw hr; simpa [S₁, (hsep 3 r).symm] using hblank r hw hr)
    (by simp [S₁, hrp.eq_iff, hcount]) (by simp [S₁, hrp.eq_iff, hunary])
    (by simp [S₁, hrp.eq_iff, hsaved])
  have hf : Function.update S₁.R (rp 3)
      (wordCopies (binSyms K (phaseBlockValue G)) n ++ S₁.R (rp 3)) =
      Function.update S.R (rp 3)
        (wordCopies (binSyms K (phaseBlockValue G)) n ++ bitSymbol true :: S.R (rp 3)) := by
    simp [S₁]
  rw [hf] at he₁
  exact ⟨v₁, 1 + m₁, hu₁, by omega, Exec.seq (hp ▸ Exec.act (body := body) seed (mk v S)) he₁⟩

end IntegerMultBounds.MathlibTM2.Routing
