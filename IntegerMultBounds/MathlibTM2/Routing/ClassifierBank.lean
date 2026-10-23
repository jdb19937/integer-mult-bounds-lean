module

public import IntegerMultBounds.MathlibTM2.Routing.ClassifierBankFrame

/-! Execute classifier generation on the concrete sixteen-tape workspace.
The initial interface consists solely of binary dimensions and blank scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

theorem classifierBank_exec {N Q A : ℕ} {P U : Type}
    (body : P → Pr P (N + 16) Q A U) (p : Par) (hG : 0 < p.G) (hGK : p.G + 1 < p.K)
    (temporary phase : Fin N) (hne : temporary ≠ phase)
    (L Ln Lo Lm : ℕ) (hK : p.K < 2 ^ L) (hn : p.n < 2 ^ Ln)
    (ho : p.ρ + 1 < 2 ^ Lo) (hm : p.m < 2 ^ Lm)
    (v : HS (N + 16) Q A U) (S : Stacks (N + 16) A)
    (hwidth : S.R (classifierAux 0) = binSyms L p.K)
    (hrun : S.R (classifierAux 1) = binSyms L p.G)
    (hcount : S.R (classifierAux 10) = binSyms Ln p.n)
    (hoffset : S.R (classifierAux 13) = binSyms Lo (p.ρ + 1))
    (hphaseOffset : S.R (classifierAux 14) = binSyms Lo p.ρ)
    (htop : S.R (classifierAux 15) = binSyms Lm p.m)
    (hscratch : ∀ i : Fin 16, 2 ≤ i.val → i.val ≠ 10 → i.val < 13 → S.R (classifierAux i) = [])
    (htemporary : S.R (classifierCore temporary) = []) (hphase : S.R (classifierCore phase) = []) :
    ∃ (v' : HS (N + 16) Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ binaryTemporaryMaskCost p L Ln Lo Lm + binaryPhaseMaskCost p L Ln Lo Lm ∧
      Exec body (classifierPairProgram classifierBankReg (classifierBankRepeat temporary phase) classifierBankPad)
        (mk v S) m (mk v' { S with R := classifierPairBank p (classifierBankRepeat temporary phase) S.R }) := by
  apply classifierPair_exec body p hG hGK classifierBankReg classifierBankReg_injective
    (classifierBankRepeat temporary phase) (classifierBankRepeat_injective temporary phase hne)
    (classifierBankRepeat_separate temporary phase) classifierBankPad
    classifierBankPad_separate (classifierBankPad_repeat temporary phase) L Ln Lo Lm hK hn ho hm v S
  · exact hwidth
  · exact hrun
  · intro r hw hr
    cases r with
    | width => exact (hw rfl).elim
    | run => exact (hr rfl).elim
    | bin => exact hscratch 2 (by decide) (by decide) (by decide)
    | low => exact hscratch 3 (by decide) (by decide) (by decide)
    | high => exact hscratch 4 (by decide) (by decide) (by decide)
    | dst => exact hscratch 5 (by decide) (by decide) (by decide)
    | work => exact hscratch 6 (by decide) (by decide) (by decide)
    | scratch i =>
      have hi := i.isLt
      exact hscratch ⟨7 + i.val, by omega⟩ (by change 2 ≤ 7 + i.val; omega)
        (by change 7 + i.val ≠ 10; omega) (by change 7 + i.val < 13; omega)
  · exact hcount
  · exact hscratch 11 (by decide) (by decide) (by decide)
  · exact hscratch 12 (by decide) (by decide) (by decide)
  · exact htemporary
  · exact hphase
  · exact hoffset
  · exact hphaseOffset
  · exact htop

end IntegerMultBounds.MathlibTM2.Routing
