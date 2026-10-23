module

public import IntegerMultBounds.MathlibTM2.Routing.ClassifierLayout

/-! Execute both classifier-mask generators with a shared workspace.
Every binary input and scratch tape is restored; exactly two outputs change. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

def classifierPairProgram {T Q A : ℕ} {P U : Type}
    (rg : PhaseBlockReg → Fin T) (rp : Fin 5 → Fin T) (pad : Fin 3 → Fin T) : Pr P T Q A U :=
  .seq (binaryTemporaryMaskProgram (rg ∘ temporaryPhaseRole)
    (rp ∘ classifierRepeatRole false) (pad ∘ classifierPadRole false))
    (binaryPhaseMaskProgram rg (rp ∘ classifierRepeatRole true) (pad ∘ classifierPadRole true))

def classifierPairBank {T A : ℕ} (p : Par) (rp : Fin 5 → Fin T)
    (bank : Fin T → List (Fin (A + 4))) :=
  Function.update (Function.update bank (rp 3) (binSyms (p.wy + 1) (IntegerMultBounds.MathlibTM2.Node.mAV p)))
    (rp 4) (binSyms (p.wy + 1) (mkV p))

theorem classifierPair_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (p : Par) (hG : 0 < p.G) (hGK : p.G + 1 < p.K)
    (rg : PhaseBlockReg → Fin T) (hrg : Function.Injective rg)
    (rp : Fin 5 → Fin T) (hrp : Function.Injective rp) (hsep : ∀ i r, rp i ≠ rg r)
    (pad : Fin 3 → Fin T) (hpadr : ∀ i r, pad i ≠ rg r) (hpadp : ∀ i j, pad i ≠ rp j)
    (L Ln Lo Lm : ℕ) (hK : p.K < 2 ^ L) (hn : p.n < 2 ^ Ln)
    (ho : p.ρ + 1 < 2 ^ Lo) (hm : p.m < 2 ^ Lm)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg .width) = binSyms L p.K) (hrun : S.R (rg .run) = binSyms L p.G)
    (hblank : ∀ r, r ≠ .width → r ≠ .run → S.R (rg r) = [])
    (hcount : S.R (rp 0) = binSyms Ln p.n) (hunary : S.R (rp 1) = []) (hsaved : S.R (rp 2) = [])
    (htemporary : S.R (rp 3) = []) (hphase : S.R (rp 4) = [])
    (hoffset : S.R (pad 0) = binSyms Lo (p.ρ + 1))
    (hphaseOffset : S.R (pad 1) = binSyms Lo p.ρ) (htop : S.R (pad 2) = binSyms Lm p.m) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ binaryTemporaryMaskCost p L Ln Lo Lm + binaryPhaseMaskCost p L Ln Lo Lm ∧
      Exec body (classifierPairProgram rg rp pad) (mk v S) m
        (mk v' { S with R := classifierPairBank p rp S.R }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := binaryTemporaryMask_exec body p hG (by omega)
    (rg ∘ temporaryPhaseRole) (hrg.comp temporaryPhaseRole_injective)
    (rp ∘ classifierRepeatRole false) (hrp.comp (classifierRepeatRole_injective false))
    (fun i r => hsep _ _) (pad ∘ classifierPadRole false) (fun i r => hpadr _ _) (fun i j => hpadp _ _)
    L Ln Lo Lm hK hn ho hm v S hwidth hrun
    (by
      intro r hw hr
      apply hblank
      · cases r <;> simp_all [temporaryPhaseRole]
      · cases r <;> simp_all [temporaryPhaseRole])
    (by simpa using hcount) (by simpa using hunary) (by simpa using hsaved)
    (by simpa using htemporary) (by simpa using hoffset) (by simpa using htop)
  simp only [Function.comp_apply, classifierRepeatRole_three, Bool.false_eq_true, ↓reduceIte] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R (rp 3) (binSyms (p.wy + 1) (IntegerMultBounds.MathlibTM2.Node.mAV p)) }
  have hkeep (i : Fin T) (hi : i ≠ rp 3) : S₁.R i = S.R i := by simp [S₁, hi]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := binaryPhaseMask_exec body p hG hGK rg hrg
    (rp ∘ classifierRepeatRole true) (hrp.comp (classifierRepeatRole_injective true))
    (fun i r => hsep _ _) (pad ∘ classifierPadRole true) (fun i r => hpadr _ _) (fun i j => hpadp _ _)
    L Ln Lo Lm hK hn (by omega) hm v₁ S₁
    (by rw [hkeep _ (hsep 3 .width).symm]; exact hwidth)
    (by rw [hkeep _ (hsep 3 .run).symm]; exact hrun)
    (by intro r hw hr; rw [hkeep _ (hsep 3 r).symm]; exact hblank r hw hr)
    (by simpa [Function.comp_apply, hkeep _ (hrp.ne (by decide : (0 : Fin 5) ≠ 3))] using hcount)
    (by simpa [Function.comp_apply, hkeep _ (hrp.ne (by decide : (1 : Fin 5) ≠ 3))] using hunary)
    (by simpa [Function.comp_apply, hkeep _ (hrp.ne (by decide : (2 : Fin 5) ≠ 3))] using hsaved)
    (by simpa [Function.comp_apply, hkeep _ (hrp.ne (by decide : (4 : Fin 5) ≠ 3))] using hphase)
    (by simpa [Function.comp_apply, hkeep _ (hpadp 1 3)] using hphaseOffset)
    (by simpa [Function.comp_apply, hkeep _ (hpadp 2 3)] using htop)
  exact ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Routing
