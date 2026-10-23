module

public import IntegerMultBounds.MathlibTM2.Routing.ClassifierBank
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Generate classifier masks, execute a core program with a stream-only frame,
and erase both masks. All generation and cleanup costs are included. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

theorem classifierBankRepair_exec {N Q A : ℕ} {P U : Type}
    (body : P → Pr P (N + 16) Q A U)
    (coreBody : P → Pr P N Q A U) (hbody : ∀ f, body f = embProg classifierCore id (coreBody f))
    (repair : Pr P N Q A U) (p : Par) (hG : 0 < p.G) (hGK : p.G + 1 < p.K)
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
    (htemporary : S.R (classifierCore temporary) = []) (hphase : S.R (classifierCore phase) = [])
    (src : Fin N) (hts : temporary ≠ src) (hps : phase ≠ src)
    (records : List (Fin (A + 4))) (C : ℝ)
    (hrepair : ∀ w : HS N Q A U,
      let W : Stacks (N + 16) A := { S with R := classifierPairBank p (classifierBankRepeat temporary phase) S.R }
      ∃ (w' : HS N Q A U) (k : ℕ), w'.user = w.user ∧ (k : ℝ) ≤ C ∧
        Exec coreBody repair (mk w (embStk classifierCore W)) k
          (mk w' { embStk classifierCore W with R := Function.update (embStk classifierCore W).R src records })) :
    ∃ (v' : HS (N + 16) Q A U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ (binaryTemporaryMaskCost p L Ln Lo Lm + binaryPhaseMaskCost p L Ln Lo Lm : ℕ) +
        C + (4 * (p.wy + 1) + 5 : ℕ) ∧
      Exec body (.seq (classifierPairProgram classifierBankReg (classifierBankRepeat temporary phase) classifierBankPad)
        (.seq (embProg classifierCore id repair)
          (metadataClean [classifierCore temporary, classifierCore phase])))
        (mk v S) m (mk v' { S with R := Function.update S.R (classifierCore src) records }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := classifierBank_exec body p hG hGK temporary phase hne
    L Ln Lo Lm hK hn ho hm v S hwidth hrun hcount hoffset hphaseOffset htop hscratch htemporary hphase
  let W : Stacks (N + 16) A := { S with R := classifierPairBank p (classifierBankRepeat temporary phase) S.R }
  obtain ⟨w₂, m₂, hu₂, hm₂, he₂⟩ := hrepair (embDn classifierCore v₁)
  obtain ⟨v₂, hu₃, he₃⟩ := exec_emb_stream classifierCore classifierCore_injective id coreBody body hbody
    repair v₁ W w₂ m₂ src records he₂
  obtain ⟨v₃, hu₄, he₄⟩ := classifierClean_exec body p (classifierBankRepeat temporary phase)
    (classifierBankRepeat_injective temporary phase hne) (classifierCore src)
    (by simpa [classifierBankRepeat, classifierCore_injective.eq_iff] using hts)
    (by simpa [classifierBankRepeat, classifierCore_injective.eq_iff] using hps)
    v₂ S records htemporary hphase
  refine ⟨v₃, m₁ + (m₂ + (4 * (p.wy + 1) + 5)), hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_,
    Exec.seq he₁ (Exec.seq he₃ he₄)⟩
  have hc : (m₁ : ℝ) ≤ (binaryTemporaryMaskCost p L Ln Lo Lm + binaryPhaseMaskCost p L Ln Lo Lm : ℕ) := by
    exact_mod_cast hm₁
  push_cast
  push_cast at hc
  linarith

end IntegerMultBounds.MathlibTM2.Routing
