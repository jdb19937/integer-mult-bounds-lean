module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapPipeline
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapPipelineExit
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! A single charged original-input bootstrap around a transform and its global cleanup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

private theorem appendRuns {T : ℕ} (body : P → Pr P T Q A U)
    (entry follow : Pr P T Q A U) (v : HS T Q A U) (S : Stacks T A)
    (R₁ R₂ : Fin T → List (Fin (A+4))) (c₁ c₂ : ℕ) (hL : ∀ i,S.L i=[])
    (he : ∃ v' steps,v'.user=v.user ∧ steps≤c₁ ∧
      Exec body entry (mk v S) steps (mk v' {S with R:=R₁}))
    (hf : LayRuns body follow R₁ R₂ c₂) :
    ∃ v' steps,v'.user=v.user ∧ steps≤c₁+c₂ ∧
      Exec body (.seq entry follow) (mk v S) steps (mk v' {S with R:=R₂}) := by
  obtain ⟨v₁,n₁,hu₁,hc₁,he₁⟩ := he
  obtain ⟨v₂,n₂,hu₂,hc₂,he₂⟩ := hf v₁ {S with R:=R₁} hL rfl
  exact ⟨v₂,n₁+n₂,hu₂.trans hu₁,by omega,Exec.seq he₁ he₂⟩

/-- Exactly one entry bootstrap and one exit cleanup enclose the transform body. -/
def compactMnTransformPipeline (transform : Pr P compactMnT Q A U) : Pr P compactMnT Q A U :=
  .seq compactMnOriginalBootstrap (.seq transform compactMnGlobalsExit)

theorem compactMnTransformPipeline_exec (body : P → Pr P compactMnT Q A U)
    (transform : Pr P compactMnT Q A U) (v : HS compactMnT Q A U)
    (S : Stacks compactMnT A) (R : Fin compactMnT → List (Fin (A+4)))
    (p d c : ℕ) (hL : ∀ i,S.L i=[])
    (hentry : ∃ v' steps,v'.user=v.user ∧ steps≤compactMnOriginalBootstrapCost p d ∧
      Exec body compactMnOriginalBootstrap (mk v S) steps
        (mk v' {S with R:=compactMnBootstrapFinal S.R p d}))
    (htransform : LayRuns body transform (compactMnBootstrapFinal S.R p d) R c)
    (hglobals : CompactMainGlobals R p d) :
    ∃ v' steps,v'.user=v.user ∧
      steps≤compactMnOriginalBootstrapCost p d+(c+((2*d+2)+(2*(4*Nat.clog 2 p+6)+2))) ∧
      Exec body (compactMnTransformPipeline transform) (mk v S) steps
        (mk v' {S with R:=Function.update (Function.update R (compactMnLay (.bc (.inl (.work 13)))) []) (compactMnLay (.bc (.inl (.work 14)))) []}) :=
  appendRuns body compactMnOriginalBootstrap (.seq transform compactMnGlobalsExit)
    v S _ _ _ _ hL hentry (htransform.seq (compactMnGlobalsExit_runs body R p d hglobals))

/-- Concrete entry hypotheses discharge the entry execution internally. -/
theorem compactMnTransformPipeline_sources_exec (body : P → Pr P compactMnT Q A U)
    (transform : Pr P compactMnT Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (p d : ℕ) (hp : 2≤p) (hd : 0<d)
    (h0 : (v (.s 0)).length=p) (h1 : (v (.s 1)).length=d-1)
    (hz : ∀ i : Fin 32,i∈[2,6,9,10,12,15,17,18,19,23,26] → v (.s i)=[])
    (vbig : HS compactMnT Q A U) (S : Stacks compactMnT A) (hL : ∀ i,S.L i=[])
    (hpSource : (S.R (compactMnRg (.io .dpn))).length=p)
    (hdSource : (S.R (compactMnLayerReg (compactLegacyReg (sreg (.p .D))))).length=d-1)
    (hblank0 : S.R (compactMnSyn (.s 0))=[]) (hblank1 : S.R (compactMnSyn (.s 1))=[])
    (hblank2 : S.R (compactMnSyn (.s 2))=[])
    (hview : compactMnBootstrapCopied S.R p (d-1) ∘ compactMnBootstrapReg=synG R v)
    (Rfinal : Fin compactMnT → List (Fin (A+4))) (c : ℕ)
    (htransform : LayRuns body transform (compactMnBootstrapFinal S.R p d) Rfinal c)
    (hglobals : CompactMainGlobals Rfinal p d) :
    ∃ v' steps,v'.user=vbig.user ∧
      steps≤compactMnOriginalBootstrapCost p d+(c+((2*d+2)+(2*(4*Nat.clog 2 p+6)+2))) ∧
      Exec body (compactMnTransformPipeline transform) (mk vbig S) steps
        (mk v' {S with R:=Function.update (Function.update Rfinal (compactMnLay (.bc (.inl (.work 13)))) []) (compactMnLay (.bc (.inl (.work 14)))) []}) :=
  compactMnTransformPipeline_exec body transform vbig S Rfinal p d c hL
    (compactMnOriginalBootstrap_exec body R v p d hp hd h0 h1 hz vbig S hL
      hpSource hdSource hblank0 hblank1 hblank2 hview) htransform hglobals

end
end IntegerMultBounds.MathlibTM2.Fast.Main
