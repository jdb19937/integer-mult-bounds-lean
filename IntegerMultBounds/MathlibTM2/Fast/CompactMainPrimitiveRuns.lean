module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainLayer
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Primitive source-register contracts on the expanded main host. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ResampA
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {A Ka : ℕ}

private theorem placedSrcRuns {T T' Q Q' : ℕ} {P P' U R : Type} [DecidableEq R]
    (e : Fin T → Fin T') (he : Function.Injective e) (hcap : Q≤Q') (hQ : 0<Q)
    (proc : P → P') (rg : R → Fin T) (scratch : Fin 64 → Fin T)
    {body : P → Pr P T Q A U} {body' : P' → Pr P' T' Q' A U}
    (hbody : ∀ f,body' (proc f)=statePlacedPr e hcap hQ proc (body f))
    {Pre : Stacks T A → Prop} {Pre' : Stacks T' A → Prop}
    (hpre : ∀ S,Pre' S → Pre (embStk e S))
    {p : Pr P T Q A U} {ρ ρ' : R → List (Fin (A+4))} {c : ℕ}
    (h : SrcRuns body rg scratch Pre p ρ ρ' c) :
    SrcRuns body' (e ∘ rg) (e ∘ scratch) Pre'
      (statePlacedNormalized e hcap hQ proc p) ρ ρ' (1+c) := by
  intro v S hc hp hS
  obtain ⟨w,S₁,n,hu,hn,hex,hρ,hfr⟩ :=
    h (stateLiftDown hQ (embDn e v)) (embStk e S)
      ⟨fun i => hc.1 (e i),hc.2⟩ (hpre S hp) hS
  obtain ⟨v',hv,hu',hex'⟩ := statePlaced_exec_normalized e he hcap hQ proc hbody v S hex
  have hproj := embStk_ovr he S₁ S
  have hL (i) : (embOvr e S₁.get S).L (e i)=S₁.L i :=
    congrArg (fun X : Stacks T A => X.L i) hproj
  have hR (i) : (embOvr e S₁.get S).R (e i)=S₁.R i :=
    congrArg (fun X : Stacks T A => X.R i) hproj
  refine ⟨v',embOvr e S₁.get S,1+n,hu'.trans hu,by omega,hex',?_,hfr.1,hfr.2.1,?_,?_⟩
  · intro r
    exact (hR (rg r)).trans (hρ r)
  · funext j
    by_cases hj : ∃ i,e i=j
    · obtain ⟨i,rfl⟩ := hj
      exact (hL i).trans (congrFun hfr.2.2.1 i)
    · exact (embOvr_off S₁.get S (fun i hi => hj ⟨i,hi⟩)).1
  · intro j hj
    by_cases hi : ∃ i,e i=j
    · obtain ⟨i,rfl⟩ := hi
      exact (hR i).trans (hfr.2.2.2 i (fun r hr => hj r (congrArg e hr)))
    · exact (embOvr_off S₁.get S (fun i hi' => hi ⟨i,hi'⟩)).2

/-- Any legacy primitive contract transports with one normalization step and its
full frame, including the newly reserved private bank. -/
theorem compactMainStage_srcRuns (legacy : MnProc → MnPr A)
    (native : LProc → CompactMnPr CompactMainProc A)
    {Pre : Stacks mnT A → Prop} {Pre' : Stacks compactMnT A → Prop}
    (hpre : ∀ S,Pre' S → Pre (embStk compactMnLegacyReg S))
    {p : MnPr A} {ρ ρ' : MnR → List (Fin (A+4))} {c : ℕ}
    (h : SrcRuns legacy mnRg mnι Pre p ρ ρ' c) :
    SrcRuns (compactMainTransportTable legacy native) compactMnRg
      (compactMnLegacyReg ∘ mnι) Pre' (compactMainStage p) ρ ρ' (1+c) := by
  have hrg : compactMnLegacyReg ∘ mnRg=compactMnRg :=
    funext compactMnLegacyReg_rg
  rw [←hrg]
  unfold compactMainStage
  with_reducible exact (placedSrcRuns (R := MnR) compactMnLegacyReg compactMnLegacyReg_injective
    compactMnQ_legacy mnQ_pos compactMainOldProc mnRg mnι
    (compactMainTransportTable_old legacy native) hpre h)

/-- The canonical table with compact layer procedures retains primitive contracts. -/
theorem compactMainBody_srcRuns (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions)
    {Pre : Stacks mnT (prime+Ka) → Prop} {Pre' : Stacks compactMnT (prime+Ka) → Prop}
    (hpre : ∀ S,Pre' S → Pre (embStk compactMnLegacyReg S))
    {p : MnPr (prime+Ka)} {ρ ρ' : MnR → List (Fin (prime+Ka+4))} {c : ℕ}
    (h : SrcRuns legacy mnRg mnι Pre p ρ ρ' c) :
    SrcRuns (compactMainBody legacy ds) compactMnRg (compactMnLegacyReg ∘ mnι) Pre'
      (compactMainStage p) ρ ρ' (1+c) :=
  compactMainStage_srcRuns legacy (compactMainNativeTable ds) hpre h

end
end IntegerMultBounds.MathlibTM2.Fast.Main
