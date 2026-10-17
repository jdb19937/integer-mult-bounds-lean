module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapPipeline
import IntegerMultBounds.MathlibTM2.Fast.CompactSynMainProjection
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynDispatch
import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapRuntime
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Derive the bootstrap setup view from the actual blank transform scratch and private bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

lemma compactMnSyn_dispatch (x : SynW) : compactMnSyn x=compactSynDispatchReg x :=
  (compactMnSyn_legacy x).symm.trans (compactMnLayerReg_legacy (sreg x))

private lemma synG_self (R : Fin (nT SXReg) → List (Fin (A+4))) :
    synG R (R ∘ sreg)=R := by
  funext z
  by_cases h : ∃ x,sreg x=z
  · obtain ⟨x,rfl⟩ := h
    exact synG_sreg x
  · exact synG_of_ne (fun x hx => h ⟨x,hx⟩)

lemma compactMnBootstrapCopied_private (R : Fin compactMnT → List (Fin (A+4)))
    (p d : ℕ) (z : CompactBReg) :
    compactMnBootstrapCopied R p d (compactMnLay (.bc (.inl z)))=
      R (compactMnLay (.bc (.inl z))) := by
  have hne (x : SynW) : compactMnLay (.bc (.inl z))≠compactMnSyn x := by
    rw [compactMnSyn_dispatch]
    exact (compactMnLegacyReg_ne_private (mnLayE (sreg x)) z).symm
  simp only [compactMnBootstrapCopied,Function.update_of_ne (hne (.s 0)),
    Function.update_of_ne (hne (.s 1))]

/-- The setup view is read from the real file; no separately initialized setup file is assumed. -/
def compactMnBootstrapView (R : Fin compactMnT → List (Fin (A+4))) (p d : ℕ) :=
  compactMnBootstrapCopied R p d ∘ compactMnBootstrapReg

lemma compactMnBootstrapView_input (R : Fin compactMnT → List (Fin (A+4)))
    (p d : ℕ) :
    compactMnBootstrapView R p d (sreg (.s 0))=List.replicate p tick ∧
      compactMnBootstrapView R p d (sreg (.s 1))=List.replicate d tick := by
  have h0 := compactMnBootstrapReg_source (.s 0)
    (by intro j; fin_cases j <;> simp [compactBasisOutputWire])
  have h1 := compactMnBootstrapReg_source (.s 1)
    (by intro j; fin_cases j <;> simp [compactBasisOutputWire])
  have hne : compactMnSyn (.s 0)≠compactMnSyn (.s 1) := compactMnSyn_injective.ne (by decide)
  simp only [compactMnBootstrapView,Function.comp_apply,h0,h1,compactMnBootstrapCopied,
    Function.update_self,Function.update_of_ne hne,true_and]

lemma compactMnBootstrapView_scratch (R : Fin compactMnT → List (Fin (A+4)))
    (p d : ℕ) (hs : ∀ i : Fin 32,R (compactMnSyn (.s i))=[])
    (hb : ∀ z : CompactBReg,R (compactMnLay (.bc (.inl z)))=[])
    (i : Fin 32) (h0 : i≠0) (h1 : i≠1) :
    compactMnBootstrapView R p d (sreg (.s i))=[] := by
  by_cases hout : ∃ j : Fin 7,SynW.s i=compactBasisOutputWire j
  · obtain ⟨j,hj⟩ := hout
    unfold compactMnBootstrapView compactMnBootstrapReg
    simp only [Function.comp_apply,hj,compactBasisSetupReg_output,compactMnLayerReg_private,
      compactMnBootstrapCopied_private,hb]
  · have he := compactMnBootstrapReg_source (.s i) (fun j hj => hout ⟨j,hj⟩)
    have hn0 : compactMnSyn (.s i)≠compactMnSyn (.s 0) :=
      compactMnSyn_injective.ne (by simpa using h0)
    have hn1 : compactMnSyn (.s i)≠compactMnSyn (.s 1) :=
      compactMnSyn_injective.ne (by simpa using h1)
    simp only [compactMnBootstrapView,Function.comp_apply,he,compactMnBootstrapCopied,
      Function.update_of_ne hn0,Function.update_of_ne hn1,hs]

/-- Actual execution needs only the original precision/depth sources and blank private scratch. -/
theorem compactMnOriginalBootstrap_from_sources (body : P → Pr P compactMnT Q A U)
    (R : Fin compactMnT → List (Fin (A+4))) (p d : ℕ) (hp : 2≤p) (hd : 0<d)
    (hpSource : (R (compactMnRg (.io .dpn))).length=p)
    (hdSource : (R (compactMnSyn (.p .D))).length=d-1)
    (hs : ∀ i : Fin 32,R (compactMnSyn (.s i))=[])
    (hb : ∀ z : CompactBReg,R (compactMnLay (.bc (.inl z)))=[]) :
    LayRuns body compactMnOriginalBootstrap R (compactMnBootstrapFinal R p d)
      (compactMnOriginalBootstrapCost p d) := by
  let Rboot := compactMnBootstrapView R p (d-1)
  have hv := compactMnBootstrapView_input R p (d-1)
  intro vbig S hL hR
  subst R
  refine compactMnOriginalBootstrap_exec body Rboot (Rboot ∘ sreg) p d hp hd
    ?_ ?_ ?_ vbig S hL hpSource ?_ (hs 0) (hs 1) (hs 2) ?_
  · simpa only [Function.comp_apply,List.length_replicate] using congrArg List.length hv.1
  · simpa only [Function.comp_apply,List.length_replicate] using congrArg List.length hv.2
  · intro i hi
    have h0 : i≠0 := by intro he; subst i; simp at hi
    have h1 : i≠1 := by intro he; subst i; simp at hi
    change compactMnBootstrapView S.R p (d-1) (sreg (.s i))=[]
    exact compactMnBootstrapView_scratch S.R p (d-1) hs hb i h0 h1
  · simpa only [compactMnSyn_legacy] using hdSource
  · exact (synG_self Rboot).symm

end
end IntegerMultBounds.MathlibTM2.Fast.Main
