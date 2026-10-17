module
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainTransport
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd


/-! Exact legacy layer contracts on the expanded main host, with one entry-normalization step. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {A Ka : ℕ}

private theorem placedNormalizedRuns {T T' Q Q' : ℕ} {P P' U : Type}
    (e : Fin T → Fin T') (he : Function.Injective e) (hcap : Q≤Q') (hQ : 0<Q) (ι : P → P')
    {body : P → Pr P T Q A U} {body' : P' → Pr P' T' Q' A U}
    (hbody : ∀ f,body' (ι f)=statePlacedPr e hcap hQ ι (body f))
    {p : Pr P T Q A U} {R₀ R₁ : Fin T → List (Fin (A+4))} {c : ℕ}
    (h : LayRuns body p R₀ R₁ c) (R : Fin T' → List (Fin (A+4))) (hR : R ∘ e=R₀) :
    LayRuns body' (statePlacedNormalized e hcap hQ ι p) R (embExt e R₁ R) (1+c) := by
  intro v S hL hS
  obtain ⟨w,k,hu,hk,hex⟩ := h (stateLiftDown hQ (embDn e v)) (embStk e S)
    (fun i => hL (e i)) (by change S.R ∘ e=R₀; rw [hS]; exact hR)
  obtain ⟨v',hv,hu',hex'⟩ := statePlaced_exec_normalized e he hcap hQ ι hbody v S hex
  refine ⟨v',1+k,hu'.trans hu,by omega,Exec.cast hex' rfl ?_⟩
  apply congrArg (mk v')
  simp only [embOvr,embStk,Stacks.get,embExt_comp,hS]

private theorem placedRuns {T T' Q : ℕ} {P P' U : Type}
    (e : Fin T → Fin T') (he : Function.Injective e) (ι : P → P')
    {body : P → Pr P T Q A U} {body' : P' → Pr P' T' Q A U}
    (hbody : ∀ f,body' (ι f)=embProg e ι (body f))
    {p : Pr P T Q A U} {R₀ R₁ : Fin T → List (Fin (A+4))} {c : ℕ}
    (h : LayRuns body p R₀ R₁ c) (R : Fin T' → List (Fin (A+4))) (hR : R ∘ e=R₀) :
    LayRuns body' (embProg e ι p) R (embExt e R₁ R) c := by
  intro v S hL hS
  obtain ⟨w,k,hu,hk,hex⟩ := h (embDn e v) (embStk e S)
    (fun i => hL (e i)) (by change S.R ∘ e=R₀; rw [hS]; exact hR)
  obtain ⟨v',hv,hu',hex'⟩ := exec_emb_ovr he hbody hex v rfl S rfl
  refine ⟨v',k,hu'.trans hu,hk,Exec.cast hex' rfl ?_⟩
  apply congrArg (mk v')
  simp only [embOvr,embStk,Stacks.get,embExt_comp,hS]

theorem compactMainStage_runs (legacy : MnProc → MnPr A)
    (native : LProc → CompactMnPr CompactMainProc A)
    {p : MnPr A} {R₀ R₁ : Fin mnT → List (Fin (A+4))} {c : ℕ}
    (h : LayRuns legacy p R₀ R₁ c)
    (R : Fin compactMnT → List (Fin (A+4))) (hR : R ∘ compactMnLegacyReg=R₀) :
    LayRuns (compactMainTransportTable legacy native) (compactMainStage p) R
      (embExt compactMnLegacyReg R₁ R) (1+c) := by
  unfold compactMainStage
  with_reducible
    exact placedNormalizedRuns compactMnLegacyReg compactMnLegacyReg_injective
      compactMnQ_legacy mnQ_pos compactMainOldProc (compactMainTransportTable_old legacy native) h R hR

/-- Place a local legacy layer execution in the old main table. -/
theorem compactOldLayer_runs (legacy : MnProc → MnPr A)
    (localBody : LProc → Pr LProc (nT SXReg) mnQ A Unit)
    (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (localBody f))
    {p : Pr LProc (nT SXReg) mnQ A Unit}
    {R₀ R₁ : Fin (nT SXReg) → List (Fin (A+4))} {c : ℕ}
    (h : LayRuns localBody p R₀ R₁ c)
    (R : Fin mnT → List (Fin (A+4))) (hR : R ∘ mnLayE=R₀) :
    LayRuns legacy (embProg mnLayE MnProc.lay p) R (embExt mnLayE R₁ R) c := by
  with_reducible exact placedRuns mnLayE mnLayE_inj MnProc.lay hbody h R hR

/-- An old local layer contract is executable after compact code without any
assumption on the current finite control state. -/
theorem compactLegacyLayer_runs (legacy : MnProc → MnPr A)
    (native : LProc → CompactMnPr CompactMainProc A)
    (localBody : LProc → Pr LProc (nT SXReg) mnQ A Unit)
    (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (localBody f))
    {p : Pr LProc (nT SXReg) mnQ A Unit}
    {R₀ R₁ : Fin (nT SXReg) → List (Fin (A+4))} {c : ℕ}
    (h : LayRuns localBody p R₀ R₁ c)
    (R : Fin compactMnT → List (Fin (A+4)))
    (hR : (R ∘ compactMnLegacyReg) ∘ mnLayE=R₀) :
    LayRuns (compactMainTransportTable legacy native)
      (compactMainStage (embProg mnLayE MnProc.lay p)) R
      (embExt compactMnLegacyReg (embExt mnLayE R₁ (R ∘ compactMnLegacyReg)) R) (1+c) :=
  compactMainStage_runs legacy native
    (compactOldLayer_runs legacy localBody hbody h (R ∘ compactMnLegacyReg) hR) R rfl

end
end IntegerMultBounds.MathlibTM2.Fast.Main
