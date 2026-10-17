module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapRead
public import IntegerMultBounds.MathlibTM2.Node.CompactGlobalBootstrap
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Execute the original-input bootstrap on the expanded main host. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

private theorem compactMainBootstrap_output
    (v : SynW → List (Fin (A+4))) (p d : ℕ)
    (h6 : v (.s 6)=[]) (h15 : v (.s 15)=[]) (h26 : v (.s 26)=[]) :
    Function.update (Function.update (Function.update (Function.update v
      (.s 19) (List.replicate (4*Nat.clog 2 p+6) tick)) (.s 18) (List.replicate d tick))
      (.s 0) []) (.s 1) [] =
    compactSetupUpdate7 v compactGlobalBootstrapSource (compactGlobalBootstrapValues p d) := by
  funext z
  by_cases h6z : z=.s 6
  · subst z; simp [compactSetupUpdate7,compactGlobalBootstrapSource,compactGlobalBootstrapValues,h6]
  by_cases h15z : z=.s 15
  · subst z; simp [compactSetupUpdate7,compactGlobalBootstrapSource,compactGlobalBootstrapValues,h15]
  by_cases h26z : z=.s 26
  · subst z; simp [compactSetupUpdate7,compactGlobalBootstrapSource,compactGlobalBootstrapValues,h26]
  simp [compactSetupUpdate7,compactGlobalBootstrapSource,compactGlobalBootstrapValues,
    Function.update_of_ne,h6z,h15z,h26z]

private theorem compactMainBootstrap_counts
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (p d : ℕ) (hp : 2≤p) (h0 : (v (.s 0)).length=p) (h1 : (v (.s 1)).length=d)
    (hz : ∀ i : Fin 32,i∈[2,6,9,10,12,15,17,18,19,23,26] → v (.s i)=[]) :
    LayRuns (fun f : Empty => f.elim) (compactGlobalBootstrapCounts (Q:=Q) (U:=U)) (synG R v)
      (compactSetupUpdate7 (synG R v) (sreg ∘ compactGlobalBootstrapSource) (compactGlobalBootstrapValues p d))
      (compactGlobalBootstrapCost p d) := by
  have h := sg_compactGlobalBootstrapCounts (Q:=Q) (A:=A) (U:=U) (fun f : Empty => f.elim)
    R v p d hp h0 h1 (fun i hi => hz i (by simp only [List.mem_cons] at hi ⊢; tauto))
  have hout := (congrArg (synG R) (compactMainBootstrap_output v p d
    (hz 6 (by simp)) (hz 15 (by simp)) (hz 26 (by simp)))).trans
    (compactSetupUpdate7_map (synG R) sreg (fun v x l => (synG_update (R:=R) (v:=v) x l).symm)
      v compactGlobalBootstrapSource (compactGlobalBootstrapValues p d))
  rw [hout] at h
  exact h

/-- Compose a source read and seven-output setup without reducing a concrete bank cardinality. -/
private theorem compactReadSetup7_exec {T T' : ℕ}
    (e : Fin T → Fin T') (he : Function.Injective e) (body : P → Pr P T' Q A U)
    {read : Pr P T' Q A U} {R₀ R₁ : Fin T' → List (Fin (A+4))} {c₁ : ℕ}
    (hread : LayRuns body read R₀ R₁ c₁)
    {setup : Pr Empty T Q A U} {R : Fin T → List (Fin (A+4))}
    {src : Fin 7 → Fin T} {values : Fin 7 → ℕ} {c₂ : ℕ}
    (hsetup : LayRuns (fun f : Empty => f.elim) setup R (compactSetupUpdate7 R src values) c₂)
    (v : HS T' Q A U) (S : Stacks T' A) (hL : ∀ i,S.L i=[])
    (hR : S.R=R₀) (hview : R₁ ∘ e=R) :
    ∃ v' steps,v'.user=v.user ∧ steps≤c₁+c₂ ∧
      Exec body (.seq read (embProg e (fun f : Empty => f.elim) setup)) (mk v S) steps
        (mk v' {S with R:=compactSetupUpdate7 R₁ (e ∘ src) values}) := by
  obtain ⟨v₁,n₁,hu₁,hc₁,he₁⟩ := hread v S hL hR
  obtain ⟨v₂,n₂,hu₂,hc₂,he₂⟩ := compactSetup7_exec e he body hsetup v₁ {S with R:=R₁}
    (fun i => hL (e i)) hview
  exact ⟨v₂,n₁+n₂,hu₂.trans hu₁,by omega,Exec.seq he₁ he₂⟩

def compactMnBootstrapReg := compactMnLayerReg ∘ compactBasisSetupReg

def compactMnBootstrapDst := compactMnBootstrapReg ∘ (sreg ∘ compactGlobalBootstrapSource)

def compactMnBootstrap : Pr P compactMnT Q A U :=
  .seq compactMnBootstrapRead
    (embProg compactMnBootstrapReg (fun f : Empty => f.elim) (compactGlobalBootstrapCounts (P:=Empty)))

def compactMnBootstrapCost (p d : ℕ) := ((4*p+4)+(4*d+4))+compactGlobalBootstrapCost p d

/-- The read sources are actual original precision and initial transform depth.
The view premise describes the file after these two charged copies, not preinitialized inputs. -/
theorem compactMnBootstrap_exec (body : P → Pr P compactMnT Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (p d : ℕ) (hp : 2≤p) (h0 : (v (.s 0)).length=p) (h1 : (v (.s 1)).length=d)
    (hz : ∀ i : Fin 32,i∈[2,6,9,10,12,15,17,18,19,23,26] → v (.s i)=[])
    (vbig : HS compactMnT Q A U) (S : Stacks compactMnT A) (hL : ∀ i,S.L i=[])
    (hpSource : (S.R (compactMnRg (.io .dpn))).length=p)
    (hdSource : (S.R (compactMnLayerReg (compactLegacyReg (sreg (.p .D))))).length=d)
    (hblank0 : S.R (compactMnSyn (.s 0))=[]) (hblank1 : S.R (compactMnSyn (.s 1))=[])
    (hblank2 : S.R (compactMnSyn (.s 2))=[])
    (hview : compactMnBootstrapCopied S.R p d ∘ compactMnBootstrapReg=synG R v) :
    ∃ v' steps,v'.user=vbig.user ∧ steps≤compactMnBootstrapCost p d ∧
      Exec body compactMnBootstrap (mk vbig S) steps
        (mk v' {S with R:=(compactSetupUpdate7 (compactMnBootstrapCopied S.R p d)
          compactMnBootstrapDst (compactGlobalBootstrapValues p d))}) :=
  compactReadSetup7_exec compactMnBootstrapReg
    (compactMnLayerReg_injective.comp compactBasisSetupReg_injective) body
    (compactMnBootstrapRead_runs body S.R p d hpSource hdSource hblank0 hblank1 hblank2)
    (compactMainBootstrap_counts R v p d hp h0 h1 hz) vbig S hL rfl hview

end
end IntegerMultBounds.MathlibTM2.Fast.Main
