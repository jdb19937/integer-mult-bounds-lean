module

import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapPipelineFrame
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapFrame
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! One bootstrap per initialized transform, carrying original depth across its rounds. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

private theorem bootstrapAppendPush {T : ℕ} (body : P → Pr P T Q A U)
    (prog : Pr P T Q A U) (x : Fin T) (v : HS T Q A U) (S : Stacks T A)
    (R : Fin T → List (Fin (A+4))) (c : ℕ) (hL : ∀ i,S.L i=[])
    (h : ∃ v' steps,v'.user=v.user ∧ steps≤c ∧
      Exec body prog (mk v S) steps (mk v' {S with R:=R})) :
    ∃ v' steps,v'.user=v.user ∧ steps≤c+1 ∧
      Exec body (.seq prog (synPush x tick)) (mk v S) steps
        (mk v' {S with R:=Function.update R x (tick::R x)}) := by
  obtain ⟨v₁,n₁,hu₁,hc₁,he₁⟩ := h
  obtain ⟨v₂,n₂,hu₂,hc₂,he₂⟩ := lr_push body (R:=R) x tick v₁ {S with R:=R} hL rfl
  exact ⟨v₂,n₁+n₂,hu₂.trans hu₁,by omega,Exec.seq he₁ he₂⟩

/-- Run once after distribution initializes `.p.D = d-1`, before the first round. -/
def compactMnOriginalBootstrap : Pr P compactMnT Q A U :=
  .seq compactMnBootstrap (synPush (compactMnLay (.bc (.inl (.work 13)))) tick)

def compactMnOriginalBootstrapCost (p d : ℕ) := compactMnBootstrapCost p (d-1)+1

/-- Compose the charged source-copy bootstrap with the one-tick original-depth correction. -/
theorem compactMnOriginalBootstrap_exec (body : P → Pr P compactMnT Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (p d : ℕ) (hp : 2≤p) (hd : 0<d)
    (h0 : (v (.s 0)).length=p) (h1 : (v (.s 1)).length=d-1)
    (hz : ∀ i : Fin 32,i∈[2,6,9,10,12,15,17,18,19,23,26] → v (.s i)=[])
    (vbig : HS compactMnT Q A U) (S : Stacks compactMnT A) (hL : ∀ i,S.L i=[])
    (hpSource : (S.R (compactMnRg (.io .dpn))).length=p)
    (hdSource : (S.R (compactMnLayerReg (compactLegacyReg (sreg (.p .D))))).length=d-1)
    (hblank0 : S.R (compactMnSyn (.s 0))=[]) (hblank1 : S.R (compactMnSyn (.s 1))=[])
    (hblank2 : S.R (compactMnSyn (.s 2))=[])
    (hview : compactMnBootstrapCopied S.R p (d-1) ∘ compactMnBootstrapReg=synG R v) :
    ∃ v' steps,v'.user=vbig.user ∧ steps≤compactMnOriginalBootstrapCost p d ∧
      Exec body compactMnOriginalBootstrap (mk vbig S) steps
        (mk v' {S with R:=compactMnBootstrapFinal S.R p d}) := by
  have hb := compactMnBootstrap_exec body R v p (d-1) hp h0 h1 hz vbig S hL
    hpSource hdSource hblank0 hblank1 hblank2 hview
  have h := bootstrapAppendPush body compactMnBootstrap
    (compactMnLay (.bc (.inl (.work 13)))) vbig S
    (compactMnBootstrapFinal S.R p (d-1)) (compactMnBootstrapCost p (d-1)) hL hb
  rw [compactMnBootstrap_original_depth_file S.R p d hd] at h
  exact h

end
end IntegerMultBounds.MathlibTM2.Fast.Main
