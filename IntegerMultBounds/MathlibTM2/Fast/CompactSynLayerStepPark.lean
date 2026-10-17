module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepWires
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRoundPark
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRoundRest
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepFrame
import IntegerMultBounds.MathlibTM2.Fast.CompactSynRoundCompose
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Concrete rest setup and parking for a prepared compact round. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

def compactSynLayerPark : Pr P (nT CompactHostBReg) Q A U :=
  .seq compactSynRestUp (.seq compactSynStash compactSynPushCfg)

theorem compactSynLayerPark_placed (body : P → Pr P (nT CompactHostBReg) Q A U)
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (N r working K ρ : ℕ) (pr : List (Fin (A+4))) (cfg : List ℕ)
    (hRo : ∀ x ∈ [LReg.ctr, .cS, .cR, .ph .rc, .ph .wc, .ph .af, .lf (.k .rctr), .lf (.k .wctr),
      .lf (.k .cf), .rowctr, .n, .w, .rw, .K, .ρ, .ph .arr], Ro (lreg x) = [])
    (hw2 : v (.p .w2)=List.replicate working tick) (hN : (v (.p .N)).length=N)
    (hr : (v (.p .r)).length=r) (hkh : v (.p .kh)=List.replicate K tick)
    (hrh : v (.p .rh)=List.replicate ρ tick) (hpr : v (.p .pr)=pr)
    (h2 : v (.s 2)=[]) (h3 : v (.s 3)=[]) (h4 : v (.s 4)=[])
    (hcf : v (.p .cf)=(topRec cfg).reverse) :
    let RF := synRestFile Ro N r working K ρ pr
    let v₂ := compactSynRaisedW v
    let park := synStkW v₂ blank synXS ++ blank :: RF (lreg .park)
    CompactPlacedRuns body compactSynLayerPark (synG Ro v)
      (synG (Function.update (Function.update RF (lreg .park) park) (lreg .park) (topRec cfg ++ park))
        (Function.update (synClrW v₂ synXS) (.p .cf) []))
      (synRestUpCost N r working K ρ pr.length+
        ((synStashCostW v₂ synXS+1)+(2*(topRec cfg : List (Fin (A+4))).length+2))) := by
  dsimp only
  let RF := synRestFile Ro N r working K ρ pr
  let v₂ := compactSynRaisedW v
  have e₁ := compactSynRestUp_runs body Ro v N r working K ρ pr hRo hw2 hN hr hkh hrh hpr h2 h3 h4
  have e₂ := compactSynStash_runs body RF v₂
  have e₃ := compactSynPushCfg_runs body
    (Function.update RF (lreg .park) (synStkW v₂ blank synXS ++ blank :: RF (lreg .park)))
    (synClrW v₂ synXS) cfg
    (by simp [v₂,compactSynRaisedW,synClrW,synXS,hcf])
  simpa only [Function.update_self,compactSynLayerPark] using e₁.seq (e₂.seq e₃)

/-- All temporary wires are blank when control reaches the actual top program. -/
theorem compactSynLayerPark_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K W l h : ℕ) (L : Equiv.Perm (Fin es.sum))
    (hv : SynV v es ℓ K W l h L) (ρ working : ℕ) (pr : List (Fin (A+4)))
    (cfg : List ℕ) (io P₀ : List (Fin (A+4)))
    (hR : R ∘ compactLegacyReg=synG (synIdle io P₀)
      (compactSynPreparedW v K ρ working pr (topRec cfg).reverse)) :
    LayRuns body compactSynLayerPark R
      (embExt compactLegacyReg
        (synG (synRestFile (synIdle io
          (topRec cfg ++ (synStkW v blank synXS ++ blank :: P₀))) es.sum (2^l) working K ρ pr)
          (fun _ => [])) R)
      (synRestUpCost es.sum (2^l) working K ρ pr.length+
        ((synStashCostW v synXS+1)+(2*(topRec cfg : List (Fin (A+4))).length+2))) := by
  let v₁ := compactSynPreparedW v K ρ working pr (topRec cfg).reverse
  let v₂ := compactSynRaisedW v₁
  let RF := synRestFile (synIdle io P₀) es.sum (2^l) working K ρ pr
  have hv₂ : v₂=Function.update v (.p .cf) (topRec cfg).reverse :=
    compactSynRaised_prepared v K ρ working pr _ hv.hkh hv.hrh hv.hpr hv.hw2
  have hX (x : SynW) (hx : x∈synXS) : v₂ x=v x :=
    compactSynRaised_prepared_synXS v K ρ working pr _ x hx
  have ep := (compactSynLayerPark_placed body (synIdle io P₀) v₁ es.sum (2^l) working K ρ pr cfg
    (synIdle_rest io P₀)
    (by simp [v₁,compactSynPreparedW])
    (by simp [v₁,compactSynPreparedW,hv.hN])
    (by simp [v₁,compactSynPreparedW,hv.hr])
    (by simp [v₁,compactSynPreparedW])
    (by simp [v₁,compactSynPreparedW])
    (by simp [v₁,compactSynPreparedW])
    (by simp [v₁,compactSynPreparedW,hv.hs])
    (by simp [v₁,compactSynPreparedW,hv.hs])
    (by simp [v₁,compactSynPreparedW,hv.hs])
    (by simp [v₁,compactSynPreparedW])).layRuns R hR
  have hpark : RF (lreg .park)=P₀ := by
    simp [RF,synRestFile,synIdle,lreg]
  have hst : synStkW v₂ blank synXS=synStkW v blank synXS := synStkW_congr blank synXS hX
  have hempty : Function.update (synClrW v₂ synXS) (.p .cf) []=(fun _ => []) := by
    funext x
    rw [hv₂]
    exact compactSynParkedW_empty v es ℓ K W l h L hv _ x
  dsimp only [RF] at hpark
  dsimp only [v₂] at hst hempty hX
  rw [Function.update_idem,hpark,hst,hempty,synStashCostW_congr synXS hX] at ep
  have hup (X : List (Fin (A+4))) : Function.update RF (lreg .park) X=
      synRestFile (synIdle io X) es.sum (2^l) working K ρ pr := by
    dsimp only [RF]
    rw [synRestFile_update (by simp),synIdle_update_park]
  dsimp only [RF] at hup
  rw [hup] at ep
  simpa only [compactSynLayerPark] using ep

end
end IntegerMultBounds.MathlibTM2.Fast
