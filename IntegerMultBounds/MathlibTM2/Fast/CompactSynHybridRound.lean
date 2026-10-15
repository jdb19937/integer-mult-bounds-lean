module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepStream
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynDirect
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynMainProjection
public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerSelectedRows

/-! A whole actual chunk round, from existing synthetic state and initialized
original globals, through the real compact top, back to the original register file. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.Rounds
open CompactGadgetReservationCapacity
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Ka : ℕ}
open Filter

theorem compactSynDispatch_eventually_exec_stream
    (hA : 21≤prime+Ka) (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4) :
    ∀ᶠ M : ℕ in atTop,
    ∀ (ds : ComplexFramedExecution.Directions) (hd : ComplexPhaseBudget.Realizes ds)
      (hgate : ∀ g,Instr.gate g∈program ds → (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4)
      (legacy : MnProc → MnPr (prime+Ka))
      (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay
        (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
      (es : List ℕ) (ℓ W l h p : ℕ),
    let d := Mult.Sizes.d M
    let g := CompactReservationGrowth.guard M
    let K := Mult.Sizes.K M
    let D := es.length
    let o := K*((h-layB ℓ K)/K*D)
    let ρ := (h-layB ℓ K)%K
    let r := 2^l
    let n := o+K*(D-CompactGlobalRowPadding.rowAxes NW m d)
    let a := es.sum-n
    ∀ (hdpos : 0<d) (hKpos : 1≤K) (H : LayHyp es ℓ K) (hh : h+1≤ℓ)
      (hcap : synChunk ℓ K h → CompactReservationFits d g K D) (hD : D≤d)
      (hprecision : es.sum+1≤Mult.Sizes.p M)
      (hrun : Mult.Sizes.r M≤r) (hwrun : Mult.Sizes.p M≤W) (hW : p+2≤W),
    let q := compactTopKernelCount d g K
    let aT := compactTopKernelOffset d g K D o
    let R₂ := compactTopRows d 1 a
    let s := (D+1)/2+q+(backChunks d g K+
      synE (gateCount (program ds)) (factorCount (program ds))
        (compactReservationActive d g K D) (compactReservationActive d g K D))
    let working := W+s+D
    let shape := compactReservationShape d g K D (2^o*(3*(r*working)))
    let pcs := compactTopPcs d g K D o R₂
    let cfg := topCfg W s a 1 R₂ q aT K o D
    let pfs := topPcRec K pcs
    ∀ (v : SynW → List (Fin (prime+Ka+4)))
      (hv : SynV v es ℓ K W l h (layPerm es ℓ K)) (P₀ : List (Fin (prime+Ka+4)))
      (Y : ℕ → Fin r → GaussianInt)
      (hY : ∀ x c,‖GaussianInt.toComplex (Y x c)‖≤2^p)
      (R : Fin compactMnT → List (Fin (prime+Ka+4)))
      (hlegacy : (R ∘ compactMnLegacyReg) ∘ mnLayE=synG (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Y)) P₀) v)
      (hblank : ∀ z : CompactBReg,z≠.work 13 → z≠.work 14 →
        R (compactMnLayerReg (reg (BReg := CompactHostBReg) (.bc (.inl z))))=[])
      (hdepth : (R (compactMnLayerReg (reg (BReg := CompactHostBReg) (.bc (.inl (.work 13)))))).length=d)
      (hguard : (R (compactMnLayerReg (reg (BReg := CompactHostBReg) (.bc (.inl (.work 14)))))).length=g),
    LayRuns (compactMainBody legacy ds) (compactSynDispatch ds) R
      (Function.update R (compactMnRg (.src (.v .io))) (cstream (prime+Ka) W (rpStream (2^es.sum) (synTrunc
        (bflyL ((selBits es h).map (twPosL (layPerm es ℓ K)))
          (fun x c => GaussianInt.toComplex (Y x c)))))))
      (compactSynDispatchCost ℓ K h+(if synChunk ℓ K h then
        (compactSynLayerRoundOverhead (gateCount (program ds)) (factorCount (program ds))
        es.sum d g K D o W r h (layB ℓ K) ρ working
        (topRec pfs : List (Fin (prime+Ka+4))).length (topRec cfg : List (Fin (prime+Ka+4))).length
        (synStashCostW v synXS)+
        compactTopCost W working s n a 1 r K ρ q aT o D R₂ pcs
          (compactTopCallCost ds shape 1 (n+a) o r working ρ ⟨0,q,1,aT⟩)
          (compactTopCallCost ds shape 1 n o r working ρ)) else
          1+synLayerStepCost ds es ℓ K W l h (synStashCostW v synXS))) := by
  filter_upwards [compactSynLayerStep_eventually_exec_stream (Ka := Ka) (U := Unit)
    compactMnQ_runtime hA hA9 hNW] with M hexec
  intro ds hd hgate legacy hbody es ℓ W l h p
  dsimp only
  intro hdpos hKpos H hh hcap hD hprecision hrun hwrun hW
  intro v hv P₀ Y hY R hlegacy hblank hdepth hguard
  have hwire (x : SynW) : R (compactSynDispatchReg x)=v x := by
    change (((R ∘ compactMnLegacyReg) ∘ mnLayE) (sreg x))=v x
    rw [hlegacy,synG_sreg]
  apply compactSynDispatchWith_runs (compactMainBody legacy ds) hv hwire
  · intro hc
    have haddr := synChunk_fit H hc
    simp only [synOS,hc.1,ite_true,Nat.not_lt.mpr hc.2,ite_false] at haddr
    have hfit := (Nat.le_add_right _ _).trans haddr
    have ha := compactCaller_selected_split (hcap hc) hfit
    have hproj : (R ∘ compactMnLayerReg) ∘ compactLegacyReg=
        synG (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Y)) P₀) v := by
      rw [←hlegacy]
      funext i
      exact congrArg R (compactMnLayerReg_legacy i)
    have e := hexec ds hd hgate es ℓ W l h p hdpos hKpos hc H (hcap hc) hD
      hfit (by rw [ha]; omega) hprecision hrun hwrun hW v (layPerm es ℓ (Mult.Sizes.K M))
      hv P₀ Y hY (R ∘ compactMnLayerReg) hproj hblank hdepth hguard
    exact compactMainChunk_runs legacy ds (R ∘ compactMnLayerReg) R _ _ rfl e
  · intro _
    exact compactMainDirect_runs legacy ds hd hbody (by omega) hA9 hNW hgate H hh hW v hv P₀ Y hY R hlegacy

end
end IntegerMultBounds.MathlibTM2.Fast.Main
