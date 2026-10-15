module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRoundFrame
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformHybridRound

/-! Named runtime geometry and the exact cost/contract of the actual hybrid layer step. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.MathlibTM2.Cost
open CompactGadgetReservationCapacity
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Ka : ℕ}

structure CompactSynUniformGeometry (M K : ℕ) (es : List ℕ) (ℓ W l p : ℕ) : Prop where
  chunkLower : Mult.Sizes.K M≤K
  chunkUpper : K≤Mult.Sizes.d M
  depth : 0<Mult.Sizes.d M
  layout : LayHyp es ℓ K
  reservation : CompactReservationFits (Mult.Sizes.d M) (CompactReservationGrowth.guard M) K es.length
  dimension : es.length≤Mult.Sizes.d M
  precision : es.sum+1≤Mult.Sizes.p M
  multiplicity : Mult.Sizes.r M≤2^l
  width : Mult.Sizes.p M≤W
  numerator : p+2≤W

def compactSynUniformLayerCost (ds : ComplexFramedExecution.Directions) (M K : ℕ)
    (es : List ℕ) (ℓ W l h stk : ℕ) : ℕ :=
    let d := Mult.Sizes.d M
    let g := CompactReservationGrowth.guard M
    let D := es.length
    let o := K*((h-layB ℓ K)/K*D)
    let ρ := (h-layB ℓ K)%K
    let r := 2^l
    let n := o+K*(D-CompactGlobalRowPadding.rowAxes NW m d)
    let a := es.sum-n
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
    compactSynDispatchCost ℓ K h+(if synChunk ℓ K h then
        (compactSynLayerRoundOverhead (gateCount (program ds)) (factorCount (program ds))
        es.sum d g K D o W r h (layB ℓ K) ρ working
        (topRec pfs : List (Fin (prime+Ka+4))).length (topRec cfg : List (Fin (prime+Ka+4))).length
        stk+
        compactTopCost W working s n a 1 r K ρ q aT o D R₂ pcs
          (compactTopCallCost ds shape 1 (n+a) o r working ρ ⟨0,q,1,aT⟩)
          (compactTopCallCost ds shape 1 n o r working ρ)) else
          1+synLayerStepCost ds es ℓ K W l h stk)

/-- A uniform contract for the concrete executable dispatch, with its actual cost. -/
def CompactSynUniformLayerContract (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions) (M K : ℕ) (es : List ℕ) (ℓ W l p : ℕ) : Prop :=
  ∀ (h : ℕ),h+1≤ℓ → ∀ (v : SynW → List (Fin (prime+Ka+4))),
    SynV v es ℓ K W l h (layPerm es ℓ K) →
    ∀ (P₀ : List (Fin (prime+Ka+4))) (Y : ℕ → Fin (2^l) → GaussianInt),
    (∀ x c,‖GaussianInt.toComplex (Y x c)‖≤2^p) →
    ∀ (R : Fin compactMnT → List (Fin (prime+Ka+4))),
    compactSynView R=synG (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Y)) P₀) v →
    CompactSynReady R M →
    LayRuns (compactMainBody legacy ds) (compactSynDispatch ds) R
      (Function.update R (compactMnRg (.src (.v .io))) (cstream (prime+Ka) W (rpStream (2^es.sum)
        (synTrunc (bflyL ((selBits es h).map (twPosL (layPerm es ℓ K)))
          (fun x c => GaussianInt.toComplex (Y x c)))))))
      (compactSynUniformLayerCost (Ka := Ka) ds M K es ℓ W l h (synStashCostW v synXS))

theorem compactSynUniformLayerContract_eventually (hA : 21≤prime+Ka)
    (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4) :
    ∀ᶠ M : ℕ in Filter.atTop,
    ∀ (ds : ComplexFramedExecution.Directions),ComplexPhaseBudget.Realizes ds →
      (∀ g,Instr.gate g∈program ds → (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4) →
    ∀ (legacy : MnProc → MnPr (prime+Ka)),
      (∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f)) →
    ∀ (es : List ℕ) (K ℓ W l p : ℕ),CompactSynUniformGeometry M K es ℓ W l p →
      CompactSynUniformLayerContract legacy ds M K es ℓ W l p := by
  filter_upwards [compactSynDispatch_uniform_eventually_exec_stream hA hA9 hNW] with M hexec
  intro ds hd hgate legacy hbody es K ℓ W l p hg h hh v hv P₀ Y hY R hR hr
  have he := hexec ds hd hgate legacy hbody es K ℓ W l h p hg.chunkLower hg.chunkUpper hg.depth hg.layout.K_pos hg.layout hh
    (fun _ => hg.reservation) hg.dimension hg.precision hg.multiplicity hg.width hg.numerator
    v hv P₀ Y hY R hR
    (by simpa only [compactMnLayerReg_private] using hr.blank)
    (by simpa only [compactMnLayerReg_private] using hr.depth)
    (by simpa only [compactMnLayerReg_private] using hr.guard)
  exact he

end
end IntegerMultBounds.MathlibTM2.Fast.Main
