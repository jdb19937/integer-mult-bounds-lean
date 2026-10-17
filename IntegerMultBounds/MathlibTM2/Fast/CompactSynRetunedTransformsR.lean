module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRoundOpR
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynTransformR
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRetunedTransforms

/-! The rounded forward and opposite transforms at every uniform chunk width, then at the
retuned sizes: `SynFwdSpecQ`, `SynOppSpecQ` with the computed rounds `compactSynFOp`,
`compactSynOOp`. All hypotheses of the rounded rounds come from the uniform geometry. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.MathlibTM2.Mult.SynthErr
open IntegerMultBounds.NLogN IntegerMultBounds.Spec.SignedRingProduct
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Ka : ℕ}

open Filter

theorem compactSynUniformFwdR_eventually (hA : 21≤prime+Ka)
    (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4) :
    ∀ᶠ M : ℕ in atTop,
    ∀ (ds : ComplexFramedExecution.Directions) (hd : ComplexPhaseBudget.Realizes ds),
      (∀ g,Instr.gate g∈program ds → (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4) →
    ∀ (legacy : MnProc → MnPr (prime+Ka))
  (_hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
  (K d ℓ W l p : ℕ) (a : Fin d → ℕ)
  (hg : CompactSynUniformGeometry M K (List.ofFn a) ℓ W l p) (_hAl : nRounds a≤l+1)
  (v₀ : SynW → List (Fin (prime+Ka+4)))
  (_hv₀ : SynV v₀ (List.ofFn a) ℓ K W l 0 (layPerm (List.ofFn a) ℓ K))
  (_hvh : v₀ (.p .h)=[]) (_hvt : v₀ (.p .t)=[]) (_hvc : (v₀ (.p .c)).length=nRounds a)
  (_hcb : blank∉v₀ (.p .c)) (Pk : List (Fin (prime+Ka+4)) → Prop)
  (layP : Pr LProc (nT SXReg) mnQ (prime+Ka) Unit) (cL : ℕ)
  (_hLay : ∀ park,Pk park → ∀ Z : ℕ → Fin (2^l) → GaussianInt,
    LayRuns (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds) layP
      (synG (synIdle (cstream (prime+Ka) W (rpStream (cvM a) Z)) park) v₀)
      (synG (synIdle (cstream (prime+Ka) W (rpStream (cvM a)
        (fun m => Z (synPi (layPerm (List.ofFn a) ℓ K) m)))) park) v₀) cL),
    SynFwdSpecQ (compactMainBodyR legacy ds) (compactSynFwdR ds layP) (compactMnRg (.src (.v .io)))
      (compactSynPre M Pk v₀) W p l a (synPi (layPerm (List.ofFn a) ℓ K))
      (compactSynFOp ds hd M K (List.ofFn a) ℓ W l p hg.layout hg.numerator hg.reservation hg.dimension)
      (compactMnOriginalBootstrapCost (Mult.Sizes.p M) (Mult.Sizes.d M)+
        (((1+cL)+compactSynLoopFCostR (Ka := Ka) ds M K (List.ofFn a) ℓ W l (nRounds a)
        (synStashCostW v₀ synXS+6*nRounds a+6))+((2*Mult.Sizes.d M+2)+(2*(4*Nat.clog 2 (Mult.Sizes.p M)+6)+2)))) := by
  filter_upwards [eventually_ge_atTop 2,compactSynUniformLoopsContractR_eventually hA hA9 hNW]
    with M hM hloops
  intro ds hd hgate legacy hbody K d ℓ W l p a hg hAl v₀ hv₀ hvh hvt hvc hcb Pk lay cL hLay
  have hp : 2≤Mult.Sizes.p M := by
    have hb := Mult.Sizes.one_le_b hM
    unfold Mult.Sizes.p
    omega
  have haddr : ∀ h,synChunk ℓ K h → K*((h-layB ℓ K)/K*(List.ofFn a).length)+K*(List.ofFn a).length≤(List.ofFn a).sum := by
    intro h hc
    have := synChunk_fit hg.layout hc
    simp only [synOS,hc.1,ite_true,Nat.not_lt.mpr hc.2,ite_false] at this
    omega
  have hfits := compactSynFitsR_of ds hd M K (List.ofFn a) ℓ W l p hg.numerator haddr
  have hinv := compactSynInvR_of ds hd M K (List.ofFn a) ℓ W l p hg.layout hg.numerator hg.reservation hg.dimension
  have hLoop := hloops ds hd hgate legacy hbody (List.ofFn a) K ℓ W l p hg hfits true
  exact compactSynFwdR_spec legacy ds hbody a hg.layout hAl hLoop hinv _ (fun _ _ => rfl) v₀ hv₀ hvh hvt hvc hcb
    Pk lay cL hLay hM hp hg.depth

theorem compactSynUniformOppR_eventually (hA : 21≤prime+Ka)
    (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4) :
    ∀ᶠ M : ℕ in atTop,
    ∀ (ds : ComplexFramedExecution.Directions) (hd : ComplexPhaseBudget.Realizes ds),
      (∀ g,Instr.gate g∈program ds → (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4) →
    ∀ (legacy : MnProc → MnPr (prime+Ka))
  (_hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
  (K d ℓ W l p : ℕ) (a : Fin d → ℕ)
  (hg : CompactSynUniformGeometry M K (List.ofFn a) ℓ W l p) (_hAl : nRounds a≤l+1)
  (v₀ : SynW → List (Fin (prime+Ka+4)))
  (_hv₀ : SynV v₀ (List.ofFn a) ℓ K W l 0 (layPerm (List.ofFn a) ℓ K))
  (_hvh : v₀ (.p .h)=[]) (_hvt : v₀ (.p .t)=[]) (_hvc : (v₀ (.p .c)).length=nRounds a)
  (_hcb : blank∉v₀ (.p .c)) (Pk : List (Fin (prime+Ka+4)) → Prop)
  (layQ : Pr LProc (nT SXReg) mnQ (prime+Ka) Unit) (cL : ℕ)
  (_hLay : ∀ park,Pk park → ∀ Y : ℕ → Fin (2^l) → GaussianInt,
    LayRuns (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds) layQ
      (synG (synIdle (cstream (prime+Ka) W (rpStream (cvM a) Y)) park) v₀)
      (synG (synIdle (cstream (prime+Ka) W (rpStream (cvM a)
        (fun x => Y ((layRec (layPerm (List.ofFn a) ℓ K))
          ⟨x % 2^(List.ofFn a).sum,Nat.mod_lt _ (by positivity)⟩)))) park) v₀) cL),
    SynOppSpecQ (compactMainBodyR legacy ds) (compactSynOppR ds layQ) (compactMnRg (.src (.v .io)))
      (compactSynPre M Pk v₀) W p l a (synPi (layPerm (List.ofFn a) ℓ K))
      (compactSynOOp ds hd M K (List.ofFn a) ℓ W l p hg.layout hg.numerator hg.reservation hg.dimension)
      (compactMnOriginalBootstrapCost (Mult.Sizes.p M) (Mult.Sizes.d M)+
        ((compactSynLoopOCostR (Ka := Ka) ds M K (List.ofFn a) ℓ W l (nRounds a)
        (synStashCostW v₀ synXS+6*nRounds a+6)+(1+cL))+((2*Mult.Sizes.d M+2)+(2*(4*Nat.clog 2 (Mult.Sizes.p M)+6)+2)))) := by
  filter_upwards [eventually_ge_atTop 2,compactSynUniformLoopsContractR_eventually hA hA9 hNW]
    with M hM hloops
  intro ds hd hgate legacy hbody K d ℓ W l p a hg hAl v₀ hv₀ hvh hvt hvc hcb Pk lay cL hLay
  have hp : 2≤Mult.Sizes.p M := by
    have hb := Mult.Sizes.one_le_b hM
    unfold Mult.Sizes.p
    omega
  have haddr : ∀ h,synChunk ℓ K h → K*((h-layB ℓ K)/K*(List.ofFn a).length)+K*(List.ofFn a).length≤(List.ofFn a).sum := by
    intro h hc
    have := synChunk_fit hg.layout hc
    simp only [synOS,hc.1,ite_true,Nat.not_lt.mpr hc.2,ite_false] at this
    omega
  have hfits := compactSynFitsR_of ds hd M K (List.ofFn a) ℓ W l p hg.numerator haddr
  have hinv := compactSynInvR_of ds hd M K (List.ofFn a) ℓ W l p hg.layout hg.numerator hg.reservation hg.dimension
  have hLoop := hloops ds hd hgate legacy hbody (List.ofFn a) K ℓ W l p hg hfits false
  exact compactSynOppR_spec legacy ds hbody a hg.layout hAl hLoop hinv _ (fun _ _ => rfl) v₀ hv₀ hvh hvt hvc hcb
    Pk lay cL hLay hM hp hg.depth

/-! ### The retuned sizes -/

open Mult.Sizes
open IntegerMultBounds.MathlibTM2.Fast.ConvSt IntegerMultBounds.MathlibTM2.Fast.TableVM

/-- The geometry of the retuned transforms (`compactSynRetunedGeometry_eventually`). -/
abbrev CompactSynRetunedGeom (M : ℕ) : Prop :=
  CompactSynUniformGeometry M (Mult.CompactSizes.K M) (dsyEs M) (Mult.Sizes.ℓ M) (dsW M)
    (Mult.Sizes.ℓ M) (Mult.Sizes.p M)

/-- The rounded forward rounds at the retuned sizes. -/
def compactRetunedFOp (M : ℕ) (hg : CompactSynRetunedGeom M) :
    RoundOp (dsyEs M).sum (Mult.Sizes.p M) (fwdRound (r := 2^(Mult.Sizes.ℓ M)) (dsyEs M))
      (etaQ (Mult.Sizes.p M) (1/16)) :=
  compactSynFOp Cost.brDirs Cost.br_directions_realizes M (Mult.CompactSizes.K M) (dsyEs M)
    (Mult.Sizes.ℓ M) (dsW M) (Mult.Sizes.ℓ M) (Mult.Sizes.p M) hg.layout hg.numerator
    hg.reservation hg.dimension

/-- The rounded opposite rounds at the retuned sizes. -/
def compactRetunedOOp (M : ℕ) (hg : CompactSynRetunedGeom M) :
    RoundOp (dsyEs M).sum (Mult.Sizes.p M) (oppRound (r := 2^(Mult.Sizes.ℓ M)) (dsyEs M))
      (etaQ (Mult.Sizes.p M) (1/16)) :=
  compactSynOOp Cost.brDirs Cost.br_directions_realizes M (Mult.CompactSizes.K M) (dsyEs M)
    (Mult.Sizes.ℓ M) (dsW M) (Mult.Sizes.ℓ M) (Mult.Sizes.p M) hg.layout hg.numerator
    hg.reservation hg.dimension

def compactSynRetunedFwdCostR (M cL : ℕ) : ℕ :=
  (compactMnOriginalBootstrapCost (Mult.Sizes.p M) (Mult.Sizes.d M)+
        (((1+cL)+compactSynLoopFCostR (Ka := mnKa) Cost.brDirs M (Mult.CompactSizes.K M) (List.ofFn (cvAx (t M))) (Mult.Sizes.ℓ M) (dsW M) (Mult.Sizes.ℓ M) (nRounds (cvAx (t M)))
        (synStashCostW (A := prime+mnKa) (compactDsyV₀ M) synXS+6*nRounds (cvAx (t M))+6))+((2*Mult.Sizes.d M+2)+(2*(4*Nat.clog 2 (Mult.Sizes.p M)+6)+2))))


theorem compactSynRetunedFwdR_eventually : ∀ᶠ M : ℕ in atTop,
    ∀ (hg : CompactSynRetunedGeom M) (mainP : MnPr (prime+mnKa)),
    SynFwdSpecQ (compactMainBodyR (Ka := mnKa) (mnBody mnLb mainP) Cost.brDirs) (compactSynFwdR (Ka := mnKa) Cost.brDirs (slyFwd mnQ_layer)) (compactMnRg (.src (.v .io)))
      (compactSynPre (Ka := mnKa) M (slyPk (blW dsW M) (blE M)) (compactDsyV₀ M)) (dsW M) (Mult.Sizes.p M) (Mult.Sizes.ℓ M) (cvAx (t M)) (synPi (layPerm (List.ofFn (cvAx (t M))) (Mult.Sizes.ℓ M) (Mult.CompactSizes.K M)))
      (compactRetunedFOp M hg)
      (compactSynRetunedFwdCostR M (compactBlCL M)) := by
  have hA : 21≤prime+mnKa := by have := mnKa_alpha; omega
  filter_upwards [compactSynUniformFwdR_eventually hA (embKa_hA9 mnKa_le) (embKa_hNW mnKa_le),
    compactBlLay.wires,compactBlLay.layF]
    with M hspec hv hLay
  intro hg mainP
  obtain ⟨hv₀,hvh,hvt,hvc,hcb⟩ := hv
  have hAl : nRounds (cvAx (t M))≤Mult.Sizes.ℓ M+1 :=
    (nRounds_le hg.layout).trans (Nat.le_succ _)
  dsimp only [compactBlLay] at hv₀ hvh hvt hvc hcb hLay
  exact hspec Cost.brDirs Cost.br_directions_realizes (embKa_gate mnKa_le)
    (mnBody mnLb mainP) (mn_body_lay mainP) (Mult.CompactSizes.K M) _
    (Mult.Sizes.ℓ M) (dsW M) (Mult.Sizes.ℓ M) (Mult.Sizes.p M) (cvAx (t M)) hg hAl
    (compactDsyV₀ M) hv₀ hvh hvt hvc hcb (slyPk (blW dsW M) (blE M))
    (slyFwd mnQ_layer) (compactBlCL M) hLay

def compactSynRetunedOppCostR (M cL : ℕ) : ℕ :=
  (compactMnOriginalBootstrapCost (Mult.Sizes.p M) (Mult.Sizes.d M)+
        ((compactSynLoopOCostR (Ka := mnKa) Cost.brDirs M (Mult.CompactSizes.K M) (List.ofFn (cvAx (t M))) (Mult.Sizes.ℓ M) (dsW M) (Mult.Sizes.ℓ M) (nRounds (cvAx (t M)))
        (synStashCostW (A := prime+mnKa) (compactDsyV₀ M) synXS+6*nRounds (cvAx (t M))+6)+(1+cL))+((2*Mult.Sizes.d M+2)+(2*(4*Nat.clog 2 (Mult.Sizes.p M)+6)+2))))


theorem compactSynRetunedOppR_eventually : ∀ᶠ M : ℕ in atTop,
    ∀ (hg : CompactSynRetunedGeom M) (mainP : MnPr (prime+mnKa)),
    SynOppSpecQ (compactMainBodyR (Ka := mnKa) (mnBody mnLb mainP) Cost.brDirs) (compactSynOppR (Ka := mnKa) Cost.brDirs (slyOpp mnQ_layer)) (compactMnRg (.src (.v .io)))
      (compactSynPre (Ka := mnKa) M (slyPk (blW dsW M) (blE M)) (compactDsyV₀ M)) (dsW M) (Mult.Sizes.p M) (Mult.Sizes.ℓ M) (cvAx (t M)) (synPi (layPerm (List.ofFn (cvAx (t M))) (Mult.Sizes.ℓ M) (Mult.CompactSizes.K M)))
      (compactRetunedOOp M hg)
      (compactSynRetunedOppCostR M (compactBlCL' M)) := by
  have hA : 21≤prime+mnKa := by have := mnKa_alpha; omega
  filter_upwards [compactSynUniformOppR_eventually hA (embKa_hA9 mnKa_le) (embKa_hNW mnKa_le),
    compactBlLay.wires,compactBlLay.layO]
    with M hspec hv hLay
  intro hg mainP
  obtain ⟨hv₀,hvh,hvt,hvc,hcb⟩ := hv
  have hAl : nRounds (cvAx (t M))≤Mult.Sizes.ℓ M+1 :=
    (nRounds_le hg.layout).trans (Nat.le_succ _)
  dsimp only [compactBlLay] at hv₀ hvh hvt hvc hcb hLay
  exact hspec Cost.brDirs Cost.br_directions_realizes (embKa_gate mnKa_le)
    (mnBody mnLb mainP) (mn_body_lay mainP) (Mult.CompactSizes.K M) _
    (Mult.Sizes.ℓ M) (dsW M) (Mult.Sizes.ℓ M) (Mult.Sizes.p M) (cvAx (t M)) hg hAl
    (compactDsyV₀ M) hv₀ hvh hvt hvc hcb (slyPk (blW dsW M) (blE M))
    (slyOpp mnQ_layer) (compactBlCL' M) hLay

end
end IntegerMultBounds.MathlibTM2.Fast.Main
