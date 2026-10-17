module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLoopsR
public import IntegerMultBounds.MathlibTM2.Fast.ConvSpecQ
import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformTransformPre
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynTransformPre
import IntegerMultBounds.MathlibTM2.Fast.CompactMainTransformPipeline
import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapTransformFrame
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayoutTransport
import IntegerMultBounds.MathlibTM2.Fast.CompactSynDirect
import IntegerMultBounds.MathlibTM2.Fast.CompactMainLegacyRuns
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapPipelineCompose
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-! The rounded forward and opposite transforms: the layout programs around the rounded loops.
`SynFwdSpecQ`, `SynOppSpecQ` are the transform contracts of `Fast/ConvSpec` with the computed
rounds `Q` in place of `Q_p` after each exact round. -/
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

/-! ### Computed rounds as iterated record maps -/

theorem fwdRoundsQ_eq_synIterF {r N p : ℕ} {R : ℕ → Recs r → Recs r} {η : ℝ}
    (F : RoundOp N p R η) {Qr : ℕ → Recs r → Recs r} (hF : ∀ h u, F.Q h u = Qr h u) :
    ∀ k u, fwdRoundsQ F k u = synIterF Qr k u
  | 0, _ => rfl
  | k + 1, u => by rw [fwdRoundsQ, synIterF, hF]; exact fwdRoundsQ_eq_synIterF F hF k _

theorem oppRoundsQ_eq_synIterO {r N p : ℕ} {R : ℕ → Recs r → Recs r} {η : ℝ}
    (O : RoundOp N p R η) {Qr : ℕ → Recs r → Recs r} (hO : ∀ h u, O.Q h u = Qr h u) :
    ∀ k u, oppRoundsQ O k u = synIterO Qr k u
  | 0, _ => rfl
  | k + 1, u => by rw [oppRoundsQ, synIterO, hO, oppRoundsQ_eq_synIterO O hO k u]

/-! ### The layout programs under the rounded procedure table -/

theorem compactSynLayoutR_runs (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions)
    (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
    {p : Pr LProc (nT SXReg) mnQ (prime+Ka) Unit}
    {io out park : List (Fin (prime+Ka+4))} {v : SynW → List (Fin (prime+Ka+4))} {c : ℕ}
    (h : LayRuns (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds) p
      (synG (synIdle io park) v) (synG (synIdle out park) v) c)
    (R : Fin compactMnT → List (Fin (prime+Ka+4)))
    (hR : compactSynView R=synG (synIdle io park) v) :
    LayRuns (compactMainBodyR legacy ds) (compactSynLayout p) R
      (Function.update R (compactMnRg (.src (.v .io))) out) (1+c) := by
  have hout : synG (synIdle out park) v=Function.update (synG (synIdle io park) v) mnLio out := by
    rw [synG_update_out (lreg_out (by simp)),synIdle_update_io]
  rw [hout] at h
  have he := compactLegacyLayer_runs legacy (compactMainNativeTableR ds)
    (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds) hbody h R hR
  rw [compactLegacyLayer_io_restore _ R _ hR] at he
  exact he

/-! ### The rounded transforms -/

def compactSynFwdCoreR (ds : ComplexFramedExecution.Directions)
    (layP : Pr LProc (nT SXReg) mnQ (prime+Ka) Unit) : CompactMnPr CompactMainProc (prime+Ka) :=
  .seq (compactSynLayout layP) (compactSynLoopFR ds)

def compactSynFwdR (ds : ComplexFramedExecution.Directions)
    (layP : Pr LProc (nT SXReg) mnQ (prime+Ka) Unit) : CompactMnPr CompactMainProc (prime+Ka) :=
  compactMnTransformPipeline (compactSynFwdCoreR ds layP)

section
variable (legacy : MnProc → MnPr (prime+Ka)) (ds : ComplexFramedExecution.Directions)
  (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
  {M K d ℓ W l p : ℕ} (a : Fin d → ℕ)
  (H : LayHyp (List.ofFn a) ℓ K) (hAl : nRounds a≤l+1)
  (hLoop : CompactSynLoopContractR legacy ds M K (List.ofFn a) ℓ W l p true)
  (hinv : CompactSynInvR ds M K (List.ofFn a) ℓ W l p) {η : ℝ}
  (F : RoundOp (List.ofFn a).sum p (fwdRound (r := 2^l) (List.ofFn a)) η)
  (hFq : ∀ h u, F.Q h u = compactSynFQ ds M K (List.ofFn a) ℓ W l p h u)
  (v₀ : SynW → List (Fin (prime+Ka+4)))
  (hv₀ : SynV v₀ (List.ofFn a) ℓ K W l 0 (layPerm (List.ofFn a) ℓ K))
  (hvh : v₀ (.p .h)=[]) (hvt : v₀ (.p .t)=[]) (hvc : (v₀ (.p .c)).length=nRounds a)
  (hcb : blank∉v₀ (.p .c)) (Pk : List (Fin (prime+Ka+4)) → Prop)
  (layP : Pr LProc (nT SXReg) mnQ (prime+Ka) Unit) (cL : ℕ)
  (hLay : ∀ park,Pk park → ∀ Z : ℕ → Fin (2^l) → GaussianInt,
    LayRuns (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds) layP
      (synG (synIdle (cstream (prime+Ka) W (rpStream (cvM a) Z)) park) v₀)
      (synG (synIdle (cstream (prime+Ka) W (rpStream (cvM a)
        (fun m => Z (synPi (layPerm (List.ofFn a) ℓ K) m)))) park) v₀) cL)
include hbody H hAl hLoop hinv hFq hv₀ hvh hvt hvc hcb hLay

theorem compactSynFwdCoreR_runs (park : List (Fin (prime+Ka+4))) (hPk : Pk park)
    (Z : ℕ → Fin (2^l) → GaussianInt) (hdisk : SupLe (List.ofFn a).sum (rpGrid p Z) 1)
    (R : Fin compactMnT → List (Fin (prime+Ka+4)))
    (hR : compactSynView R=synG (synIdle (cstream (prime+Ka) W (rpStream (cvM a) Z)) park) v₀)
    (hr : CompactSynReady R M) :
    LayRuns (compactMainBodyR legacy ds) (compactSynFwdCoreR ds layP) R
      (Function.update R (compactMnRg (.src (.v .io))) (cstream (prime+Ka) W (rpStream (cvM a)
        (cvFwdOutQ p l a (synPi (layPerm (List.ofFn a) ℓ K)) F Z))))
      ((1+cL)+compactSynLoopFCostR (Ka := Ka) ds M K (List.ofFn a) ℓ W l (nRounds a)
        (synStashCostW v₀ synXS+6*nRounds a+6)) := by
  let io := cstream (prime+Ka) W (rpStream (cvM a)
    (fun m => Z (synPi (layPerm (List.ofFn a) ℓ K) m)))
  let R₁ := Function.update R (compactMnRg (.src (.v .io))) io
  have hl := compactSynLayoutR_runs legacy ds hbody (hLay park hPk Z) R hR
  have hview : compactSynView R₁=synG (synIdle (cstream (prime+Ka) W
      (rpStream (2^(List.ofFn a).sum) (synYnum p (layPerm (List.ofFn a) ℓ K) (rpGrid p Z)))) park) v₀ := by
    rw [synYnum_rpGrid]
    exact compactSynView_io R _ _ park v₀ hR
  have hs := hLoop (nRounds a) (nRounds_le H) hAl v₀ hv₀ hvh hvt hvc hcb park
    (rpGrid p Z) hdisk (rpGrid_grid p Z) hinv R₁ hview (hr.update_io _)
  have he := hl.seq hs
  have hout : synYnum p (layPerm (List.ofFn a) ℓ K)
      (synIterF (compactSynFQ ds M K (List.ofFn a) ℓ W l p) (nRounds a) (rpGrid p Z)) =
      cvFwdOutQ p l a (synPi (layPerm (List.ofFn a) ℓ K)) F Z := by
    unfold cvFwdOutQ; rw [fwdRoundsQ_eq_synIterF F hFq]; rfl
  simpa only [compactSynFwdCoreR,R₁,Function.update_idem,ite_true,hout] using he

theorem compactSynFwdCoreR_spec :
    SynFwdSpecQ (compactMainBodyR legacy ds) (compactSynFwdCoreR ds layP) (compactMnRg (.src (.v .io)))
      (compactSynPreReady M Pk v₀) W p l a (synPi (layPerm (List.ofFn a) ℓ K)) F
      ((1+cL)+compactSynLoopFCostR (Ka := Ka) ds M K (List.ofFn a) ℓ W l (nRounds a)
        (synStashCostW v₀ synXS+6*nRounds a+6)) := by
  intro Z vv S hPre hdisk hio
  obtain ⟨hleft,hr,park,hPk,hR⟩ := hPre
  rw [hio] at hR
  exact compactSynFwdCoreR_runs legacy ds hbody a H hAl hLoop hinv F hFq v₀ hv₀ hvh hvt hvc hcb Pk layP cL hLay
    park hPk Z hdisk S.R hR hr vv S hleft rfl

end

section
variable (legacy : MnProc → MnPr (prime+Ka)) (ds : ComplexFramedExecution.Directions)
  (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
  {M K d ℓ W l p : ℕ} (a : Fin d → ℕ)
  (H : LayHyp (List.ofFn a) ℓ K) (hAl : nRounds a≤l+1)
  (hLoop : CompactSynLoopContractR legacy ds M K (List.ofFn a) ℓ W l p true)
  (hinv : CompactSynInvR ds M K (List.ofFn a) ℓ W l p) {η : ℝ}
  (F : RoundOp (List.ofFn a).sum p (fwdRound (r := 2^l) (List.ofFn a)) η)
  (hFq : ∀ h u, F.Q h u = compactSynFQ ds M K (List.ofFn a) ℓ W l p h u)
  (v₀ : SynW → List (Fin (prime+Ka+4)))
  (hv₀ : SynV v₀ (List.ofFn a) ℓ K W l 0 (layPerm (List.ofFn a) ℓ K))
  (hvh : v₀ (.p .h)=[]) (hvt : v₀ (.p .t)=[]) (hvc : (v₀ (.p .c)).length=nRounds a)
  (hcb : blank∉v₀ (.p .c)) (Pk : List (Fin (prime+Ka+4)) → Prop)
  (layP : Pr LProc (nT SXReg) mnQ (prime+Ka) Unit) (cL : ℕ)
  (hLay : ∀ park,Pk park → ∀ Z : ℕ → Fin (2^l) → GaussianInt,
    LayRuns (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds) layP
      (synG (synIdle (cstream (prime+Ka) W (rpStream (cvM a) Z)) park) v₀)
      (synG (synIdle (cstream (prime+Ka) W (rpStream (cvM a)
        (fun m => Z (synPi (layPerm (List.ofFn a) ℓ K) m)))) park) v₀) cL)
variable (hM : 2≤M)
  (hp : 2≤Mult.Sizes.p M) (hd : 0<Mult.Sizes.d M)
include hbody H hAl hLoop hinv hFq hv₀ hvh hvt hvc hcb hLay hM hp hd

theorem compactSynFwdR_spec :
    SynFwdSpecQ (compactMainBodyR legacy ds) (compactSynFwdR ds layP) (compactMnRg (.src (.v .io)))
      (compactSynPre M Pk v₀) W p l a (synPi (layPerm (List.ofFn a) ℓ K)) F
      (compactMnOriginalBootstrapCost (Mult.Sizes.p M) (Mult.Sizes.d M)+
        (((1+cL)+compactSynLoopFCostR (Ka := Ka) ds M K (List.ofFn a) ℓ W l (nRounds a)
        (synStashCostW v₀ synXS+6*nRounds a+6))+((2*Mult.Sizes.d M+2)+(2*(4*Nat.clog 2 (Mult.Sizes.p M)+6)+2)))) := by
  intro Z vv S hPre hdisk hio
  obtain ⟨hleft,hpSource,hdSource,hb,park,hPk,hR⟩ := hPre
  rw [hio] at hR
  have hs := compactSynUniformView_scratch hv₀ hR
  have hv := (compactMnBootstrapFinal_view S.R (Mult.Sizes.p M) (Mult.Sizes.d M) hs hb).trans hR
  have hr := compactMnBootstrapFinal_ready M hM S.R hs hb
  have hc := compactSynFwdCoreR_runs legacy ds hbody a H hAl hLoop hinv F hFq v₀ hv₀ hvh hvt hvc hcb Pk layP cL hLay
    park hPk Z hdisk (compactMnBootstrapFinal S.R (Mult.Sizes.p M) (Mult.Sizes.d M)) hv hr
  have he := compactMnTransformPipeline_from_sources (compactMainBodyR legacy ds)
    (compactSynFwdCoreR ds layP) S.R (Mult.Sizes.p M) (Mult.Sizes.d M) _ _ hp hd hpSource hdSource hs hb hc
  exact he vv S hleft rfl

end

def compactSynOppCoreR (ds : ComplexFramedExecution.Directions)
    (layQ : Pr LProc (nT SXReg) mnQ (prime+Ka) Unit) : CompactMnPr CompactMainProc (prime+Ka) :=
  .seq (compactSynLoopOR ds) (compactSynLayout layQ)

def compactSynOppR (ds : ComplexFramedExecution.Directions)
    (layQ : Pr LProc (nT SXReg) mnQ (prime+Ka) Unit) : CompactMnPr CompactMainProc (prime+Ka) :=
  compactMnTransformPipeline (compactSynOppCoreR ds layQ)

section
variable (legacy : MnProc → MnPr (prime+Ka)) (ds : ComplexFramedExecution.Directions)
  (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
  {M K d ℓ W l p : ℕ} (a : Fin d → ℕ)
  (H : LayHyp (List.ofFn a) ℓ K) (hAl : nRounds a≤l+1)
  (hLoop : CompactSynLoopContractR legacy ds M K (List.ofFn a) ℓ W l p false)
  (hinv : CompactSynInvR ds M K (List.ofFn a) ℓ W l p) {η : ℝ}
  (O : RoundOp (List.ofFn a).sum p (oppRound (r := 2^l) (List.ofFn a)) η)
  (hOq : ∀ h u, O.Q h u = compactSynOQ ds M K (List.ofFn a) ℓ W l p h u)
  (v₀ : SynW → List (Fin (prime+Ka+4)))
  (hv₀ : SynV v₀ (List.ofFn a) ℓ K W l 0 (layPerm (List.ofFn a) ℓ K))
  (hvh : v₀ (.p .h)=[]) (hvt : v₀ (.p .t)=[]) (hvc : (v₀ (.p .c)).length=nRounds a)
  (hcb : blank∉v₀ (.p .c)) (Pk : List (Fin (prime+Ka+4)) → Prop)
  (layQ : Pr LProc (nT SXReg) mnQ (prime+Ka) Unit) (cL : ℕ)
  (hLay : ∀ park,Pk park → ∀ Y : ℕ → Fin (2^l) → GaussianInt,
    LayRuns (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds) layQ
      (synG (synIdle (cstream (prime+Ka) W (rpStream (cvM a) Y)) park) v₀)
      (synG (synIdle (cstream (prime+Ka) W (rpStream (cvM a)
        (fun x => Y ((layRec (layPerm (List.ofFn a) ℓ K))
          ⟨x % 2^(List.ofFn a).sum,Nat.mod_lt _ (by positivity)⟩)))) park) v₀) cL)
include hbody H hAl hLoop hinv hOq hv₀ hvh hvt hvc hcb hLay

theorem compactSynOppCoreR_runs (park : List (Fin (prime+Ka+4))) (hPk : Pk park)
    (V : ℕ → Fin (2^l) → GaussianInt) (hdisk : SupLe (List.ofFn a).sum (rpGrid p V) 1)
    (R : Fin compactMnT → List (Fin (prime+Ka+4)))
    (hR : compactSynView R=synG (synIdle (cstream (prime+Ka) W (rpStream (cvM a)
      (fun m => V (synPi (layPerm (List.ofFn a) ℓ K) m)))) park) v₀)
    (hr : CompactSynReady R M) :
    LayRuns (compactMainBodyR legacy ds) (compactSynOppCoreR ds layQ) R
      (Function.update R (compactMnRg (.src (.v .io))) (cstream (prime+Ka) W (rpStream (cvM a)
        (cvOppOutQ p l a O V))))
      (compactSynLoopOCostR (Ka := Ka) ds M K (List.ofFn a) ℓ W l (nRounds a)
        (synStashCostW v₀ synXS+6*nRounds a+6)+(1+cL)) := by
  let L := layPerm (List.ofFn a) ℓ K
  let Yout := synYnum p L (synIterO (compactSynOQ ds M K (List.ofFn a) ℓ W l p) (nRounds a) (rpGrid p V))
  let io := cstream (prime+Ka) W (rpStream (cvM a) Yout)
  let R₁ := Function.update R (compactMnRg (.src (.v .io))) io
  have hview : compactSynView R=synG (synIdle (cstream (prime+Ka) W
      (rpStream (2^(List.ofFn a).sum) (synYnum p L (rpGrid p V)))) park) v₀ := by
    rw [synYnum_rpGrid]
    exact hR
  have hs := hLoop (nRounds a) (nRounds_le H) hAl v₀ hv₀ hvh hvt hvc hcb park
    (rpGrid p V) hdisk (rpGrid_grid p V) hinv R hview hr
  have hl := compactSynLayoutR_runs legacy ds hbody (hLay park hPk Yout) R₁
    (compactSynView_io R _ _ park v₀ hR)
  have hout : cstream (prime+Ka) W (rpStream (cvM a)
      (fun x => Yout ((layRec L) ⟨x % 2^(List.ofFn a).sum,Nat.mod_lt _ (by positivity)⟩)))=
      cstream (prime+Ka) W (rpStream (cvM a) (cvOppOutQ p l a O V)) := by
    apply congrArg (cstream (prime+Ka) W)
    refine rpStream_congr fun x hx => ?_
    funext c
    simp only [Yout,synYnum,cvOppOutQ,cvNum,oppRoundsQ_eq_synIterO O hOq]
    have hpi : synPi L ((layRec L) ⟨x % 2^(List.ofFn a).sum,Nat.mod_lt _ (by positivity)⟩)=x := by
      rw [synPi_layRec,Equiv.symm_apply_apply]
      exact Nat.mod_eq_of_lt hx
    rw [hpi]
  dsimp only [L] at hout
  have he := hs.seq hl
  simpa only [compactSynOppCoreR,R₁,Function.update_idem,hout,Bool.false_eq_true,ite_false] using he

theorem compactSynOppCoreR_spec :
    SynOppSpecQ (compactMainBodyR legacy ds) (compactSynOppCoreR ds layQ) (compactMnRg (.src (.v .io)))
      (compactSynPreReady M Pk v₀) W p l a (synPi (layPerm (List.ofFn a) ℓ K)) O
      (compactSynLoopOCostR (Ka := Ka) ds M K (List.ofFn a) ℓ W l (nRounds a)
        (synStashCostW v₀ synXS+6*nRounds a+6)+(1+cL)) := by
  intro V vv S hPre hdisk hio
  obtain ⟨hleft,hr,park,hPk,hR⟩ := hPre
  rw [hio] at hR
  exact compactSynOppCoreR_runs legacy ds hbody a H hAl hLoop hinv O hOq v₀ hv₀ hvh hvt hvc hcb Pk layQ cL hLay
    park hPk V hdisk S.R hR hr vv S hleft rfl

end

section
variable (legacy : MnProc → MnPr (prime+Ka)) (ds : ComplexFramedExecution.Directions)
  (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
  {M K d ℓ W l p : ℕ} (a : Fin d → ℕ)
  (H : LayHyp (List.ofFn a) ℓ K) (hAl : nRounds a≤l+1)
  (hLoop : CompactSynLoopContractR legacy ds M K (List.ofFn a) ℓ W l p false)
  (hinv : CompactSynInvR ds M K (List.ofFn a) ℓ W l p) {η : ℝ}
  (O : RoundOp (List.ofFn a).sum p (oppRound (r := 2^l) (List.ofFn a)) η)
  (hOq : ∀ h u, O.Q h u = compactSynOQ ds M K (List.ofFn a) ℓ W l p h u)
  (v₀ : SynW → List (Fin (prime+Ka+4)))
  (hv₀ : SynV v₀ (List.ofFn a) ℓ K W l 0 (layPerm (List.ofFn a) ℓ K))
  (hvh : v₀ (.p .h)=[]) (hvt : v₀ (.p .t)=[]) (hvc : (v₀ (.p .c)).length=nRounds a)
  (hcb : blank∉v₀ (.p .c)) (Pk : List (Fin (prime+Ka+4)) → Prop)
  (layQ : Pr LProc (nT SXReg) mnQ (prime+Ka) Unit) (cL : ℕ)
  (hLay : ∀ park,Pk park → ∀ Y : ℕ → Fin (2^l) → GaussianInt,
    LayRuns (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds) layQ
      (synG (synIdle (cstream (prime+Ka) W (rpStream (cvM a) Y)) park) v₀)
      (synG (synIdle (cstream (prime+Ka) W (rpStream (cvM a)
        (fun x => Y ((layRec (layPerm (List.ofFn a) ℓ K))
          ⟨x % 2^(List.ofFn a).sum,Nat.mod_lt _ (by positivity)⟩)))) park) v₀) cL)
variable (hM : 2≤M)
  (hp : 2≤Mult.Sizes.p M) (hd : 0<Mult.Sizes.d M)
include hbody H hAl hLoop hinv hOq hv₀ hvh hvt hvc hcb hLay hM hp hd

theorem compactSynOppR_spec :
    SynOppSpecQ (compactMainBodyR legacy ds) (compactSynOppR ds layQ) (compactMnRg (.src (.v .io)))
      (compactSynPre M Pk v₀) W p l a (synPi (layPerm (List.ofFn a) ℓ K)) O
      (compactMnOriginalBootstrapCost (Mult.Sizes.p M) (Mult.Sizes.d M)+
        ((compactSynLoopOCostR (Ka := Ka) ds M K (List.ofFn a) ℓ W l (nRounds a)
        (synStashCostW v₀ synXS+6*nRounds a+6)+(1+cL))+((2*Mult.Sizes.d M+2)+(2*(4*Nat.clog 2 (Mult.Sizes.p M)+6)+2)))) := by
  intro V vv S hPre hdisk hio
  obtain ⟨hleft,hpSource,hdSource,hb,park,hPk,hR⟩ := hPre
  rw [hio] at hR
  have hs := compactSynUniformView_scratch hv₀ hR
  have hv := (compactMnBootstrapFinal_view S.R (Mult.Sizes.p M) (Mult.Sizes.d M) hs hb).trans hR
  have hr := compactMnBootstrapFinal_ready M hM S.R hs hb
  have hc := compactSynOppCoreR_runs legacy ds hbody a H hAl hLoop hinv O hOq v₀ hv₀ hvh hvt hvc hcb Pk layQ cL hLay
    park hPk V hdisk (compactMnBootstrapFinal S.R (Mult.Sizes.p M) (Mult.Sizes.d M)) hv hr
  have he := compactMnTransformPipeline_from_sources (compactMainBodyR legacy ds)
    (compactSynOppCoreR ds layQ) S.R (Mult.Sizes.p M) (Mult.Sizes.d M) _ _ hp hd hpSource hdSource hs hb hc
  exact he vv S hleft rfl

end

end
end IntegerMultBounds.MathlibTM2.Fast.Main
