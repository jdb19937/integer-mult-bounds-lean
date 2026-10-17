module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRoundR
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLoopsContract

/-! The rounded forward and opposite loops: the counter scans of the rounded rounds. On
records the forward loop computes `synIterF` of `compactSynFQ` (rounds `h = A - 1, …, 0`) and
the opposite loop `synIterO` of `compactSynOQ` (rounds `h = 0, …, A - 1`), given that both
rounds keep the unit disk and the `p`-bit grid (`CompactSynInvR`). -/
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

/-! ### Iterated rounds -/

section Iter

variable {r : ℕ}

/-- Rounds `Q` at `h = k - 1, …, 0`, in this order. -/
def synIterF (Q : ℕ → Recs r → Recs r) : ℕ → Recs r → Recs r
  | 0, u => u
  | k + 1, u => synIterF Q k (Q k u)

/-- Rounds `Q` at `h = 0, …, k - 1`, in this order. -/
def synIterO (Q : ℕ → Recs r → Recs r) : ℕ → Recs r → Recs r
  | 0, u => u
  | k + 1, u => Q k (synIterO Q k u)

/-- The array after `j` forward rounds of `A`: the rounds at `h = A - 1, …, A - j`. -/
def synUFR (Q : ℕ → Recs r → Recs r) (A : ℕ) (z : Recs r) : ℕ → Recs r
  | 0 => z
  | j + 1 => Q (A - 1 - j) (synUFR Q A z j)

theorem synIterF_synUFR (Q : ℕ → Recs r → Recs r) (A : ℕ) (z : Recs r) : ∀ j ≤ A,
    synIterF Q A z = synIterF Q (A - j) (synUFR Q A z j)
  | 0, _ => rfl
  | j + 1, hj => by
      rw [synIterF_synUFR Q A z j (by omega)]
      obtain ⟨k, hk⟩ : ∃ k, A - j = k + 1 := ⟨A - j - 1, by omega⟩
      rw [hk, synIterF, synUFR, show A - (j + 1) = k by omega, show A - 1 - j = k by omega]

theorem synIterF_eq_synUFR (Q : ℕ → Recs r → Recs r) (A : ℕ) (z : Recs r) :
    synIterF Q A z = synUFR Q A z A := by
  have := synIterF_synUFR Q A z A le_rfl
  rwa [Nat.sub_self, synIterF] at this

theorem synUFR_inv (Q : ℕ → Recs r → Recs r) {P : Recs r → Prop} (hQ : ∀ h u, P u → P (Q h u))
    {A : ℕ} {z : Recs r} (hz : P z) : ∀ j, P (synUFR Q A z j)
  | 0 => hz
  | j + 1 => hQ _ _ (synUFR_inv Q hQ hz j)

theorem synIterO_inv (Q : ℕ → Recs r → Recs r) {P : Recs r → Prop} (hQ : ∀ h u, P u → P (Q h u))
    {z : Recs r} (hz : P z) : ∀ j, P (synIterO Q j z)
  | 0 => hz
  | j + 1 => hQ _ _ (synIterO_inv Q hQ hz j)

end Iter

/-- The rounded rounds keep the unit disk. -/
def CompactSynInvR (ds : ComplexFramedExecution.Directions) (M K : ℕ) (es : List ℕ)
    (ℓ W l p : ℕ) : Prop :=
  ∀ h (u : Recs (2^l)),SupLe es.sum u 1 → GridR p u →
    SupLe es.sum (compactSynFQ ds M K es ℓ W l p h u) 1 ∧
      SupLe es.sum (compactSynOQ ds M K es ℓ W l p h u) 1

theorem compactSynInvR_F {ds : ComplexFramedExecution.Directions} {M K : ℕ} {es : List ℕ}
    {ℓ W l p : ℕ} (hinv : CompactSynInvR ds M K es ℓ W l p) :
    ∀ h (u : Recs (2^l)),SupLe es.sum u 1 ∧ GridR p u →
      SupLe es.sum (compactSynFQ ds M K es ℓ W l p h u) 1 ∧
        GridR p (compactSynFQ ds M K es ℓ W l p h u) :=
  fun h u hu => ⟨(hinv h u hu.1 hu.2).1,gridR_mulYInv _ (gridR_compactSynLQ ds M K es ℓ W l p h u)⟩

theorem compactSynInvR_O {ds : ComplexFramedExecution.Directions} {M K : ℕ} {es : List ℕ}
    {ℓ W l p : ℕ} (hinv : CompactSynInvR ds M K es ℓ W l p) :
    ∀ h (u : Recs (2^l)),SupLe es.sum u 1 ∧ GridR p u →
      SupLe es.sum (compactSynOQ ds M K es ℓ W l p h u) 1 ∧
        GridR p (compactSynOQ ds M K es ℓ W l p h u) :=
  fun h u hu => ⟨(hinv h u hu.1 hu.2).2,gridR_compactSynLQ ds M K es ℓ W l p h _⟩

/-! ### Programs and costs -/

def compactSynBodyFR (ds : ComplexFramedExecution.Directions) : CompactMnPr CompactMainProc (prime+Ka) :=
  compactCounterBody (compactSynDispatchReg (.p .c)) (compactSynDispatchReg (.p .h))
    (compactSynDispatchReg (.s 2)) false (compactSynRoundFR ds)

def compactSynBodyOR (ds : ComplexFramedExecution.Directions) : CompactMnPr CompactMainProc (prime+Ka) :=
  compactCounterBody (compactSynDispatchReg (.p .t)) (compactSynDispatchReg (.p .h))
    (compactSynDispatchReg (.s 2)) true (compactSynRoundOR ds)

def compactSynLoopFR (ds : ComplexFramedExecution.Directions) : CompactMnPr CompactMainProc (prime+Ka) :=
  scanP (compactSynDispatchReg (.p .c)) (compactSynDispatchReg (.p .t)) (compactSynBodyFR ds)

def compactSynLoopOR (ds : ComplexFramedExecution.Directions) : CompactMnPr CompactMainProc (prime+Ka) :=
  scanP (compactSynDispatchReg (.p .c)) (compactSynDispatchReg (.p .t)) (compactSynBodyOR ds)

theorem compactSynLayerCostR_mono (ds : ComplexFramedExecution.Directions) (M K : ℕ)
    (es : List ℕ) (ℓ W l h : ℕ) {s s' : ℕ} (hs : s≤s') :
    compactSynLayerCostR (Ka := Ka) ds M K es ℓ W l h s≤compactSynLayerCostR (Ka := Ka) ds M K es ℓ W l h s' := by
  unfold compactSynLayerCostR
  dsimp only
  split_ifs
  · simp only [compactSynLayerRoundOverheadR,compactSynLayerParkCost,compactSynLayerUnparkCostR]
    omega
  · have he := synLayerStepCost_mono ds es ℓ K W l h hs
    omega

theorem compactSynRoundFCostR_mono (ds : ComplexFramedExecution.Directions) (M K : ℕ)
    (es : List ℕ) (ℓ W l h : ℕ) {s s' : ℕ} (hs : s≤s') :
    compactSynRoundFCostR (Ka := Ka) ds M K es ℓ W l h s≤compactSynRoundFCostR (Ka := Ka) ds M K es ℓ W l h s' :=
  Nat.add_le_add_right (compactSynLayerCostR_mono ds M K es ℓ W l h hs) _

theorem compactSynRoundOCostR_mono (ds : ComplexFramedExecution.Directions) (M K : ℕ)
    (es : List ℕ) (ℓ W l h : ℕ) {s s' : ℕ} (hs : s≤s') :
    compactSynRoundOCostR (Ka := Ka) ds M K es ℓ W l h s≤compactSynRoundOCostR (Ka := Ka) ds M K es ℓ W l h s' :=
  Nat.add_le_add_left (compactSynLayerCostR_mono ds M K es ℓ W l h hs) _

def compactSynLoopFCostR (ds : ComplexFramedExecution.Directions) (M K : ℕ)
    (es : List ℕ) (ℓ W l A stk : ℕ) : ℕ :=
  (∑ j ∈ Finset.range A, ((4*(A-1-j)+4)+1+
    compactSynRoundFCostR (Ka := Ka) ds M K es ℓ W l (A-1-j) stk+(2*(A-1-j)+2)+3))+2*A+4

def compactSynLoopOCostR (ds : ComplexFramedExecution.Directions) (M K : ℕ)
    (es : List ℕ) (ℓ W l A stk : ℕ) : ℕ :=
  (∑ j ∈ Finset.range A, ((4*(j+1)+4)+1+
    compactSynRoundOCostR (Ka := Ka) ds M K es ℓ W l j stk+(2*j+2)+3))+2*A+4

/-! ### The loops -/

theorem compactSynLoopFR_step (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions)
    (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
    (hA : 5≤prime+Ka) {M K : ℕ} {es : List ℕ} {ℓ W l p A : ℕ}
    (hLayer : CompactSynLayerContractR legacy ds M K es ℓ W l p)
    (hAℓ : A≤ℓ) (hAl : A≤l+1) (hW : p+2≤W)
    (v : SynW → List (Fin (prime+Ka+4)))
    (hv : SynV v es ℓ K W l 0 (layPerm es ℓ K))
    (hvh : v (.p .h)=[]) (hvc : (v (.p .c)).length=A) (hcb : blank∉v (.p .c))
    (P₀ : List (Fin (prime+Ka+4))) (z : Recs (2^l)) (hz : SupLe es.sum z 1) (hzg : GridR p z)
    (hinv : CompactSynInvR ds M K es ℓ W l p)
    (R : Fin compactMnT → List (Fin (prime+Ka+4)))
    (hR : compactSynView R=synG (synIdle (cstream (prime+Ka) W
      (rpStream (2^es.sum) (synYnum p (layPerm es ℓ K) z))) P₀) v)
    (hr : CompactSynReady R M) (j : ℕ) (hj : j<A) :
    let L := layPerm es ℓ K
    let cs := v (.p .c)
    LayRuns (compactMainBodyR legacy ds) (compactSynBodyFR ds)
      (compactSynScanState R (cstream (prime+Ka) W (rpStream (2^es.sum) (synYnum p L (synUFR (compactSynFQ ds M K es ℓ W l p) A z j))))
        (cs.drop (j+1)) (cs.take (j+1)).reverse)
      (compactSynScanState R (cstream (prime+Ka) W (rpStream (2^es.sum) (synYnum p L (synUFR (compactSynFQ ds M K es ℓ W l p) A z (j+1)))))
        (cs.drop (j+1)) (cs.take (j+1)).reverse)
      ((4*(A-1-j)+4)+1+compactSynRoundFCostR (Ka := Ka) ds M K es ℓ W l (A-1-j)
        (synStashCostW v synXS+6*A+6)+(2*(A-1-j)+2)) := by
  dsimp only
  let L := layPerm es ℓ K
  let cs := v (.p .c)
  let Y := synYnum p L (synUFR (compactSynFQ ds M K es ℓ W l p) A z j)
  let Rj := compactSynScanState R (cstream (prime+Ka) W (rpStream (2^es.sum) Y))
    (cs.drop (j+1)) (cs.take (j+1)).reverse
  let vj := Function.update (Function.update v (.p .c) (cs.drop (j+1))) (.p .t) (cs.take (j+1)).reverse
  let h := A-1-j
  have hcd : blank∉cs.drop (j+1) := fun hx => hcb (List.mem_of_mem_drop hx)
  have hct : blank∉(cs.take (j+1)).reverse := fun hx => hcb (List.mem_of_mem_take (List.mem_reverse.1 hx))
  have hview : compactSynView Rj=synG (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Y)) P₀) vj := by
    dsimp only [Rj,compactSynScanState]
    rw [compactSynView_update_wire,compactSynView_update_wire,compactSynView_io R _ _ P₀ v hR,
      synG_update,synG_update]
  have hviewH : compactSynView (Function.update Rj (compactSynDispatchReg (.p .h)) (List.replicate h tick))=
      synG (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Y)) P₀)
        (synSetH v (cs.drop (j+1)) (cs.take (j+1)).reverse h) := by
    rw [compactSynView_update_wire,hview,synG_update]
    rfl
  have hready : CompactSynReady Rj M := ((hr.update_io _).update_wire (.p .c) _).update_wire (.p .t) _
  obtain ⟨Y',hY',er⟩ := compactSynRoundFR_runs legacy ds hbody hA hLayer (by dsimp only [h]; omega)
    (by dsimp only [h]; omega) hW _ (hv.setH hcd hct h) P₀ (synUFR (compactSynFQ ds M K es ℓ W l p) A z j)
    (synUFR_inv _ (compactSynInvR_F hinv) ⟨hz,hzg⟩ j).1 Y (synNum_ynum (synUFR_inv _ (compactSynInvR_F hinv) ⟨hz,hzg⟩ j).2) _ hviewH (hready.update_wire (.p .h) _)
  rw [synNum_stream hY'] at er
  have hclen : (Rj (compactSynDispatchReg (.p .c))).length=h := by
    rw [compactSynView_wire hview]
    simp only [vj,Function.update_of_ne (by decide : SynW.p .c≠.p .t),Function.update_self,List.length_drop]
    dsimp only [cs,h]
    rw [hvc]
    omega
  have hhs : Rj (compactSynDispatchReg (.p .h))=[] := by
    rw [compactSynView_wire hview]; simpa [vj] using hvh
  have hts : Rj (compactSynDispatchReg (.s 2))=[] := by
    rw [compactSynView_wire hview]; simpa [vj] using hv.hs 2
  have hst : synStashCostW (synSetH v (cs.drop (j+1)) (cs.take (j+1)).reverse h) synXS≤
      synStashCostW v synXS+6*A+6 := by
    have he := synStashCostW_setH v (cs.drop (j+1)) (cs.take (j+1)).reverse h
    simp only [List.length_drop,List.length_reverse,List.length_take] at he
    have hcs : cs.length=A := hvc
    dsimp only [h] at he ⊢
    omega
  have eb := compactCounterBody_runs (compactMainBodyR legacy ds)
    (compactSynDispatchReg_injective.ne (by decide : SynW.p .c≠.p .h))
    (compactSynDispatchReg_injective.ne (by decide : SynW.p .c≠.s 2))
    (compactSynDispatchReg_injective.ne (by decide : SynW.p .h≠.s 2))
    (compactSynDispatchReg_ne_io (.p .h)) hhs hts false _
    (by simpa only [Bool.false_eq_true,ite_false,Nat.sub_zero,hclen] using er)
  apply lr_weaken (compactMainBodyR legacy ds) eb
  · exact compactScan_update_io R (compactSynDispatchReg_ne_io (.p .c))
      (compactSynDispatchReg_ne_io (.p .t)) _ _ _ _
  · have he := compactSynRoundFCostR_mono (Ka := Ka) ds M K es ℓ W l h hst
    simp only [Bool.false_eq_true,ite_false,Nat.sub_zero,hclen]
    dsimp only [h] at he ⊢
    omega

theorem compactSynLoopFR_runs (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions)
    (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
    (hA : 5≤prime+Ka) {M K : ℕ} {es : List ℕ} {ℓ W l p A : ℕ}
    (hLayer : CompactSynLayerContractR legacy ds M K es ℓ W l p)
    (hAℓ : A≤ℓ) (hAl : A≤l+1) (hW : p+2≤W)
    (v : SynW → List (Fin (prime+Ka+4)))
    (hv : SynV v es ℓ K W l 0 (layPerm es ℓ K))
    (hvh : v (.p .h)=[]) (hvt : v (.p .t)=[]) (hvc : (v (.p .c)).length=A) (hcb : blank∉v (.p .c))
    (P₀ : List (Fin (prime+Ka+4))) (z : Recs (2^l)) (hz : SupLe es.sum z 1) (hzg : GridR p z)
    (hinv : CompactSynInvR ds M K es ℓ W l p)
    (R : Fin compactMnT → List (Fin (prime+Ka+4)))
    (hR : compactSynView R=synG (synIdle (cstream (prime+Ka) W
      (rpStream (2^es.sum) (synYnum p (layPerm es ℓ K) z))) P₀) v)
    (hr : CompactSynReady R M) :
    LayRuns (compactMainBodyR legacy ds) (compactSynLoopFR ds) R
      (Function.update R (compactMnRg (.src (.v .io))) (cstream (prime+Ka) W (rpStream (2^es.sum)
        (synYnum p (layPerm es ℓ K) (synIterF (compactSynFQ ds M K es ℓ W l p) A z)))))
      (compactSynLoopFCostR (Ka := Ka) ds M K es ℓ W l A (synStashCostW v synXS+6*A+6)) := by
  let cs := v (.p .c)
  let L := layPerm es ℓ K
  let Φ := fun j => Function.update R (compactMnRg (.src (.v .io)))
    (cstream (prime+Ka) W (rpStream (2^es.sum) (synYnum p L (synUFR (compactSynFQ ds M K es ℓ W l p) A z j))))
  let cost := fun j => (4*(A-1-j)+4)+1+compactSynRoundFCostR (Ka := Ka) ds M K es ℓ W l (A-1-j)
    (synStashCostW v synXS+6*A+6)+(2*(A-1-j)+2)
  have hstep : ∀ j<cs.length,LayRuns (compactMainBodyR legacy ds) (compactSynBodyFR ds)
      (Function.update (Function.update (Φ j) (compactSynDispatchReg (.p .c)) (cs.drop (j+1)))
        (compactSynDispatchReg (.p .t)) (cs.take (j+1)).reverse)
      (Function.update (Function.update (Φ (j+1)) (compactSynDispatchReg (.p .c)) (cs.drop (j+1)))
        (compactSynDispatchReg (.p .t)) (cs.take (j+1)).reverse) (cost j) := by
    intro j hj
    exact compactSynLoopFR_step legacy ds hbody hA hLayer hAℓ hAl hW v hv hvh hvc hcb P₀ z hz hzg hinv R hR hr j
      (by change j<(v (.p .c)).length at hj; rwa [hvc] at hj)
  have he := layScan_exec (body := compactMainBodyR legacy ds)
    (compactSynDispatchReg_injective.ne (by decide : SynW.p .c≠.p .t)) Φ cs cost hstep
  have hcs : cs.length=A := hvc
  rw [hcs] at he
  have hc : R (compactSynDispatchReg (.p .c))=cs := compactSynView_wire hR _
  have ht : R (compactSynDispatchReg (.p .t))=[] := (compactSynView_wire hR _).trans hvt
  have hstart : Function.update (Function.update (Φ 0) (compactSynDispatchReg (.p .c)) cs)
      (compactSynDispatchReg (.p .t)) []=R := by
    rw [←hc,←ht]
    rw [compactScan_restore R (compactSynDispatchReg_ne_io (.p .c)) (compactSynDispatchReg_ne_io (.p .t))]
    dsimp only [L,synUFR]
    rw [←compactSynView_io_value hR,Function.update_eq_self]
  have hend : Function.update (Function.update (Φ A) (compactSynDispatchReg (.p .c)) cs)
      (compactSynDispatchReg (.p .t)) []=
      Function.update R (compactMnRg (.src (.v .io))) (cstream (prime+Ka) W (rpStream (2^es.sum)
        (synYnum p L (synIterF (compactSynFQ ds M K es ℓ W l p) A z)))) := by
    rw [←hc,←ht]
    rw [compactScan_restore R (compactSynDispatchReg_ne_io (.p .c)) (compactSynDispatchReg_ne_io (.p .t))]
    rw [synIterF_eq_synUFR]
  exact lr_weaken (compactMainBodyR legacy ds) (lr_congr_left _ he hstart.symm) hend (by rfl)

theorem compactSynLoopOR_step (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions)
    (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
    (hA : 5≤prime+Ka) {M K : ℕ} {es : List ℕ} {ℓ W l p A : ℕ}
    (hLayer : CompactSynLayerContractR legacy ds M K es ℓ W l p)
    (hAℓ : A≤ℓ) (hAl : A≤l+1) (hW : p+2≤W)
    (v : SynW → List (Fin (prime+Ka+4)))
    (hv : SynV v es ℓ K W l 0 (layPerm es ℓ K))
    (hvh : v (.p .h)=[]) (hvc : (v (.p .c)).length=A) (hcb : blank∉v (.p .c))
    (P₀ : List (Fin (prime+Ka+4))) (z : Recs (2^l)) (hz : SupLe es.sum z 1) (hzg : GridR p z)
    (hinv : CompactSynInvR ds M K es ℓ W l p)
    (R : Fin compactMnT → List (Fin (prime+Ka+4)))
    (hR : compactSynView R=synG (synIdle (cstream (prime+Ka) W
      (rpStream (2^es.sum) (synYnum p (layPerm es ℓ K) z))) P₀) v)
    (hr : CompactSynReady R M) (j : ℕ) (hj : j<A) :
    let L := layPerm es ℓ K
    let cs := v (.p .c)
    LayRuns (compactMainBodyR legacy ds) (compactSynBodyOR ds)
      (compactSynScanState R (cstream (prime+Ka) W (rpStream (2^es.sum) (synYnum p L (synIterO (compactSynOQ ds M K es ℓ W l p) j z))))
        (cs.drop (j+1)) (cs.take (j+1)).reverse)
      (compactSynScanState R (cstream (prime+Ka) W (rpStream (2^es.sum) (synYnum p L (synIterO (compactSynOQ ds M K es ℓ W l p) (j+1) z))))
        (cs.drop (j+1)) (cs.take (j+1)).reverse)
      ((4*(j+1)+4)+1+compactSynRoundOCostR (Ka := Ka) ds M K es ℓ W l j
        (synStashCostW v synXS+6*A+6)+(2*j+2)) := by
  dsimp only
  let L := layPerm es ℓ K
  let cs := v (.p .c)
  let Y := synYnum p L (synIterO (compactSynOQ ds M K es ℓ W l p) j z)
  let Rj := compactSynScanState R (cstream (prime+Ka) W (rpStream (2^es.sum) Y))
    (cs.drop (j+1)) (cs.take (j+1)).reverse
  let vj := Function.update (Function.update v (.p .c) (cs.drop (j+1))) (.p .t) (cs.take (j+1)).reverse
  let h := j
  have hcd : blank∉cs.drop (j+1) := fun hx => hcb (List.mem_of_mem_drop hx)
  have hct : blank∉(cs.take (j+1)).reverse := fun hx => hcb (List.mem_of_mem_take (List.mem_reverse.1 hx))
  have hview : compactSynView Rj=synG (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Y)) P₀) vj := by
    dsimp only [Rj,compactSynScanState]
    rw [compactSynView_update_wire,compactSynView_update_wire,compactSynView_io R _ _ P₀ v hR,
      synG_update,synG_update]
  have hviewH : compactSynView (Function.update Rj (compactSynDispatchReg (.p .h)) (List.replicate h tick))=
      synG (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Y)) P₀)
        (synSetH v (cs.drop (j+1)) (cs.take (j+1)).reverse h) := by
    rw [compactSynView_update_wire,hview,synG_update]
    rfl
  have hready : CompactSynReady Rj M := ((hr.update_io _).update_wire (.p .c) _).update_wire (.p .t) _
  obtain ⟨Y',hY',er⟩ := compactSynRoundOR_runs legacy ds hbody hA hLayer (by dsimp only [h]; omega)
    (by dsimp only [h]; omega) hW _ (hv.setH hcd hct h) P₀ (synIterO (compactSynOQ ds M K es ℓ W l p) j z)
    (synIterO_inv _ (compactSynInvR_O hinv) ⟨hz,hzg⟩ j).1 Y (synNum_ynum (synIterO_inv _ (compactSynInvR_O hinv) ⟨hz,hzg⟩ j).2) _ hviewH (hready.update_wire (.p .h) _)
  rw [synNum_stream hY'] at er
  have hclen : (Rj (compactSynDispatchReg (.p .t))).length=h+1 := by
    rw [compactSynView_wire hview]
    simp only [vj,Function.update_self,List.length_reverse,List.length_take]
    have hcs : cs.length=A := hvc
    dsimp only [h]
    omega
  have hhs : Rj (compactSynDispatchReg (.p .h))=[] := by
    rw [compactSynView_wire hview]; simpa [vj] using hvh
  have hts : Rj (compactSynDispatchReg (.s 2))=[] := by
    rw [compactSynView_wire hview]; simpa [vj] using hv.hs 2
  have hst : synStashCostW (synSetH v (cs.drop (j+1)) (cs.take (j+1)).reverse h) synXS≤
      synStashCostW v synXS+6*A+6 := by
    have he := synStashCostW_setH v (cs.drop (j+1)) (cs.take (j+1)).reverse h
    simp only [List.length_drop,List.length_reverse,List.length_take] at he
    have hcs : cs.length=A := hvc
    dsimp only [h] at he ⊢
    omega
  have eb := compactCounterBody_runs (compactMainBodyR legacy ds)
    (compactSynDispatchReg_injective.ne (by decide : SynW.p .t≠.p .h))
    (compactSynDispatchReg_injective.ne (by decide : SynW.p .t≠.s 2))
    (compactSynDispatchReg_injective.ne (by decide : SynW.p .h≠.s 2))
    (compactSynDispatchReg_ne_io (.p .h)) hhs hts true _
    (by simpa only [ite_true,hclen,Nat.add_sub_cancel] using er)
  apply lr_weaken (compactMainBodyR legacy ds) eb
  · exact compactScan_update_io R (compactSynDispatchReg_ne_io (.p .c))
      (compactSynDispatchReg_ne_io (.p .t)) _ _ _ _
  · have he := compactSynRoundOCostR_mono (Ka := Ka) ds M K es ℓ W l h hst
    simp only [ite_true,hclen,Nat.add_sub_cancel]
    dsimp only [h] at he ⊢
    omega

theorem compactSynLoopOR_runs (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions)
    (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
    (hA : 5≤prime+Ka) {M K : ℕ} {es : List ℕ} {ℓ W l p A : ℕ}
    (hLayer : CompactSynLayerContractR legacy ds M K es ℓ W l p)
    (hAℓ : A≤ℓ) (hAl : A≤l+1) (hW : p+2≤W)
    (v : SynW → List (Fin (prime+Ka+4)))
    (hv : SynV v es ℓ K W l 0 (layPerm es ℓ K))
    (hvh : v (.p .h)=[]) (hvt : v (.p .t)=[]) (hvc : (v (.p .c)).length=A) (hcb : blank∉v (.p .c))
    (P₀ : List (Fin (prime+Ka+4))) (z : Recs (2^l)) (hz : SupLe es.sum z 1) (hzg : GridR p z)
    (hinv : CompactSynInvR ds M K es ℓ W l p)
    (R : Fin compactMnT → List (Fin (prime+Ka+4)))
    (hR : compactSynView R=synG (synIdle (cstream (prime+Ka) W
      (rpStream (2^es.sum) (synYnum p (layPerm es ℓ K) z))) P₀) v)
    (hr : CompactSynReady R M) :
    LayRuns (compactMainBodyR legacy ds) (compactSynLoopOR ds) R
      (Function.update R (compactMnRg (.src (.v .io))) (cstream (prime+Ka) W (rpStream (2^es.sum)
        (synYnum p (layPerm es ℓ K) (synIterO (compactSynOQ ds M K es ℓ W l p) A z)))))
      (compactSynLoopOCostR (Ka := Ka) ds M K es ℓ W l A (synStashCostW v synXS+6*A+6)) := by
  let cs := v (.p .c)
  let L := layPerm es ℓ K
  let Φ := fun j => Function.update R (compactMnRg (.src (.v .io)))
    (cstream (prime+Ka) W (rpStream (2^es.sum) (synYnum p L (synIterO (compactSynOQ ds M K es ℓ W l p) j z))))
  let cost := fun j => (4*(j+1)+4)+1+compactSynRoundOCostR (Ka := Ka) ds M K es ℓ W l j
    (synStashCostW v synXS+6*A+6)+(2*j+2)
  have hstep : ∀ j<cs.length,LayRuns (compactMainBodyR legacy ds) (compactSynBodyOR ds)
      (Function.update (Function.update (Φ j) (compactSynDispatchReg (.p .c)) (cs.drop (j+1)))
        (compactSynDispatchReg (.p .t)) (cs.take (j+1)).reverse)
      (Function.update (Function.update (Φ (j+1)) (compactSynDispatchReg (.p .c)) (cs.drop (j+1)))
        (compactSynDispatchReg (.p .t)) (cs.take (j+1)).reverse) (cost j) := by
    intro j hj
    exact compactSynLoopOR_step legacy ds hbody hA hLayer hAℓ hAl hW v hv hvh hvc hcb P₀ z hz hzg hinv R hR hr j
      (by change j<(v (.p .c)).length at hj; rwa [hvc] at hj)
  have he := layScan_exec (body := compactMainBodyR legacy ds)
    (compactSynDispatchReg_injective.ne (by decide : SynW.p .c≠.p .t)) Φ cs cost hstep
  have hcs : cs.length=A := hvc
  rw [hcs] at he
  have hc : R (compactSynDispatchReg (.p .c))=cs := compactSynView_wire hR _
  have ht : R (compactSynDispatchReg (.p .t))=[] := (compactSynView_wire hR _).trans hvt
  have hstart : Function.update (Function.update (Φ 0) (compactSynDispatchReg (.p .c)) cs)
      (compactSynDispatchReg (.p .t)) []=R := by
    rw [←hc,←ht]
    rw [compactScan_restore R (compactSynDispatchReg_ne_io (.p .c)) (compactSynDispatchReg_ne_io (.p .t))]
    dsimp only [L,synIterO]
    rw [←compactSynView_io_value hR,Function.update_eq_self]
  have hend : Function.update (Function.update (Φ A) (compactSynDispatchReg (.p .c)) cs)
      (compactSynDispatchReg (.p .t)) []=
      Function.update R (compactMnRg (.src (.v .io))) (cstream (prime+Ka) W (rpStream (2^es.sum)
        (synYnum p L (synIterO (compactSynOQ ds M K es ℓ W l p) A z)))) := by
    rw [←hc,←ht]
    rw [compactScan_restore R (compactSynDispatchReg_ne_io (.p .c)) (compactSynDispatchReg_ne_io (.p .t))]
  exact lr_weaken (compactMainBodyR legacy ds) (lr_congr_left _ he hstart.symm) hend (by rfl)

def CompactSynLoopContractR (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions) (M K : ℕ) (es : List ℕ) (ℓ W l p : ℕ) (fwd : Bool) : Prop :=
  ∀ (A : ℕ),A≤ℓ → A≤l+1 → ∀ (v : SynW → List (Fin (prime+Ka+4))),
    SynV v es ℓ K W l 0 (layPerm es ℓ K) →
    v (.p .h)=[] → v (.p .t)=[] → (v (.p .c)).length=A → blank∉v (.p .c) →
    ∀ (P₀ : List (Fin (prime+Ka+4))) (z : Recs (2^l)),SupLe es.sum z 1 → GridR p z → CompactSynInvR ds M K es ℓ W l p →
    ∀ (R : Fin compactMnT → List (Fin (prime+Ka+4))),
    compactSynView R=synG (synIdle (cstream (prime+Ka) W
      (rpStream (2^es.sum) (synYnum p (layPerm es ℓ K) z))) P₀) v →
    CompactSynReady R M →
    LayRuns (compactMainBodyR legacy ds) (if fwd then compactSynLoopFR ds else compactSynLoopOR ds) R
      (Function.update R (compactMnRg (.src (.v .io))) (cstream (prime+Ka) W (rpStream (2^es.sum)
        (synYnum p (layPerm es ℓ K)
          (if fwd then synIterF (compactSynFQ ds M K es ℓ W l p) A z else synIterO (compactSynOQ ds M K es ℓ W l p) A z)))))
      (if fwd then compactSynLoopFCostR (Ka := Ka) ds M K es ℓ W l A (synStashCostW v synXS+6*A+6)
        else compactSynLoopOCostR (Ka := Ka) ds M K es ℓ W l A (synStashCostW v synXS+6*A+6))

theorem compactSynLoopsContractR_of_layer (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions)
    (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
    (hA : 5≤prime+Ka) {M K : ℕ} {es : List ℕ} {ℓ W l p : ℕ}
    (hLayer : CompactSynLayerContractR legacy ds M K es ℓ W l p) (hW : p+2≤W) :
    ∀ fwd,CompactSynLoopContractR legacy ds M K es ℓ W l p fwd := by
  intro fwd A hAℓ hAl v hv hvh hvt hvc hcb P₀ z hz hzg hinv R hR hr
  cases fwd
  · exact compactSynLoopOR_runs legacy ds hbody hA hLayer hAℓ hAl hW v hv hvh hvt hvc hcb P₀ z hz hzg hinv R hR hr
  · exact compactSynLoopFR_runs legacy ds hbody hA hLayer hAℓ hAl hW v hv hvh hvt hvc hcb P₀ z hz hzg hinv R hR hr


theorem compactSynLoopsContractR_eventually (hA : 21≤prime+Ka)
    (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4) :
    ∀ᶠ M : ℕ in Filter.atTop,
    ∀ (ds : ComplexFramedExecution.Directions),ComplexPhaseBudget.Realizes ds →
      (∀ g,Instr.gate g∈program ds → (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4) →
    ∀ (legacy : MnProc → MnPr (prime+Ka)),
      (∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f)) →
    ∀ (es : List ℕ) (ℓ W l p : ℕ),CompactSynGeometry M es ℓ W l p →
      CompactSynFitsR ds M (Mult.Sizes.K M) es ℓ W l p →
      ∀ fwd,CompactSynLoopContractR legacy ds M (Mult.Sizes.K M) es ℓ W l p fwd := by
  filter_upwards [compactSynLayerContractR_eventually hA hA9 hNW] with M hLayer
  intro ds hd hgate legacy hbody es ℓ W l p hg hfits
  exact compactSynLoopsContractR_of_layer legacy ds hbody (by omega)
    (hLayer ds hd hgate legacy hbody es ℓ W l p hg hfits) hg.numerator

theorem compactSynUniformLoopsContractR_eventually (hA : 21≤prime+Ka)
    (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4) :
    ∀ᶠ M : ℕ in Filter.atTop,
    ∀ (ds : ComplexFramedExecution.Directions),ComplexPhaseBudget.Realizes ds →
      (∀ g,Instr.gate g∈program ds → (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4) →
    ∀ (legacy : MnProc → MnPr (prime+Ka)),
      (∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f)) →
    ∀ (es : List ℕ) (K ℓ W l p : ℕ),CompactSynUniformGeometry M K es ℓ W l p →
      CompactSynFitsR ds M K es ℓ W l p →
      ∀ fwd,CompactSynLoopContractR legacy ds M K es ℓ W l p fwd := by
  filter_upwards [compactSynUniformLayerContractR_eventually hA hA9 hNW] with M hLayer
  intro ds hd hgate legacy hbody es K ℓ W l p hg hfits
  exact compactSynLoopsContractR_of_layer legacy ds hbody (by omega)
    (hLayer ds hd hgate legacy hbody es K ℓ W l p hg hfits) hg.numerator

end
end IntegerMultBounds.MathlibTM2.Fast.Main
