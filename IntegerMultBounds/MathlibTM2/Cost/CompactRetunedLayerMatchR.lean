module

import IntegerMultBounds.MathlibTM2.Cost.CompactCallerOverheadR
import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedCallerTopCost
import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedCallerSlack
import IntegerMultBounds.MathlibTM2.Cost.CompactCallerRetunedCapacity
import IntegerMultBounds.MathlibTM2.Cost.CompactCallerSelectedRows
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynHybridRoundR
import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerFitR
import IntegerMultBounds.MathlibTM2.Cost.CompactTopBoundR
public import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedTopGrowth
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! The rounded compact chunk round against its original stream volume: the rounded top at the
actual caller records, at any working width that holds the shifts and the child scales, and the
whole rounded chunk round `compactSynLayerCostR`. The bound has the shape of
`compactRetuned_layer_chunk_eventually`; the only new premise is `l ≤ p` on the ring exponent. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
open CompactGadgetReservationCapacity Filter
noncomputable section

private theorem first_le_totalR (a b c d e : ℕ) (h : a+b+c+d=e) : a≤e := by omega

private theorem addressGeometryR (N K D o qrow ρ : ℕ)
    (hq : qrow≤D) (hD : 0<D) (hρ : ρ<K) (haddr : o+K*D≤N) :
    let n := o+K*(D-qrow)
    let a := N-n
    n+a=N ∧ qrow*K≤a ∧ o≤n ∧ ρ+o≤N ∧ D*K≤N := by
  have he : K*(D-qrow)+qrow*K=K*D := by
    rw [Nat.mul_comm qrow K,←Nat.mul_add,Nat.sub_add_cancel hq]
  have hKD : K≤K*D := Nat.le_mul_of_pos_right _ hD
  have hDK : D*K=K*D := Nat.mul_comm _ _
  dsimp only
  omega

private theorem twiceEnvelope (A X B Q C : ℝ) (hB : 0≤B) (hQ : 0≤Q) (hC : 0≤C) :
    32768*A*X+512*B+512*Q+C≤2*(16384*A*X+512*B+512*Q+C) := by linarith

/-- **The rounded top at the actual caller records.** Any working width that holds the shifts,
the guard, the cut and the child scales `D+m+G` gives twice the retuned top coefficient. -/
theorem compactRetunedR_caller_top_cost (ds : ComplexFramedExecution.Directions)
    (M N D o W r ρ s gb s' working : ℕ) (hM : 2≤M)
    (hD : D≤Mult.Sizes.d M)
    (hfit : CompactReservationFits (Mult.Sizes.d M) (CompactReservationGrowth.guard M)
      (Mult.CompactSizes.K M) D)
    (haddr : o+Mult.CompactSizes.K M*D≤N)
    (hr : 1≤r) (hW : 1≤W) (hNW : N≤r*W)
    (hρ : ρ<Mult.CompactSizes.K M)
    (hactive : compactReservationActive (Mult.Sizes.d M) (CompactReservationGrowth.guard M)
      (Mult.CompactSizes.K M) D≠0)
    (hq : 1≤compactTopKernelCount (Mult.Sizes.d M) (CompactReservationGrowth.guard M)
      (Mult.CompactSizes.K M))
    (hal : Real.logb (m:ℝ) ((factorCount (program ds):ℝ)/NW)<CompactInterim.lam)
    (hsw : s+W≤working) (hgw : gb≤working) (hs'w : s'≤working) (hssw : (s-s')+W≤working)
    (hchild : D+m+gateCount (program ds)≤working) :
    let d := Mult.Sizes.d M
    let g := CompactReservationGrowth.guard M
    let K := Mult.CompactSizes.K M
    let n := o+K*(D-CompactGlobalRowPadding.rowAxes NW m d)
    let a := N-n
    let q := compactTopKernelCount d g K
    let aT := compactTopKernelOffset d g K D o
    let R₂ := compactTopRows d 1 a
    let shape := compactReservationShape d g K D (2^o*(3*(r*working)))
    let pcs := compactTopPcs d g K D o R₂
    (compactTopCostR W working s n a 1 r K ρ q aT o D R₂ gb s' 1 pcs
      (compactTopCallCostR ds shape 1 (n+a) o r working ρ ⟨0,q,1,aT⟩)
      (compactTopCallCostR ds shape 1 n o r working ρ):ℝ)≤
      2*compactRetunedTopCoeff 1 ds*((R₂*2^n*(r*working):ℕ):ℝ)*
        (Mult.Sizes.d M:ℝ)^CompactInterim.lam' := by
  let d := Mult.Sizes.d M
  let g := CompactReservationGrowth.guard M
  let K := Mult.CompactSizes.K M
  let qrow := CompactGlobalRowPadding.rowAxes NW m d
  let n := o+K*(D-qrow)
  let a := N-n
  let q := compactTopKernelCount d g K
  let aT := compactTopKernelOffset d g K D o
  let R₂ := compactTopRows d 1 a
  let shape := compactReservationShape d g K D (2^o*(3*(r*working)))
  have hK : 0<K := Mult.CompactSizes.one_le_K hM
  have hqD : qrow≤D := first_le_totalR _ _ _ _ _ (compactReservation_axes hfit)
  have hactiveD : compactReservationActive d g K D≤D :=
    ((Nat.sub_le _ _).trans (Nat.sub_le _ _)).trans (Nat.sub_le _ _)
  have hDpos : 0<D := (Nat.pos_of_ne_zero hactive).trans_le hactiveD
  obtain ⟨htotal,ha,hon,hρN,hDK⟩ := addressGeometryR N K D o qrow ρ hqD hDpos hρ haddr
  have hworking : W≤working := by omega
  have hw : 1≤working := hW.trans hworking
  have hN : n+a≤r*working := htotal.le.trans (hNW.trans (Nat.mul_le_mul_left r hworking))
  have hbits : shape.bits≤n-o := by
    rw [compactReservation_bits hK hfit]
    exact (Nat.add_sub_cancel_left o (K*(D-qrow))).symm.le
  have hker := (compactTopKernel_geometry (o := o) hfit hρ ha).2
  have hqa : o≤aT := Nat.le_add_right _ _
  have hcap : 2^a*1≤R₂ := by
    simpa only [Nat.mul_one,Nat.one_mul] using (compactTopRows_bounds hK (by decide : 0<1) ha).1
  have hpcs := compactTop_working_pcs_ok ds hK (by decide : 0<1) hfit hD ha (w := W) (oS := o)
  have hpcsR : ∀ pc∈compactTopPcs d g K D o R₂,pc.OkR K n R₂ := fun pc hpc => (hpcs pc hpc).okR
  have hpf := compactTopPcs_facts (o := o) (R₂ := R₂) hfit
  have hpcsS : ∀ pc∈compactTopPcs d g K D o R₂,TopPcOkS ds K n working R₂ pc := by
    intro pc hpc
    have hR := hpcsR pc hpc
    refine ⟨hR.hu,hR.hR₀,hR.hR,fun i _ => ?_,hR.hfit⟩
    have hu := (hpf.2 pc hpc).2
    cases i with
    | zero => simp only [expSeq]; omega
    | succ i => rw [expSeq,Nat.zero_mul,Nat.add_zero]; omega
  have hgA := compactRetuned_caller_guard hM
  have hG : 1≤shape.guard := by
    change 1≤g
    dsimp only [g]
    rw [hgA]
    change 1≤4*Nat.clog 2 (Mult.Sizes.p M)+6
    omega
  have hd : 1≤d := Mult.Sizes.one_le_d hM
  have h := compactTopCostR_complete (lam:=CompactInterim.lam) ds shape 1 d g K D o R₂ W working s n a
    1 r ρ o q aT gb s' 1 hd hD hactive rfl hK (le_refl 1) hr hw hρ hG hon (le_refl o) hbits rfl
    hsw hgw hs'w hssw (le_refl 1) hN (hρN.trans htotal.ge) (hDK.trans htotal.ge) hker hqa hq hcap
    (by norm_num [CompactInterim.lam]) (by norm_num [Parameters.tau,CompactInterim.lam]) hal hpcsR hpcsS
    (fun _ hp => compactTopPcs_offset hp)
  have henv := compactRetuned_top_envelope 1 ds M hM D hD
  unfold compactRetunedTopEnvelope at henv
  simp only [←hgA] at henv
  change _≤((R₂*2^n*(r*working):ℕ):ℝ)*
    (32768*compactTopCountConst CompactInterim.lam*(d:ℝ)^CompactInterim.lam+
     512*(backChunks d g K:ℝ)+512*(q:ℝ)+
     compactDigitSumConst (compactLayerClosedConst (nT CompactBReg) 1 ds CompactInterim.lam) m
       CompactInterim.lam*(compactReservationActive d g K D:ℝ)^CompactInterim.lam*
       (g:ℝ)^Parameters.tau) at h
  have hC : 0≤compactDigitSumConst (compactLayerClosedConst (nT CompactBReg) 1 ds CompactInterim.lam) m
      CompactInterim.lam := (compactLayerDyadic_pos _).le
  have hCt : 0≤compactDigitSumConst (compactLayerClosedConst (nT CompactBReg) 1 ds CompactInterim.lam) m
      CompactInterim.lam*(compactReservationActive d g K D:ℝ)^CompactInterim.lam*(g:ℝ)^Parameters.tau :=
    mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have htwice := twiceEnvelope (compactTopCountConst CompactInterim.lam) ((d:ℝ)^CompactInterim.lam)
    (backChunks d g K:ℝ) (q:ℝ) _ (Nat.cast_nonneg _) (Nat.cast_nonneg _) hCt
  have hV : (0:ℝ)≤((R₂*2^n*(r*working):ℕ):ℝ) := Nat.cast_nonneg _
  have henv' : 16384*compactTopCountConst CompactInterim.lam*(d:ℝ)^CompactInterim.lam+
      512*(backChunks d g K:ℝ)+512*(q:ℝ)+
      compactDigitSumConst (compactLayerClosedConst (nT CompactBReg) 1 ds CompactInterim.lam) m
        CompactInterim.lam*(compactReservationActive d g K D:ℝ)^CompactInterim.lam*
        (g:ℝ)^Parameters.tau≤
      compactRetunedTopCoeff 1 ds*(d:ℝ)^CompactInterim.lam' := henv
  calc _ ≤ _ := h
    _ ≤ ((R₂*2^n*(r*working):ℕ):ℝ)*(2*(compactRetunedTopCoeff 1 ds*(d:ℝ)^CompactInterim.lam')) :=
        mul_le_mul_of_nonneg_left (htwice.trans (mul_le_mul_of_nonneg_left henv'
          (by norm_num : (0:ℝ)≤2))) hV
    _ = _ := by ring

/-- Fixed coefficient for the rounded compact round, including all setup passes. -/
def compactRetunedRoundCoeffR (ds : ComplexFramedExecution.Directions) : ℝ :=
  16*(32768+2*compactRetunedTopCoeff 1 ds)

private theorem mergeBoundR (overhead top V B stash : ℕ) (C P : ℝ)
    (ho : overhead≤32768*V+2*stash) (ht : (top:ℝ)≤2*C*(V:ℝ)*P)
    (hV : V≤16*B) (hC : 0≤C) (hP : 1≤P) :
    ((overhead+top:ℕ):ℝ)≤16*(32768+2*C)*(B:ℝ)*P+2*(stash:ℝ) := by
  have hoR : (overhead:ℝ)≤32768*(V:ℝ)+2*(stash:ℝ) := by exact_mod_cast ho
  have hVR : (V:ℝ)≤16*(B:ℝ) := by exact_mod_cast hV
  have hVP : (V:ℝ)≤(V:ℝ)*P := by nlinarith [Nat.cast_nonneg (α:=ℝ) V]
  have hmul := mul_le_mul_of_nonneg_right hVR
    (mul_nonneg (by linarith : 0≤32768+2*C) (by linarith : 0≤P))
  rw [Nat.cast_add]
  nlinarith only [hoR,ht,hVP,hmul]

/-- **Every rounded full-axis chunk** has a cost bound from layout and runtime size facts only,
with the new premise `l ≤ p` on the ring exponent and no power cap beyond `d^2 ≤ b`. -/
theorem compactRetunedR_layer_chunk_eventually {Ka : ℕ}
    (ds : ComplexFramedExecution.Directions) (c : ℕ)
    (hal : Real.logb (m:ℝ) ((factorCount (program ds):ℝ)/NW)<CompactInterim.lam) :
    ∀ᶠ M : ℕ in atTop, ∀ (es : List ℕ) (ℓ W l h stash : ℕ),
    LayHyp es ℓ (Mult.CompactSizes.K M) → es.length=Mult.Sizes.d M-1 →
    es.sum≤Mult.Sizes.p M → ℓ≤Mult.Sizes.p M →
    Mult.Sizes.r M≤2^l → l≤Mult.Sizes.p M → Mult.Sizes.p M≤W → W≤2^c*(Mult.Sizes.p M+1) →
    h+1≤ℓ → synChunk ℓ (Mult.CompactSizes.K M) h →
    (compactSynLayerCostR (Ka:=Ka) ds M (Mult.CompactSizes.K M) es ℓ W l h stash:ℝ)≤
      (compactSynDispatchCost ℓ (Mult.CompactSizes.K M) h:ℝ)+
      (compactRetunedRoundCoeffR ds*((2^es.sum*(2^l*W):ℕ):ℝ)*
        (Mult.Sizes.d M:ℝ)^CompactInterim.lam'+2*(stash:ℝ)) := by
  filter_upwards [eventually_ge_atTop 2,compactRetuned_caller_eventually_slack,
    compactCaller_retuned_eventually_full_dimension,
    compactCallerR_eventually_roundOverhead ds (cGain ds) c,
    compactCallerR_eventually_width (gateCount (program ds)) (cGain ds)]
    with M hM hslack hcapacity hover hwidth
  intro es ℓ W l h stash H hlen hN hℓ hrun hl hWp hW hh hchunk
  let d := Mult.Sizes.d M
  let g := CompactReservationGrowth.guard M
  let K := Mult.CompactSizes.K M
  let D := es.length
  let o := K*((h-layB ℓ K)/K*D)
  let ρ := (h-layB ℓ K)%K
  let r := 2^l
  let n := o+K*(D-CompactGlobalRowPadding.rowAxes NW m d)
  let a := es.sum-n
  let q := compactTopKernelCount d g K
  let aT := compactTopKernelOffset d g K D o
  let R₂ := compactTopRows d 1 a
  let E := backChunks d g K+
    synE (gateCount (program ds)) 0
      (compactReservationActive d g K D) (compactReservationActive d g K D)
  let gb := guardG (cGain ds) es.sum l D
  let s := (D+1)/2+q+(gb+E)
  let s' := gb+E-5
  let working := W+s+D+guardKc (cGain ds) es.sum l D+gateCount (program ds)+m+4
  have hK : 0<K := Mult.CompactSizes.one_le_K hM
  have hD : D≤d := hlen.le.trans (Nat.sub_le _ _)
  have hfit : CompactReservationFits d g K D := by
    dsimp only [D]; rw [hlen]; exact hcapacity.1
  have hactive : compactReservationActive d g K D≠0 := by
    dsimp only [D]; rw [hlen]; exact hslack.1
  have hq : 1≤q := hslack.2.1
  have hinner : CompactGlobalRowPadding.rowAxes NW m d*K+3≤n := by
    have he := hslack.2.2 o
    simpa only [←hlen] using he
  have haddr : o+K*D≤es.sum := by
    have he := synChunk_fit H hchunk
    simp only [synOS,hchunk.1,ite_true,Nat.not_lt.mpr hchunk.2,ite_false] at he
    exact (Nat.le_add_right _ _).trans he
  have hsplit := compactCaller_selected_split hfit haddr
  have ha : CompactGlobalRowPadding.rowAxes NW m d*K≤a := by
    dsimp only [a,n]
    rw [hsplit]
    exact Nat.le_add_right _ _
  have hn : n≤es.sum :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left K (Nat.sub_le _ _)) o).trans haddr
  have htotal : n+a=es.sum := Nat.add_sub_of_le hn
  have hρ : ρ<K := Nat.mod_lt _ hK
  have hr : 1≤r := Nat.one_le_two_pow
  have hWpos : 1≤W := by
    have hb := Mult.Sizes.one_le_b hM
    have hp : 1≤Mult.Sizes.p M := by unfold Mult.Sizes.p; omega
    exact hp.trans hWp
  have hNW : es.sum≤r*W := (hN.trans hWp).trans (Nat.le_mul_of_pos_left _ hr)
  have hhb : h≤Mult.Sizes.p M := (by omega : h≤ℓ).trans hℓ
  have hb : layB ℓ K≤Mult.Sizes.p M :=
    ((Nat.mod_le _ _).trans (Nat.sub_le ℓ 1)).trans hℓ
  have ho := hover es.sum D o W r h (layB ℓ K) l ρ stash hN hD hfit haddr hWp hW hhb hb hl hrun
    hρ hinner
  obtain ⟨hgbE,hwork⟩ := hwidth K D W es.sum l hD hfit hWp hN hl
  change gb+E≤4*W at hgbE
  change working≤8*W at hwork
  have hKc : guardKc (cGain ds) es.sum l D≤gb := by
    change guardKc (cGain ds) es.sum l D≤guardG (cGain ds) es.sum l D
    unfold guardG; omega
  have hwv : working=W+s+D+guardKc (cGain ds) es.sum l D+gateCount (program ds)+m+4 := rfl
  have hsv : s=(D+1)/2+q+(gb+E) := rfl
  have hs'v : s'=gb+E-5 := rfl
  have ht := compactRetunedR_caller_top_cost ds M es.sum D o W r ρ s gb s' working hM hD hfit
    haddr hr hWpos hNW hρ hactive hq hal (by omega) (by omega) (by omega) (by omega) (by omega)
  have hV : R₂*2^n*(r*working)≤16*(2^es.sum*(2^l*W)) := by
    have hrows : R₂≤2*(1*2^a) := (compactTopRows_bounds hK (by decide : 0<1) ha).2.2.1
    calc
      R₂*2^n*(r*working)≤(2*(1*2^a))*2^n*(r*(8*W)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ hrows) (Nat.mul_le_mul_left _ hwork)
      _ = 16*(2^(n+a)*(2^l*W)) := by rw [pow_add]; ring
      _ = 16*(2^es.sum*(2^l*W)) := by rw [htotal]
  have hP : (1:ℝ)≤(d:ℝ)^CompactInterim.lam' :=
    Real.one_le_rpow (by exact_mod_cast Mult.Sizes.one_le_d hM)
      (by norm_num [CompactInterim.lam'])
  have hC : 0≤compactRetunedTopCoeff 1 ds := (compactLayerDyadic_pos _).le
  have hbound := mergeBoundR _ _ _ _ stash (compactRetunedTopCoeff 1 ds)
    ((d:ℝ)^CompactInterim.lam') ho ht hV hC hP
  dsimp only [compactSynLayerCostR]
  rw [ite_eq_left hchunk]
  simp only [length_topRec',Nat.cast_add]
  dsimp only [compactRetunedRoundCoeffR,d,g,K,D,o,ρ,r] at hbound ⊢
  exact add_le_add (le_refl (compactSynDispatchCost ℓ K h:ℝ))
    (by simpa only [Nat.cast_add] using hbound)

end
end IntegerMultBounds.MathlibTM2.Cost
