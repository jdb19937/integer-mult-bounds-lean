module

public import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedCallerTopCost
public import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedCallerSlack
public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerUniformOverhead
public import IntegerMultBounds.MathlibTM2.Cost.CompactRoundVolume
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformLayerContract
public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerSelectedRows

/-! Matching the actual retuned hybrid chunk cost to its original stream volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
open CompactGadgetReservationCapacity Filter
noncomputable section

/-- Fixed coefficient for the actual compact round, including all setup passes. -/
def compactRetunedRoundCoeff (ds : ComplexFramedExecution.Directions) : ℝ :=
  4*(32768+compactRetunedTopCoeff 1 ds)

private theorem mergeBound (overhead top V B stash : ℕ) (C P : ℝ)
    (ho : overhead≤32768*V+2*stash) (ht : (top:ℝ)≤C*(V:ℝ)*P)
    (hV : V≤4*B) (hC : 0≤C) (hP : 1≤P) :
    ((overhead+top:ℕ):ℝ)≤4*(32768+C)*(B:ℝ)*P+2*(stash:ℝ) := by
  have hoR : (overhead:ℝ)≤32768*(V:ℝ)+2*(stash:ℝ) := by exact_mod_cast ho
  have hVR : (V:ℝ)≤4*(B:ℝ) := by exact_mod_cast hV
  have hVP : (V:ℝ)≤(V:ℝ)*P := by nlinarith [Nat.cast_nonneg (α:=ℝ) V]
  have hmul := mul_le_mul_of_nonneg_right hVR (mul_nonneg (by linarith : 0≤32768+C) (by linarith : 0≤P))
  rw [Nat.cast_add]
  nlinarith only [hoR,ht,hVP,hmul]

/-- Every actual full-axis chunk has a cost bound from layout and runtime size
facts only. Direct rounds are deliberately left to their exact branch cost. -/
theorem compactRetuned_layer_chunk_eventually {Ka : ℕ}
    (ds : ComplexFramedExecution.Directions) (c : ℕ)
    (hF : factorCount (program ds)+1≤m^5)
    (hal : Real.logb (m:ℝ) ((factorCount (program ds):ℝ)/NW)<Parameters.lam) :
    ∀ᶠ M : ℕ in atTop, ∀ (es : List ℕ) (ℓ W l h stash : ℕ),
    LayHyp es ℓ (Mult.CompactSizes.K M) → es.length=Mult.Sizes.d M-1 →
    es.sum≤Mult.Sizes.p M → ℓ≤Mult.Sizes.p M →
    Mult.Sizes.r M≤2^l → Mult.Sizes.p M≤W → W≤2^c*(Mult.Sizes.p M+1) →
    h+1≤ℓ → synChunk ℓ (Mult.CompactSizes.K M) h →
    (compactSynUniformLayerCost (Ka:=Ka) ds M (Mult.CompactSizes.K M) es ℓ W l h stash:ℝ)≤
      (compactSynDispatchCost ℓ (Mult.CompactSizes.K M) h:ℝ)+
      (compactRetunedRoundCoeff ds*((2^es.sum*(2^l*W):ℕ):ℝ)*
        (Mult.Sizes.d M:ℝ)^CompactInterim.lam'+2*(stash:ℝ)) := by
  filter_upwards [eventually_ge_atTop 2,compactRetuned_caller_eventually_slack,
    compactCaller_retuned_eventually_full_dimension,
    compactCaller_retuned_eventually_roundOverhead ds c hF,
    compactCaller_uniform_eventually_workingWidth (gateCount (program ds)) (factorCount (program ds)) hF]
    with M hM hslack hcapacity hover hwidth
  intro es ℓ W l h stash H hlen hN hℓ hrun hWp hW hh hchunk
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
  let shift := (D+1)/2+q+(backChunks d g K+
    synE (gateCount (program ds)) (factorCount (program ds))
      (compactReservationActive d g K D) (compactReservationActive d g K D))
  let w := W+shift+D
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
  have ho := hover es.sum D o W r h (layB ℓ K) ρ stash hN hD hfit haddr hWp hW hhb hb hrun hρ hinner
  have ht := compactRetuned_caller_top_cost ds M es.sum D o W r ρ hM hD hfit haddr hr hWpos hNW hρ hactive hq hal
  have hw := hwidth K D W hD hfit hWp
  have hV := (compactTopWorkingVolume_bounds d K 1 a n r W shift D es.sum hK (by decide) ha htotal hw.1).2
  simp only [Nat.one_mul] at hV
  have hP : (1:ℝ)≤(d:ℝ)^CompactInterim.lam' :=
    Real.one_le_rpow (by exact_mod_cast Mult.Sizes.one_le_d hM)
      (by norm_num [CompactInterim.lam'])
  have hC : 0≤compactRetunedTopCoeff 1 ds := (compactLayerDyadic_pos _).le
  have hbound := mergeBound _ _ _ _ stash (compactRetunedTopCoeff 1 ds)
    ((d:ℝ)^CompactInterim.lam') ho ht hV hC hP
  dsimp only [compactSynUniformLayerCost]
  rw [ite_eq_left hchunk]
  simp only [length_topRec',Nat.cast_add]
  dsimp only [compactTopKernelCount,compactTopKernelOffset,compactRetunedRoundCoeff,
    d,g,K,D,o,ρ,r] at hbound ⊢
  exact add_le_add (le_refl (compactSynDispatchCost ℓ K h:ℝ))
    (by simpa only [Nat.cast_add] using hbound)

end
end IntegerMultBounds.MathlibTM2.Cost
