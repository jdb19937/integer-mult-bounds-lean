module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepR
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepUniformR
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynHybridRound

/-! The rounded dispatch: the main procedure table with the placed rounded layer table, the
rounded chunk round `compactSynLayerStepR` placed on the main machine, and the whole dispatch
round. The chunk output is `compactSynChunkR`; the direct rounds are unchanged.
`CompactSynFitsR` collects the width hypotheses of the rounded top for every chunk round. -/
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

/-! ### The rounded main procedure table -/

private theorem placedLayRunsR {T T' Q A : ℕ} {U P P' : Type}
    (e : Fin T → Fin T') (he : Function.Injective e) (ι : P → P')
    {body : P → Pr P T Q A U} {body' : P' → Pr P' T' Q A U}
    (hbody : ∀ f,body' (ι f)=embProg e ι (body f))
    {p : Pr P T Q A U} {R₀ R₁ : Fin T → List (Fin (A+4))} {c : ℕ}
    (h : LayRuns body p R₀ R₁ c) (R : Fin T' → List (Fin (A+4))) (hR : R ∘ e=R₀) :
    LayRuns body' (embProg e ι p) R (embExt e R₁ R) c := by
  intro v S hL hS
  obtain ⟨w,k,hu,hc,hex⟩ := h (embDn e v) (embStk e S) (fun i => hL (e i))
    (by change S.R ∘ e=R₀; rw [hS]; exact hR)
  obtain ⟨v',hv,hu',hex'⟩ := exec_emb_ovr he hbody hex v rfl S rfl
  refine ⟨v',k,hu'.trans hu,hc,Exec.cast hex' rfl ?_⟩
  apply congrArg (mk v')
  simp only [embOvr,embStk,Stacks.get,embExt_comp,hS]

def compactMainNativeTableR (ds : ComplexFramedExecution.Directions) :
    LProc → CompactMnPr CompactMainProc (prime+Ka) := fun f =>
  embProg compactMnLayerReg compactMainLayerProc
    (compactPlacedLayerTableR (Ka := Ka) (U := Unit) compactMnQ_runtime ds f)

def compactMainBodyR (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions) :
    CompactMainProc → CompactMnPr CompactMainProc (prime+Ka) :=
  compactMainTransportTable legacy (compactMainNativeTableR ds)

def compactMainChunkR (ds : ComplexFramedExecution.Directions) :
    CompactMnPr CompactMainProc (prime+Ka) :=
  embProg compactMnLayerReg compactMainLayerProc (compactSynLayerStepR ds)

theorem compactMainChunkR_runs (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions)
    (R₀ : Fin (nT CompactHostBReg) → List (Fin (prime+Ka+4)))
    (R : Fin compactMnT → List (Fin (prime+Ka+4))) (io : List (Fin (prime+Ka+4)))
    (c : ℕ) (hR : R ∘ compactMnLayerReg=R₀)
    (h : LayRuns (compactPlacedLayerTableR (Ka := Ka) (U := Unit) compactMnQ_runtime ds)
      (compactSynLayerStepR ds) R₀ (Function.update R₀ (reg (BReg := CompactHostBReg) .io) io) c) :
    LayRuns (compactMainBodyR legacy ds) (compactMainChunkR ds) R
      (Function.update R (compactMnRg (.src (.v .io))) io) c := by
  have he : LayRuns (compactMainBodyR legacy ds) (compactMainChunkR ds) R
      (embExt compactMnLayerReg (Function.update R₀ (reg (BReg := CompactHostBReg) .io) io) R) c := by
    exact (placedLayRunsR compactMnLayerReg compactMnLayerReg_injective
      compactMainLayerProc (body' := compactMainBodyR legacy ds) (fun _ => rfl) h R hR)
  rw [compactMainLayer_io_restore R₀ R io hR] at he
  exact he

/-- The unchanged direct round under the rounded procedure table. -/
theorem compactMainDirectR_runs (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions) (hd : ComplexPhaseBudget.Realizes ds)
    (hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay
      (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
    (hA : 14≤prime+Ka) (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4)
    (hgate : ∀ g,Instr.gate g∈program ds → (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4)
    {es : List ℕ} {ℓ K : ℕ} (H : LayHyp es ℓ K) {l w p h : ℕ} (hh : h+1≤ℓ)
    (hpw : p+2≤w) (v : SynW → List (Fin (prime+Ka+4)))
    (hv : SynV v es ℓ K w l h (layPerm es ℓ K)) (P₀ : List (Fin (prime+Ka+4)))
    (Y : ℕ → Fin (2^l) → GaussianInt) (hY : ∀ x c,‖GaussianInt.toComplex (Y x c)‖≤2^p)
    (R : Fin compactMnT → List (Fin (prime+Ka+4)))
    (hR : (R ∘ compactMnLegacyReg) ∘ mnLayE=
      synG (synIdle (cstream (prime+Ka) w (rpStream (2^es.sum) Y)) P₀) v) :
    LayRuns (compactMainBodyR legacy ds) (compactMainDirect ds) R
      (Function.update R (compactMnRg (.src (.v .io)))
        (cstream (prime+Ka) w (rpStream (2^es.sum) (synTrunc
          (bflyL ((selBits es h).map (twPosL (layPerm es ℓ K)))
            (fun x c => GaussianInt.toComplex (Y x c)))))))
      (1+synLayerStepCost ds es ℓ K w l h (synStashCostW v synXS)) := by
  have he := sg_synLayerStep (U := Unit) mnQ_layer ds hd hA hA9 hNW hgate H hh hpw v hv P₀ Y hY
  have ei := compactLegacyLayer_runs legacy (compactMainNativeTableR ds)
    (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds) hbody he R hR
  have eio (io io' : List (Fin (prime+Ka+4))) :
      synG (synIdle io' P₀) v=Function.update (synG (synIdle io P₀) v) mnLio io' := by
    rw [synG_update_out (lreg_out (by simp)),synIdle_update_io]
  rw [eio (cstream (prime+Ka) w (rpStream (2^es.sum) Y)) _,
    compactLegacyLayer_io_restore _ R _ hR] at ei
  exact ei

def compactSynDispatchR (ds : ComplexFramedExecution.Directions) :
    CompactMnPr CompactMainProc (prime+Ka) :=
  compactSynDispatchWith (compactMainChunkR ds) (compactMainDirect ds)

/-! ### The rounded chunk output and its width hypotheses -/

open Classical in
/-- The records returned by the rounded chunk round at chunk width `K`. Off the geometry of the
chunk tables it is the input. -/
def compactSynChunkR (ds : ComplexFramedExecution.Directions) (M K : ℕ) (es : List ℕ)
    (ℓ W l h : ℕ) (Y : ℕ → Fin (2^l) → GaussianInt) : ℕ → Fin (2^l) → GaussianInt :=
  let d := Mult.Sizes.d M
  let g := CompactReservationGrowth.guard M
  let D := es.length
  let o := K*((h-layB ℓ K)/K*D)
  let ρ := (h-layB ℓ K)%K
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
  let pcs := compactTopPcs d g K D o R₂
  if hc : 1≤K ∧ CompactReservationFits d g K D ∧ D≤d ∧
      CompactGlobalRowPadding.rowAxes NW m d*K≤a then
    let hρ : ρ<K := Nat.mod_lt _ hc.1
    let hfitT := (compactTopKernel_geometry (o := o) hc.2.1 hρ hc.2.2.2).1
    let hpcs := compactTop_working_pcs_ok ds (oS := o) (R := 1) hc.1 (le_refl 1) hc.2.1 hc.2.2.1
      hc.2.2.2 (w := W)
    let hpcsR : ∀ pc∈pcs, pc.OkR K n R₂ := fun pc hpc => (hpcs pc hpc).okR
    let Ps := topPiecesR hρ pcs hpcsR
    let low := (topPieces hρ pcs hpcs).flatMap Piece.bitsList
    let hR₂ := (compactTopRows_bounds (Nat.lt_of_lt_of_le Nat.zero_lt_one hc.1) Nat.zero_lt_one
      hc.2.2.2).1
    synRd (topRSW ds working a low (topTop aT ρ K q (n+a) hfitT) hR₂ Ps gb s (1*2^s') (synZ (n+a) Y))
  else Y

theorem compactSynChunkR_of (ds : ComplexFramedExecution.Directions) (M K : ℕ) (es : List ℕ)
    (ℓ W l h : ℕ) (Y : ℕ → Fin (2^l) → GaussianInt) :
    let d := Mult.Sizes.d M
    let g := CompactReservationGrowth.guard M
    let D := es.length
    let o := K*((h-layB ℓ K)/K*D)
    let ρ := (h-layB ℓ K)%K
    let n := o+K*(D-CompactGlobalRowPadding.rowAxes NW m d)
    let a := es.sum-n
    ∀ (hKpos : 1≤K) (hcap : CompactReservationFits d g K D) (hD : D≤d)
      (ha : CompactGlobalRowPadding.rowAxes NW m d*K≤a),
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
    let pcs := compactTopPcs d g K D o R₂
    let hρ : ρ<K := Nat.mod_lt _ (by omega)
    let hfitT := (compactTopKernel_geometry (o := o) hcap hρ ha).1
    let hpcs := compactTop_working_pcs_ok ds (oS := o) (R := 1) hKpos (by omega : 1≤1) hcap hD ha (w := W)
    let hpcsR : ∀ pc∈pcs, pc.OkR K n R₂ := fun pc hpc => (hpcs pc hpc).okR
    let Ps := topPiecesR hρ pcs hpcsR
    let low := (topPieces hρ pcs hpcs).flatMap Piece.bitsList
    let hR₂ := (compactTopRows_bounds (by omega : 0<K) (by omega : 0<1) ha).1
    compactSynChunkR ds M K es ℓ W l h Y=
      synRd (topRSW ds working a low (topTop aT ρ K q (n+a) hfitT) hR₂ Ps gb s (1*2^s') (synZ (n+a) Y)) := by
  intro d g D o ρ n a hKpos hcap hD ha
  exact dite_eq_left_of_eq_true (eq_true ⟨hKpos,hcap,hD,ha⟩)

/-- The width hypotheses of the rounded top at every chunk round: the kernel scales fit the
working width, and so does the array before the final shift for every input in the disk. -/
def CompactSynFitsR (ds : ComplexFramedExecution.Directions) (M K : ℕ) (es : List ℕ)
    (ℓ W l p : ℕ) : Prop :=
  ∀ h,synChunk ℓ K h →
    let d := Mult.Sizes.d M
    let g := CompactReservationGrowth.guard M
    let D := es.length
    let o := K*((h-layB ℓ K)/K*D)
    let ρ := (h-layB ℓ K)%K
    let n := o+K*(D-CompactGlobalRowPadding.rowAxes NW m d)
    let a := es.sum-n
    ∀ (hKpos : 1≤K) (hcap : CompactReservationFits d g K D) (hD : D≤d)
      (ha : CompactGlobalRowPadding.rowAxes NW m d*K≤a),
    let q := compactTopKernelCount d g K
    let aT := compactTopKernelOffset d g K D o
    let R₂ := compactTopRows d 1 a
    let E := backChunks d g K+
      synE (gateCount (program ds)) 0
        (compactReservationActive d g K D) (compactReservationActive d g K D)
    let gb := guardG (cGain ds) es.sum l D
    let s := (D+1)/2+q+(gb+E)
    let working := W+s+D+guardKc (cGain ds) es.sum l D+gateCount (program ds)+m+4
    let pcs := compactTopPcs d g K D o R₂
    let hρ : ρ<K := Nat.mod_lt _ (by omega)
    let hfitT := (compactTopKernel_geometry (o := o) hcap hρ ha).1
    let hpcs := compactTop_working_pcs_ok ds (oS := o) (R := 1) hKpos (by omega : 1≤1) hcap hD ha (w := W)
    let hpcsR : ∀ pc∈pcs, pc.OkR K n R₂ := fun pc hpc => (hpcs pc hpc).okR
    let Ps := topPiecesR hρ pcs hpcsR
    let low := (topPieces hρ pcs hpcs).flatMap Piece.bitsList
    let hR₂ := (compactTopRows_bounds (by omega : 0<K) (by omega : 0<1) ha).1
    (∀ pc∈pcs, ∀ i<pc.j, scaleR pc.u ds i<working) ∧
    ∀ Y : ℕ → Fin (2^l) → GaussianInt,(∀ x c,‖GaussianInt.toComplex (Y x c)‖≤2^p) →
      ∀ z, TopFitsZ working (topPreRW ds working a low (topTop aT ρ K q (n+a) hfitT)
        hR₂ Ps gb (synZ (n+a) Y) z)

/-- The cost of the rounded dispatch round. -/
def compactSynLayerCostR (ds : ComplexFramedExecution.Directions) (M K : ℕ)
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
  let E := backChunks d g K+
    synE (gateCount (program ds)) 0
      (compactReservationActive d g K D) (compactReservationActive d g K D)
  let gb := guardG (cGain ds) es.sum l D
  let s := (D+1)/2+q+(gb+E)
  let s' := gb+E-5
  let working := W+s+D+guardKc (cGain ds) es.sum l D+gateCount (program ds)+m+4
  let shape := compactReservationShape d g K D (2^o*(3*(r*working)))
  let pcs := compactTopPcs d g K D o R₂
  let cfg := topCfgR W s a 1 R₂ q aT K o D gb s' 1
  let pfs := topPcRec K pcs
  compactSynDispatchCost ℓ K h+(if synChunk ℓ K h then
    (compactSynLayerRoundOverheadR (gateCount (program ds)) (cGain ds)
      es.sum d g K D o W r h (layB ℓ K) l ρ working
      (topRec pfs : List (Fin (prime+Ka+4))).length (topRec cfg : List (Fin (prime+Ka+4))).length
      stk+
      compactTopCostR W working s n a 1 r K ρ q aT o D R₂ gb s' 1 pcs
        (compactTopCallCostR ds shape 1 (n+a) o r working ρ ⟨0,q,1,aT⟩)
        (compactTopCallCostR ds shape 1 n o r working ρ)) else
      1+synLayerStepCost ds es ℓ K W l h stk)

/-! ### The rounded dispatch round -/

theorem compactSynDispatchR_eventually_exec_stream
    (hA : 21≤prime+Ka) (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4) :
    ∀ᶠ M : ℕ in atTop,
    ∀ (ds : ComplexFramedExecution.Directions) (_hd : ComplexPhaseBudget.Realizes ds)
      (_hgate : ∀ g,Instr.gate g∈program ds → (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4)
      (legacy : MnProc → MnPr (prime+Ka))
      (_hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay
        (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
      (es : List ℕ) (ℓ W l h p : ℕ),
    let d := Mult.Sizes.d M
    let g := CompactReservationGrowth.guard M
    let K := Mult.Sizes.K M
    let D := es.length
    ∀ (_hdpos : 0<d) (_hKpos : 1≤K) (_H : LayHyp es ℓ K) (_hh : h+1≤ℓ)
      (_hcap : synChunk ℓ K h → CompactReservationFits d g K D) (_hD : D≤d)
      (_hprecision : es.sum+1≤Mult.Sizes.p M)
      (_hrun : Mult.Sizes.r M≤2^l) (_hwrun : Mult.Sizes.p M≤W) (_hW : p+2≤W)
      (_hfits : CompactSynFitsR ds M K es ℓ W l p)
      (v : SynW → List (Fin (prime+Ka+4)))
      (_hv : SynV v es ℓ K W l h (layPerm es ℓ K)) (P₀ : List (Fin (prime+Ka+4)))
      (Y : ℕ → Fin (2^l) → GaussianInt)
      (_hY : ∀ x c,‖GaussianInt.toComplex (Y x c)‖≤2^p)
      (R : Fin compactMnT → List (Fin (prime+Ka+4)))
      (_hlegacy : (R ∘ compactMnLegacyReg) ∘ mnLayE=synG (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Y)) P₀) v)
      (_hblank : ∀ z : CompactBReg,z≠.work 13 → z≠.work 14 →
        R (compactMnLayerReg (reg (BReg := CompactHostBReg) (.bc (.inl z))))=[])
      (_hdepth : (R (compactMnLayerReg (reg (BReg := CompactHostBReg) (.bc (.inl (.work 13)))))).length=d)
      (_hguard : (R (compactMnLayerReg (reg (BReg := CompactHostBReg) (.bc (.inl (.work 14)))))).length=g),
    LayRuns (compactMainBodyR legacy ds) (compactSynDispatchR ds) R
      (Function.update R (compactMnRg (.src (.v .io))) (cstream (prime+Ka) W (rpStream (2^es.sum)
        (if synChunk ℓ K h then compactSynChunkR ds M K es ℓ W l h Y else synTrunc
          (bflyL ((selBits es h).map (twPosL (layPerm es ℓ K)))
            (fun x c => GaussianInt.toComplex (Y x c)))))))
      (compactSynLayerCostR (Ka := Ka) ds M K es ℓ W l h (synStashCostW v synXS)) := by
  filter_upwards [compactSynLayerStepR_eventually_exec_stream (Ka := Ka) (U := Unit)
    compactMnQ_runtime hA hA9 hNW] with M hexec
  intro ds hd hgate legacy hbody es ℓ W l h p
  dsimp only
  intro hdpos hKpos H hh hcap hD hprecision hrun hwrun hW hfits v hv P₀ Y hY R hlegacy hblank hdepth hguard
  have hwire (x : SynW) : R (compactSynDispatchReg x)=v x := by
    change (((R ∘ compactMnLegacyReg) ∘ mnLayE) (sreg x))=v x
    rw [hlegacy,synG_sreg]
  apply compactSynDispatchWith_runs (compactMainBodyR legacy ds) hv hwire
  · intro hc
    have haddr := synChunk_fit H hc
    simp only [synOS,hc.1,ite_true,Nat.not_lt.mpr hc.2,ite_false] at haddr
    have hfit := (Nat.le_add_right _ _).trans haddr
    have ha := compactCaller_selected_split (hcap hc) hfit
    have ha' : CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d M)*Mult.Sizes.K M≤
        es.sum-(Mult.Sizes.K M*((h-layB ℓ (Mult.Sizes.K M))/Mult.Sizes.K M*es.length)+
          Mult.Sizes.K M*(es.length-CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d M))) := by
      rw [ha]; omega
    have hproj : (R ∘ compactMnLayerReg) ∘ compactLegacyReg=
        synG (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Y)) P₀) v := by
      rw [←hlegacy]
      funext i
      exact congrArg R (compactMnLayerReg_legacy i)
    have hF := hfits h hc hKpos (hcap hc) hD ha'
    have e := hexec ds hgate es ℓ W l h p hdpos hKpos hc H (hcap hc) hD
      hfit ha' hprecision hrun hwrun hW hF.1 v (layPerm es ℓ (Mult.Sizes.K M))
      hv P₀ Y hY (hF.2 Y hY) (R ∘ compactMnLayerReg) hproj hblank hdepth hguard
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc),compactSynChunkR_of ds M (Mult.Sizes.K M) es ℓ W l h Y hKpos (hcap hc) hD ha']
    exact compactMainChunkR_runs legacy ds (R ∘ compactMnLayerReg) R _ _ rfl e
  · intro hc
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    exact compactMainDirectR_runs legacy ds hd hbody (by omega) hA9 hNW hgate H hh hW v hv P₀ Y hY R hlegacy


theorem compactSynDispatchR_uniform_eventually_exec_stream
    (hA : 21≤prime+Ka) (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4) :
    ∀ᶠ M : ℕ in atTop,
    ∀ (ds : ComplexFramedExecution.Directions) (_hd : ComplexPhaseBudget.Realizes ds)
      (_hgate : ∀ g,Instr.gate g∈program ds → (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4)
      (legacy : MnProc → MnPr (prime+Ka))
      (_hbody : ∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay
        (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f))
      (es : List ℕ) (K ℓ W l h p : ℕ),
    let d := Mult.Sizes.d M
    let g := CompactReservationGrowth.guard M
    let D := es.length
    ∀ (_hlo : Mult.Sizes.K M≤K) (_hhi : K≤d) (_hdpos : 0<d) (_hKpos : 1≤K) (_H : LayHyp es ℓ K) (_hh : h+1≤ℓ)
      (_hcap : synChunk ℓ K h → CompactReservationFits d g K D) (_hD : D≤d)
      (_hprecision : es.sum+1≤Mult.Sizes.p M)
      (_hrun : Mult.Sizes.r M≤2^l) (_hwrun : Mult.Sizes.p M≤W) (_hW : p+2≤W)
      (_hfits : CompactSynFitsR ds M K es ℓ W l p)
      (v : SynW → List (Fin (prime+Ka+4)))
      (_hv : SynV v es ℓ K W l h (layPerm es ℓ K)) (P₀ : List (Fin (prime+Ka+4)))
      (Y : ℕ → Fin (2^l) → GaussianInt)
      (_hY : ∀ x c,‖GaussianInt.toComplex (Y x c)‖≤2^p)
      (R : Fin compactMnT → List (Fin (prime+Ka+4)))
      (_hlegacy : (R ∘ compactMnLegacyReg) ∘ mnLayE=synG (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Y)) P₀) v)
      (_hblank : ∀ z : CompactBReg,z≠.work 13 → z≠.work 14 →
        R (compactMnLayerReg (reg (BReg := CompactHostBReg) (.bc (.inl z))))=[])
      (_hdepth : (R (compactMnLayerReg (reg (BReg := CompactHostBReg) (.bc (.inl (.work 13)))))).length=d)
      (_hguard : (R (compactMnLayerReg (reg (BReg := CompactHostBReg) (.bc (.inl (.work 14)))))).length=g),
    LayRuns (compactMainBodyR legacy ds) (compactSynDispatchR ds) R
      (Function.update R (compactMnRg (.src (.v .io))) (cstream (prime+Ka) W (rpStream (2^es.sum)
        (if synChunk ℓ K h then compactSynChunkR ds M K es ℓ W l h Y else synTrunc
          (bflyL ((selBits es h).map (twPosL (layPerm es ℓ K)))
            (fun x c => GaussianInt.toComplex (Y x c)))))))
      (compactSynLayerCostR (Ka := Ka) ds M K es ℓ W l h (synStashCostW v synXS)) := by
  filter_upwards [compactSynLayerStepR_uniform_eventually_exec_stream (Ka := Ka) (U := Unit)
    compactMnQ_runtime hA hA9 hNW] with M hexec
  intro ds hd hgate legacy hbody es K ℓ W l h p
  dsimp only
  intro hlo hhi hdpos hKpos H hh hcap hD hprecision hrun hwrun hW hfits v hv P₀ Y hY R hlegacy hblank hdepth hguard
  have hwire (x : SynW) : R (compactSynDispatchReg x)=v x := by
    change (((R ∘ compactMnLegacyReg) ∘ mnLayE) (sreg x))=v x
    rw [hlegacy,synG_sreg]
  apply compactSynDispatchWith_runs (compactMainBodyR legacy ds) hv hwire
  · intro hc
    have haddr := synChunk_fit H hc
    simp only [synOS,hc.1,ite_true,Nat.not_lt.mpr hc.2,ite_false] at haddr
    have hfit := (Nat.le_add_right _ _).trans haddr
    have ha := compactCaller_selected_split (hcap hc) hfit
    have ha' : CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d M)*K≤
        es.sum-(K*((h-layB ℓ K)/K*es.length)+
          K*(es.length-CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d M))) := by
      rw [ha]; omega
    have hproj : (R ∘ compactMnLayerReg) ∘ compactLegacyReg=
        synG (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Y)) P₀) v := by
      rw [←hlegacy]
      funext i
      exact congrArg R (compactMnLayerReg_legacy i)
    have hF := hfits h hc hKpos (hcap hc) hD ha'
    have e := hexec ds hgate es K ℓ W l h p hlo hhi hdpos hKpos hc H (hcap hc) hD
      hfit ha' hprecision hrun hwrun hW hF.1 v (layPerm es ℓ K)
      hv P₀ Y hY (hF.2 Y hY) (R ∘ compactMnLayerReg) hproj hblank hdepth hguard
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc),compactSynChunkR_of ds M K es ℓ W l h Y hKpos (hcap hc) hD ha']
    exact compactMainChunkR_runs legacy ds (R ∘ compactMnLayerReg) R _ _ rfl e
  · intro hc
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    exact compactMainDirectR_runs legacy ds hd hbody (by omega) hA9 hNW hgate H hh hW v hv P₀ Y hY R hlegacy

end
end IntegerMultBounds.MathlibTM2.Fast.Main
