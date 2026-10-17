module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepPrepR
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepRuntime
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepCompose
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepStream
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopRuntimeExecutionR

/-! The rounded chunk round: the rounded preparation, parking, the rounded top program
`compactTopProgR` on the placed rounded layer table, unparking and cleanup. The parked runtime
execution of the rounded top (`compactSynParkedRuntimeR_eventually_exec`) and the assembly. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.Rounds
open CompactGadgetReservationCapacity
open CompactGadgetReservationShape (Shape)
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Q Ka : ℕ} {U : Type}
open Filter

section Unpark
variable {Q A : ℕ} {U P : Type}

/-- Remove the `13` fields of the rounded configuration from `park`. -/
def compactSynDropCfgCoreR : Pr P (nT SXReg) Q A U :=
  .seq (topSkips (lreg .park) (sreg (.s 30)) (sreg (.s 31)) 13) (uclear (sreg (.s 30)))

theorem sg_compactSynDropCfgR (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (cfg : List ℕ) (P₀ : List (Fin (A+4))) (hlen : cfg.length=13)
    (hpark : R (lreg .park)=topRec cfg++P₀) (h30 : v (.s 30)=[]) :
    LayRuns body compactSynDropCfgCoreR (synG R v)
      (synG (Function.update R (lreg .park) P₀) v)
      ((2*(topRec cfg : List (Fin (A+4))).length+14)+(2*(topRec cfg : List (Fin (A+4))).length+2)) := by
  have ht : cfg.take 13=cfg := List.take_of_length_le hlen.le
  have hd : cfg.drop 13=[] := List.drop_eq_nil_iff.mpr hlen.le
  have e₁ := so_topSkips body (R := R) (v := v) (o := lreg .park) (b := .s 30) (c := .s 31)
    (lreg_out (by simp)) (by decide) 13 cfg P₀ hlen.ge hpark
  simp only [ht,hd,topRec_nil,List.nil_append,h30,List.append_nil] at e₁
  have e₂ := sg_uclear body (R := Function.update R (lreg .park) P₀)
    (v := Function.update v (.s 30) (topRec cfg).reverse) (a := .s 30)
  refine lr_weaken body (e₁.seq e₂) ?_ ?_
  · rw [Function.update_idem,←h30,Function.update_eq_self]
  · simp

def compactSynDropCfgR : Pr P (nT CompactHostBReg) Q A U :=
  embProg compactLegacyReg (fun f : Empty => f.elim) (compactSynDropCfgCoreR (P := Empty))

theorem compactSynDropCfgR_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (cfg : List ℕ) (P₀ : List (Fin (A+4))) (hlen : cfg.length=13)
    (hpark : R (lreg .park)=topRec cfg++P₀) (h30 : v (.s 30)=[]) :
    CompactPlacedRuns body compactSynDropCfgR (synG R v)
      (synG (Function.update R (lreg .park) P₀) v)
      ((2*(topRec cfg : List (Fin (A+4))).length+14)+(2*(topRec cfg : List (Fin (A+4))).length+2)) := by
  intro vbig S hL hR
  exact compactEmptySetup_exec compactLegacyReg compactLegacyReg_injective body
    (sg_compactSynDropCfgR (fun f : Empty => f.elim) R v cfg P₀ hlen hpark h30) vbig S hL hR

def compactSynLayerUnparkR : Pr P (nT CompactHostBReg) Q A U :=
  .seq compactSynDropCfgR (.seq compactSynUnstash compactSynRestDown)

theorem compactSynLayerUnparkR_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K W l h : ℕ) (L : Equiv.Perm (Fin es.sum))
    (hv : SynV v es ℓ K W l h L) (ρ working : ℕ) (pfs cfg : List ℕ)
    (hlen : cfg.length=13) (io P₀ : List (Fin (A+4))) :
    LayRuns body compactSynLayerUnparkR
      (compactSynParkedFile R io (synStkW v blank synXS ++ blank :: P₀) es.sum (2^l) working K ρ cfg pfs)
      (embExt compactLegacyReg (synG (synIdle io P₀) v)
        (compactSynParkedFile R io (synStkW v blank synXS ++ blank :: P₀) es.sum (2^l) working K ρ cfg pfs))
      (((2*(topRec cfg : List (Fin (A+4))).length+14)+(2*(topRec cfg : List (Fin (A+4))).length+2))+
        ((synStashCostW v synXS+1)+synRestDownCost es.sum (2^l) working K ρ (topRec pfs : List (Fin (A+4))).length)) := by
  let park := synStkW v blank synXS ++ blank :: P₀
  let RF := synRestFile (synIdle io P₀) es.sum (2^l) working K ρ (topRec pfs)
  have hup (X : List (Fin (A+4))) : Function.update RF (lreg .park) X=
      synRestFile (synIdle io X) es.sum (2^l) working K ρ (topRec pfs) := by
    dsimp only [RF]
    rw [synRestFile_update (by simp),synIdle_update_park]
  have hclr : synClrW v synXS=(fun _ => []) := by
    funext x
    by_cases hx : x∈synXS
    · simp [synClrW,hx]
    · by_cases hcf : x=.p .cf
      · subst x; simp [synClrW,synXS,hv.hcf]
      · have hh := compactSynParkedW_empty v es ℓ K W l h L hv [] x
        simpa [synClrW,hx,Function.update_of_ne,hcf] using hh
  have e₁ := compactSynDropCfgR_runs body
    (synRestFile (synIdle io (topRec cfg ++ park)) es.sum (2^l) working K ρ (topRec pfs))
    (fun _ => []) cfg park hlen (by simp [synRestFile,synIdle,lreg]) rfl
  have e₂ := compactSynUnstash_runs body RF v P₀ hv.hblank
  have e₃ := compactSynRestDown_runs body (synIdle io P₀) v es.sum (2^l) working K ρ (topRec pfs)
    (synIdle_rest io P₀)
  rw [hclr,hup,hup] at e₂
  have hreset : Function.update
      (synRestFile (synIdle io (topRec cfg ++ park)) es.sum (2^l) working K ρ (topRec pfs))
      (lreg .park) park=synRestFile (synIdle io park) es.sum (2^l) working K ρ (topRec pfs) := by
    rw [synRestFile_update (by simp),synIdle_update_park]
  rw [hreset] at e₁
  exact (e₁.seq (e₂.seq e₃)).layRuns _ (embExt_comp_e compactLegacyReg_injective _ _)

end Unpark

/-- The complete rounded round. -/
def compactSynLayerStepR (ds : ComplexFramedExecution.Directions) :
    Pr LProc (nT CompactHostBReg) Q (prime+Ka) U :=
  .seq (compactSynLayerPrepareR (gateCount (program ds)) (cGain ds))
    (.seq compactSynRestUp
      (.seq compactSynStash
        (.seq compactSynPushCfg
          (.seq (compactTopProgR (.call .layer))
            (.seq compactSynDropCfgR
              (.seq compactSynUnstash
                (.seq compactSynRestDown compactBasisRefreshCleanup)))))))

/-- Assembly of the rounded round from its stages. -/
theorem compactSynLayerStepR_compose (body : LProc → Pr LProc (nT CompactHostBReg) Q (prime+Ka) U)
    (ds : ComplexFramedExecution.Directions)
    (R₀ R₁ R₂ R₃ R₄ R₅ : Fin (nT CompactHostBReg) → List (Fin (prime+Ka+4)))
    (c₁ c₂ c₃ c₄ c₅ : ℕ)
    (hp : LayRuns body (compactSynLayerPrepareR (gateCount (program ds)) (cGain ds)) R₀ R₁ c₁)
    (hk : LayRuns body compactSynLayerPark R₁ R₂ c₂)
    (ht : LayRuns body (compactTopProgR (.call .layer)) R₂ R₃ c₃)
    (hu : LayRuns body compactSynLayerUnparkR R₃ R₄ c₄)
    (hc : LayRuns body compactBasisRefreshCleanup R₄ R₅ c₅) :
    LayRuns body (compactSynLayerStepR ds) R₀ R₅ (c₁+(c₂+(c₃+(c₄+c₅)))) := by
  intro v S hL hR
  obtain ⟨v₁,n₁,hu₁,hc₁,e₁⟩ := hp v S hL hR
  obtain ⟨v₂,n₂,hu₂,hc₂,e₂⟩ := hk v₁ {S with R:=R₁} hL rfl
  obtain ⟨v₃,n₃,hu₃,hc₃,e₃⟩ := ht v₂ {S with R:=R₂} hL rfl
  obtain ⟨v₄,n₄,hu₄,hc₄,e₄⟩ := hu v₃ {S with R:=R₃} hL rfl
  obtain ⟨v₅,n₅,hu₅,hc₅,e₅⟩ := hc v₄ {S with R:=R₄} hL rfl
  let total := n₁+(n₂+(n₃+(n₄+n₅)))
  cases e₂ with
  | seq e₂a e₂bc =>
    cases e₂bc with
    | seq e₂b e₂c =>
      cases e₄ with
      | seq e₄a e₄bc =>
        cases e₄bc with
        | seq e₄b e₄c =>
          refine ⟨v₅,total,hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),?_,?_⟩
          · dsimp only [total]; omega
          · simpa only [total,Nat.add_assoc,compactSynLayerStepR] using Exec.seq e₁ (Exec.seq e₂a
              (Exec.seq e₂b (Exec.seq e₂c (Exec.seq e₃ (Exec.seq e₄a (Exec.seq e₄b
                (Exec.seq e₄c e₅)))))))

theorem compactSynParkedRuntimeR_eventually_exec (hQ : compactRuntimeStates ≤ Q)
    (hA : 21≤prime+Ka) (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4) :
    ∀ᶠ N : ℕ in atTop,
    ∀ (ds : ComplexFramedExecution.Directions)
      (_hgate : ∀ g, Instr.gate g∈program ds →
        (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4)
      (D o a R rBits r W p ρ gb s' k w : ℕ)
      (h : CompactReservationFits (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
        (Mult.Sizes.K N) D) (hD : D≤Mult.Sizes.d N)
      (hρ : ρ<Mult.Sizes.K N) (hR : 1≤R) (_hr : 1≤r) (_hW : p+2≤W)
      (_hRbits : R≤2^rBits)
      (ha : CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d N)*Mult.Sizes.K N≤a)
      (_hprecision : rBits+(o+Mult.Sizes.K N*(D-CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d N))+a)+1≤Mult.Sizes.p N)
      (_hrun : Mult.Sizes.r N≤r) (_hwrun : Mult.Sizes.p N≤W),
    let d := Mult.Sizes.d N
    let g := CompactReservationGrowth.guard N
    let K := Mult.Sizes.K N
    let n := o+K*(D-CompactGlobalRowPadding.rowAxes NW m d)
    let q := compactTopKernelCount d g K
    let aT := compactTopKernelOffset d g K D o
    let R₂ := compactTopRows d R a
    let s := (D+1)/2+q+(gb+(backChunks d g K+
      synE (gateCount (program ds)) 0
        (compactReservationActive d g K D) (compactReservationActive d g K D)))
    let shape := compactReservationShape d g K D (2^o*(3*(r*w)))
    let pcs := compactTopPcs d g K D o R₂
    let hfitT := (compactTopKernel_geometry (o := o) h hρ ha).1
    let hpcs := compactTop_working_pcs_ok ds (by omega) hR h hD ha (w := W)
    let hpcsR : ∀ pc∈pcs, pc.OkR K n R₂ := fun pc hpc => (hpcs pc hpc).okR
    let Ps := topPiecesR hρ pcs hpcsR
    let low := (topPieces hρ pcs hpcs).flatMap Piece.bitsList
    ∀ (_hww : W+s+D≤w) (_hs' : s'≤s)
      (_hscale : ∀ pc∈pcs, ∀ i<pc.j, scaleR pc.u ds i<w)
      (Rsrc : Fin (nT CompactHostBReg) → List (Fin (prime+Ka+4)))
      (_hblank : ∀ z : CompactBReg,z≠.work 13 → z≠.work 14 →
        Rsrc (reg (BReg := CompactHostBReg) (.bc (.inl z)))=[])
      (_hdepth : (Rsrc (reg (BReg := CompactHostBReg) (.bc (.inl (.work 13))))).length=d)
      (_hguard : (Rsrc (reg (BReg := CompactHostBReg) (.bc (.inl (.work 14))))).length=g)
      (park : List (Fin (prime+Ka+4)))
      (Z : ZArr (Fin R × Fin r) (n+a))
      (_hZ : ∀ z, ‖GaussianInt.toComplex (Z z)‖≤2^p)
      (_hX : ∀ z, TopFitsZ w (topPreRW ds w a low (topTop aT ρ K q (n+a) hfitT)
        (compactTopRows_bounds (by omega) hR ha).1 Ps gb Z z))
      (v : HS (nT CompactHostBReg) Q (prime+Ka) U)
      (S : Stacks (nT CompactHostBReg) (prime+Ka))
      (_hL : ∀ y,S.L y=[])
      (_hfile : S.R=compactSynParkedFile
        (compactSynSourceClearOut (compactSetupUpdate7 Rsrc compactBasisRefreshDst
          (compactZeroTail (compactBasisSetupValues d g K D o r))))
        (encZ (prime+Ka) W Z) park (n+a) r w K ρ
        (topCfgR W s a R R₂ q aT K o D gb s' k) (topPcRec K pcs)),
    ∃ (v' : HS (nT CompactHostBReg) Q (prime+Ka) U) (c : ℕ), v'.user=v.user ∧
      c≤compactTopCostR W w s n a R r K ρ q aT o D R₂ gb s' k pcs
        (compactTopCallCostR ds shape 1 (n+a) o r w ρ ⟨0,q,R,aT⟩)
        (compactTopCallCostR ds shape 1 n o r w ρ) ∧
      Exec (compactPlacedLayerTableR hQ ds) (compactTopProgR (.call .layer)) (mk v S) c
        (mk v' {S with R := Function.update S.R (reg (BReg := CompactHostBReg) .io) (encZ
                (prime+Ka) W (topRSW ds w a low (topTop aT ρ K q (n+a) hfitT)
                  (compactTopRows_bounds (by omega) hR ha).1 Ps gb s (k*2^s') Z))}) := by
  filter_upwards [compactTopRuntimeR_eventually_exec (Q := Q) (Ka := Ka) (U := U) hQ hA hA9 hNW] with N hrunTop
  intro ds hgate D o a R rBits r W p ρ gb s' k w h hD hρ hR hr hW hRbits ha hprecision hrun hwrun
  dsimp only
  intro hww hs' hscale Rsrc hblank hdepth hguard park Z hZ hX v S hL hfile
  have hK : 0<Mult.Sizes.K N := by omega
  let working := w
  let shape := compactReservationShape (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
    (Mult.Sizes.K N) D (2^o*(3*(r*working)))
  have hb := compactBasisRefresh_actual_rest (shape := shape) Rsrc (Mult.Sizes.d N)
    (CompactReservationGrowth.guard N) (Mult.Sizes.K N) D o r hblank hdepth hguard
    (compactReservation_back _ _ _ _ _ hK) rfl (compactReservation_bits hK h) rfl rfl
  have hbclear (z : CompactBReg) : compactBasisRest shape o r z
      (compactSynSourceClearOut (compactSetupUpdate7 Rsrc compactBasisRefreshDst
        (compactZeroTail (compactBasisSetupValues (Mult.Sizes.d N) (CompactReservationGrowth.guard N)
          (Mult.Sizes.K N) D o r)))
        (reg (BReg := CompactHostBReg) (.bc (.inl z)))) := by
    rw [compactSynSourceClear_compact]
    exact hb (.inl z)
  apply hrunTop ds hgate D o a R rBits r W p ρ gb s' k w h hD hρ hR hr hW hRbits ha hprecision
    hrun hwrun hww hs' hscale Z hZ hX v S hL
  · rw [hfile]
    exact compactSynParkedFile_topRegs _ _ _ _ _ _ _ _ _ _ shape o hbclear
  · rw [hfile]
    exact compactSynParkedFile_topIn _ _ _ _ _ _ _ _ _ _
  · rw [hfile]
    unfold compactSynParkedFile
    have he : compactLegacyReg (lreg .io)=reg (BReg := CompactHostBReg) .io := by
      simp [lreg,compactLegacyReg,compactMapRegName]
    rw [←he,embExt_apply compactLegacyReg_injective,synG_of_ne (lreg_out (by simp))]
    simp [synRestFile,synIdle,lreg]

theorem compactSynLayerStepR_eventually_exec (hQ : compactRuntimeStates≤Q)
    (hA : 21≤prime+Ka) (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4) :
    ∀ᶠ M : ℕ in atTop,
    ∀ (ds : ComplexFramedExecution.Directions)
      (hgate : ∀ g,Instr.gate g∈program ds → (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4)
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
    ∀ (_hdpos : 0<d) (hKpos : 1≤K) (_hchunk : synChunk ℓ K h)
      (hcap : CompactReservationFits d g K D) (hD : D≤d)
      (_haddr : o+K*D≤es.sum)
      (ha : CompactGlobalRowPadding.rowAxes NW m d*K≤a)
      (_hprecision : es.sum+1≤Mult.Sizes.p M)
      (_hrun : Mult.Sizes.r M≤r) (_hwrun : Mult.Sizes.p M≤W) (_hW : p+2≤W),
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
    let hρ : ρ<K := Nat.mod_lt _ (by omega)
    let hfitT := (compactTopKernel_geometry (o := o) hcap hρ ha).1
    let hpcs := compactTop_working_pcs_ok ds (oS := o) (R := 1) hKpos (by omega : 1≤1) hcap hD ha (w := W)
    let hpcsR : ∀ pc∈pcs, pc.OkR K n R₂ := fun pc hpc => (hpcs pc hpc).okR
    let Ps := topPiecesR hρ pcs hpcsR
    let low := (topPieces hρ pcs hpcs).flatMap Piece.bitsList
    let hR₂ := (compactTopRows_bounds (by omega : 0<K) (by omega : 0<1) ha).1
    ∀ (_hscale : ∀ pc∈pcs, ∀ i<pc.j, scaleR pc.u ds i<working)
      (v : SynW → List (Fin (prime+Ka+4))) (L : Equiv.Perm (Fin es.sum))
      (_hv : SynV v es ℓ K W l h L) (P₀ : List (Fin (prime+Ka+4)))
      (Z : ZArr (Fin 1 × Fin r) (n+a))
      (_hZ : ∀ z,‖GaussianInt.toComplex (Z z)‖≤2^p)
      (_hX : ∀ z, TopFitsZ working (topPreRW ds working a low (topTop aT ρ K q (n+a) hfitT)
        hR₂ Ps gb Z z))
      (R : Fin (nT CompactHostBReg) → List (Fin (prime+Ka+4)))
      (_hlegacy : R ∘ compactLegacyReg=synG (synIdle (encZ (prime+Ka) W Z) P₀) v)
      (_hblank : ∀ z : CompactBReg,z≠.work 13 → z≠.work 14 →
        R (reg (BReg := CompactHostBReg) (.bc (.inl z)))=[])
      (_hdepth : (R (reg (BReg := CompactHostBReg) (.bc (.inl (.work 13))))).length=d)
      (_hguard : (R (reg (BReg := CompactHostBReg) (.bc (.inl (.work 14))))).length=g),
    LayRuns (compactPlacedLayerTableR (Ka := Ka) (U := U) hQ ds) (compactSynLayerStepR ds) R
      (Function.update R (reg (BReg := CompactHostBReg) .io) (encZ (prime+Ka) W
        (topRSW ds working a low (topTop aT ρ K q (n+a) hfitT) hR₂ Ps gb s (1*2^s') Z)))
      (compactSynLayerRoundOverheadR (gateCount (program ds)) (cGain ds)
        es.sum d g K D o W r h (layB ℓ K) l ρ working
        (topRec pfs : List (Fin (prime+Ka+4))).length (topRec cfg : List (Fin (prime+Ka+4))).length
        (synStashCostW v synXS)+
        compactTopCostR W working s n a 1 r K ρ q aT o D R₂ gb s' 1 pcs
          (compactTopCallCostR ds shape 1 (n+a) o r working ρ ⟨0,q,1,aT⟩)
          (compactTopCallCostR ds shape 1 n o r working ρ)) := by
  filter_upwards [compactSynParkedRuntimeR_eventually_exec (Q := Q) (Ka := Ka) (U := U) hQ hA hA9 hNW] with M htopRuntime
  intro ds hgate es ℓ W l h p
  dsimp only
  intro hdpos hKpos hchunk hcap hD haddr ha hprecision hrun hwrun hW hscale v L hv P₀ Z hZ hX R hlegacy hblank hdepth hguard
  let d := Mult.Sizes.d M
  let g := CompactReservationGrowth.guard M
  let K := Mult.Sizes.K M
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
  have hρ : ρ<K := Nat.mod_lt _ (by omega)
  have hn : n≤es.sum := by
    have hm := Nat.mul_le_mul_left K (Nat.sub_le D (CompactGlobalRowPadding.rowAxes NW m d))
    exact (Nat.add_le_add_left hm o).trans haddr
  have htotal : n+a=es.sum := Nat.add_sub_of_le hn
  let hfitT := (compactTopKernel_geometry (o := o) hcap hρ ha).1
  let hpcs := compactTop_working_pcs_ok ds (oS := o) (R := 1) hKpos (by omega : 1≤1) hcap hD ha (w := W)
  let hpcsR : ∀ pc∈pcs, pc.OkR K n R₂ := fun pc hpc => (hpcs pc hpc).okR
  let Ps := topPiecesR hρ pcs hpcsR
  let low := (topPieces hρ pcs hpcs).flatMap Piece.bitsList
  let hR₂ := (compactTopRows_bounds (by omega : 0<K) (by omega : 0<1) ha).1
  let io := encZ (prime+Ka) W Z
  let io' := encZ (prime+Ka) W
    (topRSW ds working a low (topTop aT ρ K q (n+a) hfitT) hR₂ Ps gb s (1*2^s') Z)
  let Ro := synIdle io P₀
  let body := compactPlacedLayerTableR (Ka := Ka) (U := U) hQ ds
  let G := gateCount (program ds)
  let cG := cGain ds
  let Rsrc := compactSynLayerRecordsOutR R Ro v es ℓ K W l h G cG d g
  let Rready := compactSynSourceClearOut (compactSynLayerRefreshOutR R Ro v es ℓ K W l h G cG d g)
  let park := synStkW v blank synXS ++ blank :: P₀
  let Rpark := compactSynParkedFile Rready io park es.sum r working K ρ cfg pfs
  let Rdone := compactSynParkedFile Rready io' park es.sum r working K ρ cfg pfs
  let restored := synG (synIdle io' P₀) v
  let Rrest := embExt compactLegacyReg restored Rdone
  let values := compactBasisSetupValues d g K D o r
  let prepCost := compactSynLayerPrepareRCost G cG es.sum d g K D o W r h (layB ℓ K) l
  let parkCost := compactSynLayerParkCost es.sum r working K ρ
    (topRec pfs : List (Fin (prime+Ka+4))).length (topRec cfg : List (Fin (prime+Ka+4))).length (synStashCostW v synXS)
  let topCost := compactTopCostR W working s n a 1 r K ρ q aT o D R₂ gb s' 1 pcs
    (compactTopCallCostR ds shape 1 (n+a) o r working ρ ⟨0,q,1,aT⟩)
    (compactTopCallCostR ds shape 1 n o r working ρ)
  let unparkCost := compactSynLayerUnparkCostR es.sum r working K ρ
    (topRec pfs : List (Fin (prime+Ka+4))).length (topRec cfg : List (Fin (prime+Ka+4))).length (synStashCostW v synXS)
  let cleanCost := compactClear7Cost (compactZeroTail values)
  have hblankDst (i : Fin 7) : R (compactBasisRefreshDst i)=[] := by
    apply hblank (.work (compactBasisRefreshWork i)) <;> fin_cases i <;> decide
  have ep : LayRuns body (compactSynLayerPrepareR G cG) R Rready prepCost :=
    compactSynLayerPrepareR_runs body R Ro v es ℓ K W l h L G cG d g hv hKpos hdpos hlegacy hdepth hguard hblankDst
  have hview : Rready ∘ compactLegacyReg=synG Ro
      (compactSynPreparedW v K ρ working (topRec pfs) (topRec cfg).reverse) := by
    have he := compactSynLayerPrepareR_projection R Ro v es ℓ K W l h L hv G cG d g
    simpa only [Rready,working,s,s',gb,E,q,aT,cfg,pfs,pcs,compactTopPcs,compactRebasePc_record,
      compactTopKernelCount,compactTopKernelOffset,compactReservationActive,d,g,K,D,o,ρ,r,n,a,G,cG,R₂] using he
  have ek : LayRuns body compactSynLayerPark Rready Rpark parkCost :=
    compactSynLayerPark_runs body Rready v es ℓ K W l h L hv ρ working (topRec pfs) cfg io P₀ hview
  have hoff (z : CompactBReg) : Rsrc (reg (BReg := CompactHostBReg) (.bc (.inl z)))=
      R (reg (BReg := CompactHostBReg) (.bc (.inl z))) :=
    compactSynLayerRecordsOutR_compact R Ro v es ℓ K W l h G cG d g z
  have hprec : 0+(o+K*(D-CompactGlobalRowPadding.rowAxes NW m d)+a)+1≤Mult.Sizes.p M := by
    rw [Nat.zero_add]
    change n+a+1≤Mult.Sizes.p M
    rw [htotal]
    exact hprecision
  have et : LayRuns body (compactTopProgR (.call .layer)) Rpark Rdone topCost := by
    intro vb S hL hR
    obtain ⟨vb',c,hu,hc,he⟩ := htopRuntime ds hgate D o a 1 0 r W p ρ gb s' 1 working hcap hD hρ
      (by omega) (by change 1≤2^l; exact Nat.one_le_two_pow) hW (by simp) ha hprec
      hrun hwrun (by simp only [working, s, E, gb, q, d, g, K, D]; omega)
      (by simp only [s', E, gb, d, g, K, D]; omega) hscale Rsrc
      (by intro z h13 h14; rw [hoff]; exact hblank z h13 h14)
      (by rw [hoff]; exact hdepth) (by rw [hoff]; exact hguard) park Z hZ hX vb S hL
      (by rw [hR]; change Rpark=compactSynParkedFile Rready io park (n+a) r working K ρ cfg pfs; rw [htotal])
    rw [hR] at he
    have hi : Function.update Rpark (reg (BReg := CompactHostBReg) .io) io'=Rdone :=
      compactSynParkedFile_io_update Rready io io' park es.sum r working K ρ cfg pfs
    rw [hi] at he
    exact ⟨vb',c,hu,hc,he⟩
  have eu : LayRuns body compactSynLayerUnparkR Rdone Rrest unparkCost :=
    compactSynLayerUnparkR_runs body Rready v es ℓ K W l h L hv ρ working pfs cfg
      (by simp [cfg,topCfgR,topCfg]) io' P₀
  have erest : Rrest=embExt compactLegacyReg restored
      (compactSetupUpdate7 R compactBasisRefreshDst (compactZeroTail values)) := by
    unfold Rrest Rdone compactSynParkedFile
    rw [compactEmbExt_overwrite]
    -- The preparation changes only its explicit refresh counters outside the legacy image.
    dsimp only [Rready]
    rw [compactSynLayer_final_backgroundR]
    exact (compactSynLayerCleanup_commute restored R (compactZeroTail values)).symm
  have ec : LayRuns body compactBasisRefreshCleanup Rrest
      (Function.update R (reg (BReg := CompactHostBReg) .io) io') cleanCost := by
    rw [erest]
    have he := compactSynLayerCleanup_runs body restored R values hblankDst
    rw [compactSynRestored_io_update R io io' P₀ v hlegacy] at he
    exact he
  have eall := compactSynLayerStepR_compose body ds R Rready Rpark Rdone Rrest
    (Function.update R (reg (BReg := CompactHostBReg) .io) io') prepCost parkCost topCost unparkCost cleanCost ep ek et eu ec
  apply eall.mono
  change prepCost+(parkCost+(topCost+(unparkCost+cleanCost)))≤
    (prepCost+(parkCost+(unparkCost+cleanCost)))+topCost
  omega

theorem compactSynLayerStepR_eventually_exec_stream (hQ : compactRuntimeStates≤Q)
    (hA : 21≤prime+Ka) (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4) :
    ∀ᶠ M : ℕ in atTop,
    ∀ (ds : ComplexFramedExecution.Directions)
      (hgate : ∀ g,Instr.gate g∈program ds → (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4)
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
    ∀ (_hdpos : 0<d) (hKpos : 1≤K) (_hchunk : synChunk ℓ K h) (_H : LayHyp es ℓ K)
      (hcap : CompactReservationFits d g K D) (hD : D≤d)
      (_haddr : o+K*D≤es.sum)
      (ha : CompactGlobalRowPadding.rowAxes NW m d*K≤a)
      (_hprecision : es.sum+1≤Mult.Sizes.p M)
      (_hrun : Mult.Sizes.r M≤r) (_hwrun : Mult.Sizes.p M≤W) (_hW : p+2≤W),
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
    let hρ : ρ<K := Nat.mod_lt _ (by omega)
    let hfitT := (compactTopKernel_geometry (o := o) hcap hρ ha).1
    let hpcs := compactTop_working_pcs_ok ds (oS := o) (R := 1) hKpos (by omega : 1≤1) hcap hD ha (w := W)
    let hpcsR : ∀ pc∈pcs, pc.OkR K n R₂ := fun pc hpc => (hpcs pc hpc).okR
    let Ps := topPiecesR hρ pcs hpcsR
    let low := (topPieces hρ pcs hpcs).flatMap Piece.bitsList
    let hR₂ := (compactTopRows_bounds (by omega : 0<K) (by omega : 0<1) ha).1
    ∀ (_hscale : ∀ pc∈pcs, ∀ i<pc.j, scaleR pc.u ds i<working)
      (v : SynW → List (Fin (prime+Ka+4))) (L : Equiv.Perm (Fin es.sum))
      (_hv : SynV v es ℓ K W l h L) (P₀ : List (Fin (prime+Ka+4)))
      (Y : ℕ → Fin r → GaussianInt)
      (_hY : ∀ x c,‖GaussianInt.toComplex (Y x c)‖≤2^p)
      (_hX : ∀ z, TopFitsZ working (topPreRW ds working a low (topTop aT ρ K q (n+a) hfitT)
        hR₂ Ps gb (synZ (n+a) Y) z))
      (R : Fin (nT CompactHostBReg) → List (Fin (prime+Ka+4)))
      (_hlegacy : R ∘ compactLegacyReg=synG (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Y)) P₀) v)
      (_hblank : ∀ z : CompactBReg,z≠.work 13 → z≠.work 14 →
        R (reg (BReg := CompactHostBReg) (.bc (.inl z)))=[])
      (_hdepth : (R (reg (BReg := CompactHostBReg) (.bc (.inl (.work 13))))).length=d)
      (_hguard : (R (reg (BReg := CompactHostBReg) (.bc (.inl (.work 14))))).length=g),
    LayRuns (compactPlacedLayerTableR (Ka := Ka) (U := U) hQ ds) (compactSynLayerStepR ds) R
      (Function.update R (reg (BReg := CompactHostBReg) .io) (cstream (prime+Ka) W
        (rpStream (2^es.sum) (synRd (topRSW ds working a low (topTop aT ρ K q (n+a) hfitT) hR₂ Ps
          gb s (1*2^s') (synZ (n+a) Y))))))
      (compactSynLayerRoundOverheadR (gateCount (program ds)) (cGain ds)
        es.sum d g K D o W r h (layB ℓ K) l ρ working
        (topRec pfs : List (Fin (prime+Ka+4))).length (topRec cfg : List (Fin (prime+Ka+4))).length
        (synStashCostW v synXS)+
        compactTopCostR W working s n a 1 r K ρ q aT o D R₂ gb s' 1 pcs
          (compactTopCallCostR ds shape 1 (n+a) o r working ρ ⟨0,q,1,aT⟩)
          (compactTopCallCostR ds shape 1 n o r working ρ)) := by
  filter_upwards [compactSynLayerStepR_eventually_exec (Q := Q) (Ka := Ka) (U := U) hQ hA hA9 hNW] with M hexec
  intro ds hgate es ℓ W l h p
  dsimp only
  intro hdpos hKpos hchunk H hcap hD haddr ha hprecision hrun hwrun hW hscale v L hv P₀ Y hY hX R hlegacy hblank hdepth hguard
  have hn : Mult.Sizes.K M*((h-layB ℓ (Mult.Sizes.K M))/Mult.Sizes.K M*es.length)+
      Mult.Sizes.K M*(es.length-CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d M))≤es.sum := by
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) _).trans haddr
  have hna := Nat.add_sub_of_le hn
  let n := Mult.Sizes.K M*((h-layB ℓ (Mult.Sizes.K M))/Mult.Sizes.K M*es.length)+
      Mult.Sizes.K M*(es.length-CompactGlobalRowPadding.rowAxes NW m (Mult.Sizes.d M))
  have hinput : R ∘ compactLegacyReg=synG (synIdle
      (encZ (prime+Ka) W (synZ (n+(es.sum-n)) Y)) P₀) v := by
    rw [encZ_synZ,hna]
    exact hlegacy
  have he := hexec ds hgate es ℓ W l h p hdpos hKpos hchunk hcap hD haddr ha
    hprecision hrun hwrun hW hscale v L hv P₀ (synZ _ Y) (fun z => hY _ _) hX R
    hinput hblank hdepth hguard
  have hpow : (2:ℕ)^(n+(es.sum-n))=2^es.sum := by rw [hna]
  rw [encZ_eq_synRd, hpow] at he
  exact he

end
end IntegerMultBounds.MathlibTM2.Fast
