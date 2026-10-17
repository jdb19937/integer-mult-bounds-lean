module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynHybridRoundR
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerContract
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformLayerContract
public import IntegerMultBounds.MathlibTM2.Fast.SynFwd
import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapRuntime
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! The rounded layer contract on records. `synDec p L Y` reads physical numerators `Y` back as
logical records; `compactSynLQ` is the rounded dispatch round on records: the rounded chunk
output read back on chunk rounds, `Q_p` of the butterflies on direct rounds. The contract
`CompactSynLayerContractR` says the rounded dispatch carries numerators of `u` to numerators of
`compactSynLQ h u`. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.MathlibTM2.Mult.SynthErr
open IntegerMultBounds.MathlibTM2.Cost IntegerMultBounds.NLogN
open CompactGadgetReservationCapacity
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Ka : ℕ}

/-! ### Numerators read back as records -/

section Dec

variable {r N : ℕ}

/-- The logical records whose numerators in the layout `L` are `Y`. -/
def synDec (p : ℕ) (L : Equiv.Perm (Fin N)) (Y : ℕ → Fin r → GaussianInt) : Recs r :=
  fun x c => if hx : x<2^N then GaussianInt.toComplex (Y (layRec L ⟨x,hx⟩) c)/2^p else 0

theorem synNum_dec (p : ℕ) (L : Equiv.Perm (Fin N)) (Y : ℕ → Fin r → GaussianInt) :
    SynNum p L (synDec p L Y) Y := by
  intro x hx c
  have e : (⟨synPi L x,synPi_lt L x⟩ : Fin (2^N))=(layRec L).symm ⟨x,hx⟩ :=
    Fin.ext (synPi_layRec L ⟨x,hx⟩)
  simp only [synDec,synPi_lt L x,dite_true,e,Equiv.apply_symm_apply]

theorem synMask_ynum {p : ℕ} {L : Equiv.Perm (Fin N)} {u : Recs r}
    {Y : ℕ → Fin r → GaussianInt} (h : SynNum p L u Y) :
    synMask (2^N) Y=synMask (2^N) (synYnum p L u) := by
  funext x c
  by_cases hx : x<2^N
  · simp only [synMask,hx,ite_true,synYnum]
    rw [←h x hx c,numer_grid]
  · simp only [synMask,hx,ite_false]

/-- The direct round: `Q_p` of the butterflies on the physical selected bits. -/
theorem synNum_trunc (es : List ℕ) (L : Equiv.Perm (Fin es.sum)) (p h : ℕ)
    {u : Recs r} {Y : ℕ → Fin r → GaussianInt} (hY : SynNum p L u Y) :
    SynNum p L (rdR p (bflyL (selBits es h) u))
      (synTrunc (bflyL ((selBits es h).map (twPosL L))
        (fun x c => GaussianInt.toComplex (Y x c)))) := by
  intro m hm c'
  have hP : ∀ q ∈ (selBits es h).map (twPosL L), q < es.sum := by
    intro q hq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hq
    exact twPosL_lt L k (selBits_lt es hk)
  have e1 : (fun x c => GaussianInt.toComplex (Y x c)) =
      fun x c => (2 : ℂ) ^ p * (GaussianInt.toComplex (Y x c) / 2 ^ p) := by
    funext x c; field_simp
  have heq : EqBelow es.sum (fun x c => GaussianInt.toComplex (Y x c) / 2 ^ p)
      (synPhys L u) := by
    intro x hx; funext c; exact hY x hx c
  have h2 := bflyL_eqBelow hP heq m hm
  rw [bflyL_phys L u _ (fun q hq => selBits_lt es hq)] at h2
  simp only [synTrunc]
  rw [e1, bflyL_smul]
  have h3 := synTr_toComplex p (bflyL ((selBits es h).map (twPosL L))
    (fun x c => GaussianInt.toComplex (Y x c) / 2 ^ p) m c')
  simpa [h2, synPhys, rdR] using h3

/-- The forward twiddle on numerators: `y^(-E_h)` on the logical records. -/
theorem synNum_twF (es : List ℕ) (L : Equiv.Perm (Fin es.sum)) {l : ℕ} (p h : ℕ)
    {w : Recs (2^l)} {Y : ℕ → Fin (2^l) → GaussianInt} (hY : SynNum p L w Y) :
    SynNum p L (mulYInv (twE es (2^l) h (parts es h)) w)
      (fun m => twShiftZ (twEx true es l h (twGat (twPosL L) es.sum m)) (Y m)) := by
  intro x hx c
  rw [twShiftZ_toComplex]
  have hrec : (fun c' => GaussianInt.toComplex (Y x c') / 2 ^ p) = w (synPi L x) := by
    funext c'; exact hY x hx c'
  rw [hrec]
  rfl

theorem isFixed_toComplex_div (p : ℕ) (z : GaussianInt) :
    IsFixed p (GaussianInt.toComplex z/2^p) := by
  have h := isFixed_rhoC p (GaussianInt.toComplex z/2^p)
  rwa [rhoC_eq_numer,numer_grid] at h

theorem gridR_synDec (p : ℕ) (L : Equiv.Perm (Fin N)) (Y : ℕ → Fin r → GaussianInt) :
    GridR p (synDec p L Y) := by
  intro x c
  unfold synDec
  split_ifs
  · exact isFixed_toComplex_div p _
  · exact ⟨0,0,by apply Complex.ext <;> simp⟩

end Dec

/-! ### The rounded layer contract -/

/-- The rounded dispatch round on logical records. -/
def compactSynLQ (ds : ComplexFramedExecution.Directions) (M K : ℕ) (es : List ℕ)
    (ℓ W l p h : ℕ) (u : Recs (2^l)) : Recs (2^l) :=
  if synChunk ℓ K h then
    synDec p (layPerm es ℓ K) (compactSynChunkR ds M K es ℓ W l h
      (synMask (2^es.sum) (synYnum p (layPerm es ℓ K) u)))
  else rdR p (bflyL (selBits es h) u)

theorem gridR_compactSynLQ (ds : ComplexFramedExecution.Directions) (M K : ℕ) (es : List ℕ)
    (ℓ W l p h : ℕ) (u : Recs (2^l)) : GridR p (compactSynLQ ds M K es ℓ W l p h u) := by
  unfold compactSynLQ
  split_ifs
  · exact gridR_synDec p _ _
  · exact gridR_rdR p _

/-- The rounded dispatch carries numerators of `u` to numerators of `compactSynLQ h u`. -/
def CompactSynLayerContractR (legacy : MnProc → MnPr (prime+Ka))
    (ds : ComplexFramedExecution.Directions) (M K : ℕ) (es : List ℕ) (ℓ W l p : ℕ) : Prop :=
  ∀ (h : ℕ),h+1≤ℓ → ∀ (v : SynW → List (Fin (prime+Ka+4))),
    SynV v es ℓ K W l h (layPerm es ℓ K) →
    ∀ (P₀ : List (Fin (prime+Ka+4))) (u : Recs (2^l)),SupLe es.sum u 1 →
    ∀ (Y : ℕ → Fin (2^l) → GaussianInt),SynNum p (layPerm es ℓ K) u Y →
    ∀ (R : Fin compactMnT → List (Fin (prime+Ka+4))),
    compactSynView R=synG (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Y)) P₀) v →
    CompactSynReady R M →
    ∃ Y',SynNum p (layPerm es ℓ K)
        (compactSynLQ ds M K es ℓ W l p h u) Y' ∧
      LayRuns (compactMainBodyR legacy ds) (compactSynDispatchR ds) R
        (Function.update R (compactMnRg (.src (.v .io)))
          (cstream (prime+Ka) W (rpStream (2^es.sum) Y')))
        (compactSynLayerCostR (Ka := Ka) ds M K es ℓ W l h (synStashCostW v synXS))

theorem compactSynLayerContractR_eventually (hA : 21≤prime+Ka)
    (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4) :
    ∀ᶠ M : ℕ in Filter.atTop,
    ∀ (ds : ComplexFramedExecution.Directions),ComplexPhaseBudget.Realizes ds →
      (∀ g,Instr.gate g∈program ds → (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4) →
    ∀ (legacy : MnProc → MnPr (prime+Ka)),
      (∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f)) →
    ∀ (es : List ℕ) (ℓ W l p : ℕ),CompactSynGeometry M es ℓ W l p →
      CompactSynFitsR ds M (Mult.Sizes.K M) es ℓ W l p →
      CompactSynLayerContractR legacy ds M (Mult.Sizes.K M) es ℓ W l p := by
  filter_upwards [compactSynDispatchR_eventually_exec_stream hA hA9 hNW] with M hexec
  intro ds hd hgate legacy hbody es ℓ W l p hg hfits h hh v hv P₀ u hu Y hY R hR hr
  let L := layPerm es ℓ (Mult.Sizes.K M)
  let Ym := synMask (2^es.sum) Y
  have hR' : compactSynView R=synG (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Ym)) P₀) v := by
    simp only [Ym,rpStream_synMask]; exact hR
  have he := hexec ds hd hgate legacy hbody es ℓ W l h p hg.depth hg.layout.K_pos hg.layout hh
    (fun _ => hg.reservation) hg.dimension hg.precision hg.multiplicity hg.width hg.numerator
    hfits v hv P₀ Ym (synMask_norm hY hu) R
    hR'
    (by simpa only [compactMnLayerReg_private] using hr.blank)
    (by simpa only [compactMnLayerReg_private] using hr.depth)
    (by simpa only [compactMnLayerReg_private] using hr.guard)
  refine ⟨_,?_,he⟩
  unfold compactSynLQ
  by_cases hc : synChunk ℓ (Mult.Sizes.K M) h
  · simp only [hc,ite_true]
    have hm : Ym=synMask (2^es.sum) (synYnum p L u) := synMask_ynum hY
    rw [hm]
    exact synNum_dec p L _
  · simp only [hc,ite_false]
    exact synNum_trunc es L p h (synNum_mask hY)


theorem compactSynUniformLayerContractR_eventually (hA : 21≤prime+Ka)
    (hA9 : 9^4≤prime+Ka+4) (hNW : NW≤prime+Ka+4) :
    ∀ᶠ M : ℕ in Filter.atTop,
    ∀ (ds : ComplexFramedExecution.Directions),ComplexPhaseBudget.Realizes ds →
      (∀ g,Instr.gate g∈program ds → (2*gateBound g+1)^(2*(gateWires g).length)≤prime+Ka+4) →
    ∀ (legacy : MnProc → MnPr (prime+Ka)),
      (∀ f,legacy (.lay f)=embProg mnLayE MnProc.lay (layerTable (Ka := Ka) (U := Unit) mnQ_layer ds f)) →
    ∀ (es : List ℕ) (K ℓ W l p : ℕ),CompactSynUniformGeometry M K es ℓ W l p →
      CompactSynFitsR ds M K es ℓ W l p →
      CompactSynLayerContractR legacy ds M K es ℓ W l p := by
  filter_upwards [compactSynDispatchR_uniform_eventually_exec_stream hA hA9 hNW] with M hexec
  intro ds hd hgate legacy hbody es K ℓ W l p hg hfits h hh v hv P₀ u hu Y hY R hR hr
  let L := layPerm es ℓ K
  let Ym := synMask (2^es.sum) Y
  have hR' : compactSynView R=synG (synIdle (cstream (prime+Ka) W (rpStream (2^es.sum) Ym)) P₀) v := by
    simp only [Ym,rpStream_synMask]; exact hR
  have he := hexec ds hd hgate legacy hbody es K ℓ W l h p hg.chunkLower hg.chunkUpper hg.depth hg.layout.K_pos hg.layout hh
    (fun _ => hg.reservation) hg.dimension hg.precision hg.multiplicity hg.width hg.numerator
    hfits v hv P₀ Ym (synMask_norm hY hu) R
    hR'
    (by simpa only [compactMnLayerReg_private] using hr.blank)
    (by simpa only [compactMnLayerReg_private] using hr.depth)
    (by simpa only [compactMnLayerReg_private] using hr.guard)
  refine ⟨_,?_,he⟩
  unfold compactSynLQ
  by_cases hc : synChunk ℓ K h
  · simp only [hc,ite_true]
    have hm : Ym=synMask (2^es.sum) (synYnum p L u) := synMask_ynum hY
    rw [hm]
    exact synNum_dec p L _
  · simp only [hc,ite_false]
    exact synNum_trunc es L p h (synNum_mask hY)

end
end IntegerMultBounds.MathlibTM2.Fast.Main
