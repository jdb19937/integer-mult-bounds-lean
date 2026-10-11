module

public import IntegerMultBounds.Machine.CompactComplexActualCallAlignment
public import IntegerMultBounds.Machine.CompactNativeRoleChildLifecycleBudget

/-! Selected role arrays have the genuine parent-row quotient. Each physical
basis pass temporarily computes that quotient in numeric43, executes the
selected-count codec lifecycle, and restores the original parent row count. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexActualCallRoleAlignment
noncomputable section
open CompactComplexActualCallAlignment (coefficients coefficients_width nativeCost)
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open ButterflyStreamData (Coefficient)
open ActivePrefixStageNativePolynomial (rows symbols)
open CompactNativeRoleSourcePorts (external callerTapes)
open CompactNativeRoleConjugatedPorts (encoding)
open Networks.Shared50ModularControl (prime)
open CompactAllAxisPhaseDispatch (count)
variable {t c : ℕ} {sh : Shape}

def program {q : ℕ} (P : Program ActivePrefixStageNative.tapes q prime)
    (t c : ℕ) (j : Fin c) (pc : Fin count) (reverse : Bool) :=
  seq (extend (Alphabet.program encoding
      (CompactNativeRoleChildHeadersPorts.program (CompactNativeRoleChildBank.prepare c) t c))
      CompactNativeConjugatedHeaderBank.tapes)
    (seq (CompactComplexActualCallAlignment.program P t c j pc reverse)
      (extend (Alphabet.program encoding
        (CompactNativeRoleChildHeadersPorts.program (CompactNativeRoleChildBank.restore c) t c))
        CompactNativeConjugatedHeaderBank.tapes))

def rowCost (c : ℕ) (v : Stage sh) (rowsCount ell p : ℕ) :=
  CompactChildHeadersArithmetic.scheduleCost (CompactNativeRoleChildBank.prepare c)
      (CompactNativeRoleConjugatedLifecycle.rawState v rowsCount ell p)+
  CompactChildHeadersArithmetic.scheduleCost (CompactNativeRoleChildBank.restore c)
      (CompactNativeRoleConjugatedLifecycle.rawState v (rowsCount/c) ell p)

def cost (c : ℕ) (v : Stage sh) (rowsCount ell p passTime : ℕ) :=
  CompactChildHeadersArithmetic.scheduleCost (CompactNativeRoleChildBank.prepare c)
      (CompactNativeRoleConjugatedLifecycle.rawState v rowsCount ell p)+
    CompactNativeRoleConjugatedLifecycle.cost v (rowsCount/c) ell p passTime+
  CompactChildHeadersArithmetic.scheduleCost (CompactNativeRoleChildBank.restore c)
      (CompactNativeRoleConjugatedLifecycle.rawState v (rowsCount/c) ell p)+2

private theorem lifted {n q time : ℕ} {M : Program n q 2} {v w : Tapes n 2}
    (h : HoareTime M (fun z => z=v) (fun z => z=w) time) :
    HoareTime (Alphabet.program encoding M) (fun z => z=Alphabet.mapTapes encoding v)
      (fun z => z=Alphabet.mapTapes encoding w) time := by
  apply (Alphabet.map_hoare encoding h).consequence _ _ le_rfl
  · rintro z rfl; exact ⟨_,rfl,rfl⟩
  · rintro z ⟨_,rfl,rfl⟩;rfl

private theorem native_volume {sh : Shape} (v : Stage sh) (rowsCount c ell p : ℕ)
    (hG : 1≤sh.guard) (hGK : sh.guard+1≤sh.chunk) (hg : 0<rowsCount/c) (hd : c∣rowsCount) :
    (CompactNativeRoleTransferBudget.volume rowsCount sh ell p : ℝ)≤
      (c : ℝ)*ActivePrefixStageInverseBudget.scale
        (NativePolynomialStageShape.inputs v (rowsCount/c) ell p hG hGK hg) := by
  let d := NativePolynomialStageShape.inputs v (rowsCount/c) ell p hG hGK hg
  have hv := NativePolynomialStageHeaderBudget.expanded_volume sh (rowsCount/c) ell p
  have hvolume := CompactNativeConjugatedPhaseFamily.volume_le_scale d
  have hs : (CompactNativeRoleTransferBudget.volume (rowsCount/c) sh ell p : ℝ)≤ActivePrefixStageInverseBudget.scale d := by
    have hn : CompactNativeRoleTransferBudget.volume (rowsCount/c) sh ell p≤
        (rowsCount/c)*(NativePolynomialStageShape.shape sh ell p).recordWidth := by omega
    exact (Nat.cast_le.mpr hn).trans hvolume
  have he : CompactNativeRoleTransferBudget.volume rowsCount sh ell p=
      c*CompactNativeRoleTransferBudget.volume (rowsCount/c) sh ell p := by
    unfold CompactNativeRoleTransferBudget.volume
    rw [←Nat.mul_assoc,Nat.mul_div_cancel' hd]
  rw [he,Nat.cast_mul]
  exact mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg c)

/-- One fixed real basis machine covers both directions on every genuine
selected quotient, with total raw parent metadata restored before child entry. -/
theorem exists_program (D c : ℕ) (hc : 0<c) :
    ∃ q, ∃ P : Program ActivePrefixStageNative.tapes q prime, ∃ C : ℝ,0<C ∧
    ∀ (t : ℕ) (old : Tapes t 2) (ht : 43<t) (payload : Tapes (1+c) 2) (j : Fin c)
      (sh : Shape) (v : Stage sh) (rowsCount ell p : ℕ)
      (hG : 1≤sh.guard) (hGK : sh.guard+1≤sh.chunk) (hr : 0<rowsCount) (hgroup : 0<rowsCount/c) (hd : c∣rowsCount)
      (_hpay : sh.payload=1) (hslots : v.slots=25^3) (pc : Fin count) (reverse : Bool)
      (hp : ∀ op,1<v.f → ActivePrefixStageRuntimeData.Packed
        (ActivePrefixStagePairData.changePair (NativePolynomialStageShape.inputs v (rowsCount/c) ell p hG hGK hgroup) op) D)
      (xs : Fin (ActivePrefixStageTripleWords.count (NativePolynomialStageShape.inputs v (rowsCount/c) ell p hG hGK hgroup)) →
        Fin (2^ell) → Coefficient)
      (hw : ∀ i k,(xs i k).1.length=NativePolynomialStageShape.width sh p ∧
        (xs i k).2.length=NativePolynomialStageShape.width sh p)
      (hword : payload.tape ⟨j.val+1,by omega⟩=SymbolTripleClean.word
        (List.ofFn (ActivePrefixStageNativeRows.flat (rows (NativePolynomialStageShape.inputs v (rowsCount/c) ell p hG hGK hgroup) xs hw))))
      (hhead : payload.head ⟨j.val+1,by omega⟩=0),
      let d := NativePolynomialStageShape.inputs v (rowsCount/c) ell p hG hGK hgroup
      let raw := CompactNativeRoleConjugatedLifecycle.rawState v rowsCount ell p
      let before := Alphabet.mapTapes encoding (external old ht raw payload)
      let out := SharedPlacementAlphabet.setTape payload (CompactNativeRoleConjugatedOutput.roleSlot j)
        (SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
          (rows d (coefficients d hslots pc reverse xs) (coefficients_width d hslots pc reverse xs hw))))) 0
      let passTime := CompactNativeConjugatedSharedCaller.cost (callerTapes t c) d ell
        (nativeCost D d hslots pc reverse (symbols (2^ell) (NativePolynomialStageShape.width sh p)) hp)
      HoareTime (program P t c j pc reverse)
        (fun z => z=before.append (FixedHeaderBankCopy.empty CompactNativeConjugatedHeaderBank.tapes))
        (fun z => z=(Alphabet.mapTapes encoding (external old ht raw out)).append
          (FixedHeaderBankCopy.empty CompactNativeConjugatedHeaderBank.tapes))
        (cost c v rowsCount ell p passTime) ∧
      (cost c v rowsCount ell p passTime : ℝ)≤
        C*ActivePrefixStageInverseBudget.scale d := by
  obtain ⟨q,P,C,hC,hP⟩ := CompactComplexActualCallAlignment.exists_program D
  refine ⟨q,P,C+(12000*(c+1) : ℝ)*c+2,by positivity,?_⟩
  intro t old ht payload j sh v rowsCount ell p hG hGK hr hgroup hd hpay hslots pc reverse hp xs hw hword hhead
  let d := NativePolynomialStageShape.inputs v (rowsCount/c) ell p hG hGK hgroup
  let out := SharedPlacementAlphabet.setTape payload (CompactNativeRoleConjugatedOutput.roleSlot j)
    (SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
      (rows d (coefficients d hslots pc reverse xs) (coefficients_width d hslots pc reverse xs hw))))) 0
  have hpre := hoare_extend_eq (lifted (CompactNativeRoleChildHeadersPorts.prepare_runs old ht sh
    rowsCount ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val payload hc))
    (FixedHeaderBankCopy.empty CompactNativeConjugatedHeaderBank.tapes)
  obtain ⟨hpass,hbound⟩ := hP t c old ht payload j sh v (rowsCount/c) ell p hG hGK hgroup hpay hslots pc reverse hp xs hw hword hhead
  have hpost := hoare_extend_eq (lifted (CompactNativeRoleChildHeadersPorts.restore_runs old ht sh
    rowsCount ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val out hd hc hr))
    (FixedHeaderBankCopy.empty CompactNativeConjugatedHeaderBank.tapes)
  constructor
  · exact (hpre.seq (hpass.seq hpost)).consequence (fun _ hz => hz) (fun _ hz => hz)
      (by unfold cost CompactNativeRoleConjugatedLifecycle.rawState;omega)
  · have hrows := CompactNativeRoleChildLifecycleBudget.row_cost c sh rowsCount ell p
      v.rho v.left v.f v.slots v.right v.source.val v.target.val hr hd
    have hrowsR := Nat.cast_le (α:=ℝ).mpr hrows
    have hvol := native_volume v rowsCount c ell p hG hGK hgroup hd
    have hpay := mul_le_mul_of_nonneg_left hvol (by positivity : (0 : ℝ)≤(12000*(c+1) : ℕ))
    have hunit := ActivePrefixStageInverseBudget.one_le_scale d
    unfold cost CompactNativeRoleConjugatedLifecycle.rawState
    push_cast at hrowsR hpay ⊢
    dsimp only [d] at hbound hunit
    nlinarith only [hrowsR,hpay,hbound,hunit]

end
end IntegerMultBounds.Machine.CompactComplexActualCallRoleAlignment
