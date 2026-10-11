module

public import IntegerMultBounds.Machine.CompactComplexRolePhaseSite
public import IntegerMultBounds.Machine.CompactComplexNativeCodecFrame

/-! A single physical basis pass on an original selected role. Unlike the
complete scalar phase lifecycle, this restores a canonical raw bank after
only the forward or reversed original basis word, so a recursive child can
execute between the two passes. The alphabet is the native prime alphabet. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexActualCallAlignment
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageParameters (Stage)
open ButterflyStreamData (Coefficient)
open ActivePrefixStageNativePolynomial (rows symbols)
open CompactNativeRoleSourcePorts (external callerTapes)
open CompactNativeRoleConjugatedPorts (encoding selected)
open Networks.Shared50ModularControl (prime)
open CompactAllAxisPhaseDispatch (count edge)
variable {sh : Shape} {t c : ℕ}

/-- Both passes use the original ambient basis word, in opposite orders. -/
def word (d : Inputs sh) (hs : d.stage.slots=25^3) (pc : Fin count) (reverse : Bool) :=
  if reverse then (CompactNativeConjugatedPhase.ops d hs pc).reverse
  else CompactNativeConjugatedPhase.ops d hs pc

def coefficients (d : Inputs sh) (hs : d.stage.slots=25^3) (pc : Fin count)
    (reverse : Bool) {ell : ℕ}
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient) :=
  ActivePrefixStageNativePolynomialWord.word d (word d hs pc reverse) xs

theorem coefficients_width (d : Inputs sh) (hs : d.stage.slots=25^3) (pc : Fin count)
    (reverse : Bool) {ell w : ℕ}
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (hw : ∀ i k,(xs i k).1.length=w ∧ (xs i k).2.length=w) :
    ∀ i k,(coefficients d hs pc reverse xs i k).1.length=w ∧
      (coefficients d hs pc reverse xs i k).2.length=w :=
  ActivePrefixStageNativePolynomialWord.word_width d _ xs hw

def nativePair {q : ℕ} (P : Program ActivePrefixStageNative.tapes q prime)
    (pc : Fin count) (reverse : Bool) : Σ r,Program CompactNativeConjugatedHeaderBank.tapes r prime :=
  if reverse then ⟨_,CompactNativeConjugatedPhase.framedReverse P pc⟩
  else ⟨_,CompactNativeConjugatedPhase.framedForward P pc⟩

def nativeProgram {q : ℕ} (P : Program ActivePrefixStageNative.tapes q prime)
    (pc : Fin count) (reverse : Bool) := (nativePair P pc reverse).2

def nativeCost (D : ℕ) (d : Inputs sh) (hs : d.stage.slots=25^3)
    (pc : Fin count) (reverse : Bool) (B : ℕ)
    (hp : ∀ op,1<d.stage.f → ActivePrefixStageRuntimeData.Packed (ActivePrefixStagePairData.changePair d op) D) :=
  CompactNativeConjugatedPhase.wordCost D d B hp (word d hs pc reverse)

private theorem native_runs {q : ℕ} (D : ℕ)
    (P : Program ActivePrefixStageNative.tapes q prime) (C : ℝ)
    (hP : CompactComplexPhaseFixedWord.Spec D P C)
    (d : Inputs sh) (hs : d.stage.slots=25^3) (pc : Fin count) (reverse : Bool)
    (ell w : ℕ) (hcode : sh.payload=symbols (2^ell) w*3+0)
    (hp : ∀ op,1<d.stage.f → ActivePrefixStageRuntimeData.Packed (ActivePrefixStagePairData.changePair d op) D)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (hw : ∀ i k,(xs i k).1.length=w ∧ (xs i k).2.length=w) :
    HoareTime (nativeProgram P pc reverse)
      (fun z => z=CompactNativeConjugatedPhase.bank d ell (rows d xs hw))
      (fun z => z=CompactNativeConjugatedPhase.bank d ell
        (rows d (coefficients d hs pc reverse xs) (coefficients_width d hs pc reverse xs hw)))
      (nativeCost D d hs pc reverse (symbols (2^ell) w) hp) ∧
    (nativeCost D d hs pc reverse (symbols (2^ell) w) hp : ℝ)≤
      ((Networks.ComplexPhaseRowSchedule.word (edge pc)).length : ℝ)*C*ActivePrefixStageInverseBudget.scale d := by
  obtain ⟨hf,hfr,hb,hbr⟩ := hP sh (symbols (2^ell) w) d hs hcode hp (edge pc)
    (rows d xs hw) (ActivePrefixStageNativePolynomial.rows_nonblank d xs hw)
  rw [ActivePrefixStageNativePolynomialWord.result_rows] at hfr hbr
  cases reverse
  · exact ⟨hoare_extend_eq (hoare_extend_eq hfr (AllAxisPhaseOriginalScalar.scalar ell))
      (FixedHeaderBankCopy.empty 67),hf⟩
  · exact ⟨hoare_extend_eq (hoare_extend_eq hbr (AllAxisPhaseOriginalScalar.scalar ell))
      (FixedHeaderBankCopy.empty 67),hb⟩

def sharedProgram {q : ℕ} (P : Program ActivePrefixStageNative.tapes q prime)
    (focus : Fin 14 → Fin t) (j : Fin t) (pc : Fin count) (reverse : Bool) :=
  seq (CompactNativeConjugatedHeaderBank.setup focus)
    (seq (Placement.placed (nativeProgram P pc reverse)
      (SharedPlacementAlphabet.sharedPlacement j CompactNativeConjugatedHeaderBank.source))
      (CompactNativeConjugatedHeaderBank.cleanup t))

private theorem shared_runs {q B time : ℕ} (P : Program ActivePrefixStageNative.tapes q prime)
    (focus : Fin 14 → Fin t) (j : Fin t) (pc : Fin count) (reverse : Bool)
    (v : Tapes t prime) (d : Inputs sh) (ell : ℕ)
    (xs ys : ActivePrefixStageNativeRows.Rows d B)
    (hf : ∀ i,v.tape (focus i)=RadixZeroFill.encodedBinary (AllAxisPhaseOriginalScalar.words d ell i))
    (hh : ∀ i,v.head (focus i)=1)
    (hs : v.tape j=(CompactNativeConjugatedPhase.bank d ell xs).tape CompactNativeConjugatedHeaderBank.source)
    (hp : v.head j=(CompactNativeConjugatedPhase.bank d ell xs).head CompactNativeConjugatedHeaderBank.source)
    (hnative : HoareTime (nativeProgram P pc reverse)
      (fun z => z=CompactNativeConjugatedPhase.bank d ell xs)
      (fun z => z=CompactNativeConjugatedPhase.bank d ell ys) time) :
    HoareTime (sharedProgram P focus j pc reverse)
      (fun z => z=v.append (FixedHeaderBankCopy.empty CompactNativeConjugatedHeaderBank.tapes))
      (fun z => z=(SharedPlacementAlphabet.setTape v j
        ((CompactNativeConjugatedPhase.bank d ell ys).tape CompactNativeConjugatedHeaderBank.source)
        ((CompactNativeConjugatedPhase.bank d ell ys).head CompactNativeConjugatedHeaderBank.source)).append
          (FixedHeaderBankCopy.empty CompactNativeConjugatedHeaderBank.tapes))
      (CompactNativeConjugatedSharedCaller.cost t d ell time) := by
  have hc := CompactNativeConjugatedHeaderBank.setup_runs focus v d ell hf hh
  have hn := SharedPlacementAlphabet.shared_hoare hnative v j CompactNativeConjugatedHeaderBank.source
    (fun _ => blank) 0 hs hp
  rw [CompactNativeConjugatedHeaderBank.bank_without_source,
    CompactNativeConjugatedHeaderBank.bank_without_source] at hn
  have he := CompactNativeConjugatedHeaderBank.cleanup_runs
    (SharedPlacementAlphabet.setTape v j
      ((CompactNativeConjugatedPhase.bank d ell ys).tape CompactNativeConjugatedHeaderBank.source)
      ((CompactNativeConjugatedPhase.bank d ell ys).head CompactNativeConjugatedHeaderBank.source)) d ell
  exact (hc.seq (hn.seq he)).consequence (fun _ hz => hz) (fun _ hz => hz)
    (by unfold CompactNativeConjugatedSharedCaller.cost; omega)

/-- On generated numeric43, original metadata and every unselected role are
retained; only the selected source is physically permuted, and copied metadata
is erased. No alignment or execution premise is supplied. -/
theorem exists_prepared_program (D : ℕ) :
    ∃ q, ∃ P : Program ActivePrefixStageNative.tapes q prime, ∃ C : ℝ,0<C ∧
    ∀ (t c : ℕ) (old : Tapes t 2) (ht : 43<t) (payload : Tapes (1+c) 2) (j : Fin c)
      (sh : Shape) (v : Stage sh) (rowsCount ell p : ℕ)
      (hG : 1≤sh.guard) (hGK : sh.guard+1≤sh.chunk) (hr : 0<rowsCount)
      (hslots : v.slots=25^3) (pc : Fin count) (reverse : Bool)
      (hp : ∀ op,1<v.f → ActivePrefixStageRuntimeData.Packed
        (ActivePrefixStagePairData.changePair (NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr) op) D)
      (xs : Fin (ActivePrefixStageTripleWords.count (NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr)) →
        Fin (2^ell) → Coefficient)
      (hw : ∀ i k,(xs i k).1.length=NativePolynomialStageShape.width sh p ∧
        (xs i k).2.length=NativePolynomialStageShape.width sh p)
      (hword : payload.tape ⟨j.val+1,by omega⟩=SymbolTripleClean.word
        (List.ofFn (ActivePrefixStageNativeRows.flat (rows (NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr) xs hw))))
      (hhead : payload.head ⟨j.val+1,by omega⟩=0),
      let d := NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr
      let st := NativePolynomialStageHeaders.prepared sh rowsCount ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val
      let before := Alphabet.mapTapes encoding (external old ht st payload)
      let out := SharedPlacementAlphabet.setTape payload (CompactNativeRoleConjugatedOutput.roleSlot j)
        (SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
          (rows d (coefficients d hslots pc reverse xs) (coefficients_width d hslots pc reverse xs hw))))) 0
      let time := CompactNativeConjugatedSharedCaller.cost (callerTapes t c) d ell
        (nativeCost D d hslots pc reverse (symbols (2^ell) (NativePolynomialStageShape.width sh p)) hp)
      HoareTime (sharedProgram P (CompactNativeRoleConjugatedPorts.focus t c) (selected t j) pc reverse)
        (fun z => z=before.append (FixedHeaderBankCopy.empty CompactNativeConjugatedHeaderBank.tapes))
        (fun z => z=(Alphabet.mapTapes encoding (external old ht st out)).append
          (FixedHeaderBankCopy.empty CompactNativeConjugatedHeaderBank.tapes)) time ∧
      (time : ℝ)≤C*ActivePrefixStageInverseBudget.scale d := by
  obtain ⟨q,P,C,hC,hP⟩ := CompactComplexPhaseFixedWord.exists_fixed_program D
  refine ⟨q,P,(CompactNativeConjugatedPhaseFamily.wordBudget : ℝ)*C+268,by positivity,?_⟩
  intro t c old ht payload j sh v rowsCount ell p hG hGK hr hslots pc reverse hp xs hw hword hhead
  let d := NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr
  have hbounds := CompactNativeRoleConjugatedBudget.polynomial_bounds sh ell p
  obtain ⟨hn,hb⟩ := native_runs D P C hP d hslots pc reverse ell (NativePolynomialStageShape.width sh p)
    (NativePolynomialStageShape.code sh ell p) hp xs hw
  constructor
  · have hs : (Alphabet.mapTapes encoding (external old ht
        (NativePolynomialStageHeaders.prepared sh rowsCount ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val) payload)).tape
        (selected t j)=(CompactNativeConjugatedPhase.bank d ell (rows d xs hw)).tape CompactNativeConjugatedHeaderBank.source := by
      rw [(CompactNativeRoleConjugatedPorts.selected_source old ht _ payload j).1,
        (CompactNativeConjugatedHeaderBank.bank_source d (rows d xs hw) ell).1,hword]
      rfl
    have hh : (Alphabet.mapTapes encoding (external old ht
        (NativePolynomialStageHeaders.prepared sh rowsCount ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val) payload)).head
        (selected t j)=(CompactNativeConjugatedPhase.bank d ell (rows d xs hw)).head CompactNativeConjugatedHeaderBank.source := by
      rw [(CompactNativeRoleConjugatedPorts.selected_source old ht _ payload j).2,
        (CompactNativeConjugatedHeaderBank.bank_source d (rows d xs hw) ell).2,hhead]
    have h := shared_runs P (CompactNativeRoleConjugatedPorts.focus t c) (selected t j) pc reverse _ d ell
      (rows d xs hw) _ (fun i => (CompactNativeRoleConjugatedPorts.prepared_headers old ht payload v rowsCount ell p hG hGK hr i).1)
      (fun i => (CompactNativeRoleConjugatedPorts.prepared_headers old ht payload v rowsCount ell p hG hGK hr i).2) hs hh hn
    rw [CompactNativeRoleConjugatedOutput.installed_word] at h
    exact h
  · have hlife := CompactNativeRoleConjugatedBudget.lifecycle_linear (callerTapes t c)
      (CompactNativeRoleConjugatedCaller.order v) d
      (CompactNativeRoleConjugatedCaller.expanded_ordered v ell p) ell hbounds.1
    have hvolume := CompactNativeConjugatedPhaseFamily.volume_le_scale d
    have hpay := (Nat.cast_le (α:=ℝ).mpr hlife).trans
      (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using
        mul_le_mul_of_nonneg_left hvolume (by norm_num : (0 : ℝ)≤266))
    have hwordBound := Nat.cast_le (α:=ℝ).mpr (CompactNativeConjugatedPhaseFamily.word_le pc)
    have hscale := ActivePrefixStageInverseBudget.one_le_scale d
    have hwpay := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hwordBound hC.le)
      (by linarith : 0≤ActivePrefixStageInverseBudget.scale d)
    unfold CompactNativeConjugatedSharedCaller.cost
    push_cast at hpay ⊢
    dsimp only [d] at hb hpay hscale hwpay
    nlinarith only [hb,hpay,hscale,hwpay]


/-- Each serialized coefficient follows the chronological original basis
permutation, in either direction, without changing its polynomial index. -/
theorem coefficients_destination (d : Inputs sh) (hs : d.stage.slots=25^3)
    (pc : Fin count) (reverse : Bool) {ell : ℕ}
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (r : Fin (ActivePrefixStageTripleWords.count d)) (j : Fin (2^ell)) :
    coefficients d hs pc reverse xs
      (ActivePrefixStageNativePairCoordinates.run d (word d hs pc reverse) r) j=xs r j :=
  ActivePrefixStageNativePolynomialWord.word_destination d _ xs r j

/-- Forward and reverse passes restore the literal coefficient arrays. -/
theorem coefficients_reverse_forward (d : Inputs sh) (hs : d.stage.slots=25^3)
    (pc : Fin count) {ell : ℕ}
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient) :
    coefficients d hs pc true (coefficients d hs pc false xs)=xs := by
  funext r j
  change ActivePrefixStageNativePolynomialWord.word d (CompactNativeConjugatedPhase.ops d hs pc).reverse
    (ActivePrefixStageNativePolynomialWord.word d (CompactNativeConjugatedPhase.ops d hs pc) xs) r j=xs r j
  rw [ActivePrefixStageNativePolynomialWord.word_reverse_entry,
    ActivePrefixStageNativePolynomialWord.word_destination]

/-- The forward native row endpoint is the same physical destination used
by the bilinear-control compiler. -/
theorem forward_address (d : Inputs sh) (hs : d.stage.slots=25^3) (pc : Fin count)
    (r : Fin (ActivePrefixStageTripleWords.count d)) :
    ActivePrefixStageNativePairCoordinates.start d
      (ActivePrefixStageNativePairCoordinates.run d (word d hs pc false) r)=
      CompactComplexPhasePhysical.destination d hs (edge pc)
        (ActivePrefixStageNativePairCoordinates.start d r) :=
  (ActivePrefixStageNativePairCoordinates.run_start d _ r).symm

/-- Actual occurrence PC selection preserves the exact original edge, so
its physical basis word uses the original chosen residual basis. -/
theorem call_word (d : Inputs sh) (hs : d.stage.slots=25^3)
    (call : Networks.ComplexRecursiveCallSchema.Call) :
    word d hs (CompactComplexRolePhaseSite.pc call.site) false=
      CompactComplexPhasePhysical.word d hs (Networks.ComplexRecursiveCallSchema.edge call.site) := by
  change CompactComplexPhasePhysical.word d hs (edge (CompactComplexRolePhaseSite.pc call.site))=_
  rw [CompactComplexRolePhaseSite.actual_edge]

def program {q : ℕ} (P : Program ActivePrefixStageNative.tapes q prime)
    (t c : ℕ) (j : Fin c) (pc : Fin count) (reverse : Bool) :=
  seq (extend (Alphabet.program encoding (CompactNativeRoleGuardedChildCaller.payloadProgram t c))
      CompactNativeConjugatedHeaderBank.tapes)
    (seq (sharedProgram P (CompactNativeRoleConjugatedPorts.focus t c) (selected t j) pc reverse)
      (extend (Alphabet.program encoding (CompactNativeRoleGuardedChildCaller.payloadRestore t c))
        CompactNativeConjugatedHeaderBank.tapes))

private theorem numeric {q : ℕ} (M : Program 43 q 2) (old : Tapes t 2) (ht : 43<t)
    (st su : ActiveRepairRankHeadersCommands.State) (payload : Tapes (1+c) 2) (time : ℕ)
    (h : HoareTime M (fun v => v=ActiveRepairRankHeadersCommands.bank st)
      (fun v => v=ActiveRepairRankHeadersCommands.bank su) time) :
    HoareTime (Placement.placed M (CompactNativeRoleChildHeadersPorts.placement t c))
      (fun v => v=external old ht st payload) (fun v => v=external old ht su payload) time := by
  have hh := Placement.hoare_at h (CompactNativeRoleChildHeadersPorts.placement t c)
    (external old ht st payload) (CompactNativeRoleChildHeadersPorts.active old ht st payload)
  apply hh.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  rw [Placement.replace,CompactNativeRoleChildHeadersPorts.extra old ht st su payload,
    ←CompactNativeRoleChildHeadersPorts.active old ht su payload,Placement.view]

private theorem lifted {n q time : ℕ} {M : Program n q 2} {v w : Tapes n 2}
    (h : HoareTime M (fun z => z=v) (fun z => z=w) time) :
    HoareTime (Alphabet.program encoding M) (fun z => z=Alphabet.mapTapes encoding v)
      (fun z => z=Alphabet.mapTapes encoding w) time := by
  apply (Alphabet.map_hoare encoding h).consequence _ _ le_rfl
  · rintro z rfl; exact ⟨_,rfl,rfl⟩
  · rintro z ⟨_,rfl,rfl⟩; rfl

/-- A physical forward or inverse basis pass starts and finishes with the
original raw numeric43 caller, without a prepared-bank or alignment premise.
Both joins, generated headers, copied controls and all cleanup are paid. -/
theorem exists_program (D : ℕ) :
    ∃ q, ∃ P : Program ActivePrefixStageNative.tapes q prime, ∃ C : ℝ,0<C ∧
    ∀ (t c : ℕ) (old : Tapes t 2) (ht : 43<t) (payload : Tapes (1+c) 2) (j : Fin c)
      (sh : Shape) (v : Stage sh) (rowsCount ell p : ℕ)
      (hG : 1≤sh.guard) (hGK : sh.guard+1≤sh.chunk) (hr : 0<rowsCount)
      (_hpay : sh.payload=1) (hslots : v.slots=25^3) (pc : Fin count) (reverse : Bool)
      (hp : ∀ op,1<v.f → ActivePrefixStageRuntimeData.Packed
        (ActivePrefixStagePairData.changePair (NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr) op) D)
      (xs : Fin (ActivePrefixStageTripleWords.count (NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr)) →
        Fin (2^ell) → Coefficient)
      (hw : ∀ i k,(xs i k).1.length=NativePolynomialStageShape.width sh p ∧
        (xs i k).2.length=NativePolynomialStageShape.width sh p)
      (hword : payload.tape ⟨j.val+1,by omega⟩=SymbolTripleClean.word
        (List.ofFn (ActivePrefixStageNativeRows.flat (rows (NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr) xs hw))))
      (hhead : payload.head ⟨j.val+1,by omega⟩=0),
      let d := NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr
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
        (CompactNativeRoleConjugatedLifecycle.cost v rowsCount ell p passTime) ∧
      (CompactNativeRoleConjugatedLifecycle.cost v rowsCount ell p passTime : ℝ)≤
        C*ActivePrefixStageInverseBudget.scale d := by
  obtain ⟨q,P,C,hC,hP⟩ := exists_prepared_program D
  refine ⟨q,P,C+NativePolynomialStageHeaderBudget.constant+2,by positivity,?_⟩
  intro t c old ht payload j sh v rowsCount ell p hG hGK hr hpay hslots pc reverse hp xs hw hword hhead
  let d := NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr
  let out := SharedPlacementAlphabet.setTape payload (CompactNativeRoleConjugatedOutput.roleSlot j)
    (SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
      (rows d (coefficients d hslots pc reverse xs) (coefficients_width d hslots pc reverse xs hw))))) 0
  have hA : 0<sh.axes := lt_of_lt_of_le v.positiveWidth v.widthFits
  have hK : 0<sh.chunk := lt_of_le_of_lt (Nat.zero_le _) v.selectedFits
  have hsetup := hoare_extend_eq (lifted (numeric _ old ht _ _ payload _
    (NativePolynomialStageHeaders.runs (a:=2) sh rowsCount ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val hG hA hK)))
    (FixedHeaderBankCopy.empty CompactNativeConjugatedHeaderBank.tapes)
  obtain ⟨hpass,hbound⟩ := hP t c old ht payload j sh v rowsCount ell p hG hGK hr hslots pc reverse hp xs hw hword hhead
  have hrestore := hoare_extend_eq (lifted (numeric _ old ht _ _ out _
    (NativePolynomialStageHeaders.restore_runs (a:=2) sh rowsCount ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val)))
    (FixedHeaderBankCopy.empty CompactNativeConjugatedHeaderBank.tapes)
  constructor
  · exact (hsetup.seq (hpass.seq hrestore)).consequence (fun _ hz => hz) (fun _ hz => hz)
      (by unfold CompactNativeRoleConjugatedLifecycle.cost CompactNativeRoleConjugatedLifecycle.preparedState; omega)
  · have hlife := NativePolynomialStageHeaderBudget.lifecycle_linear v rowsCount ell p hr hA hG hK hpay
    have hvol := NativePolynomialStageHeaderBudget.expanded_volume sh rowsCount ell p
    have hvolume := CompactNativeConjugatedPhaseFamily.volume_le_scale d
    have hsmall : (CompactNativeRoleTransferBudget.volume rowsCount sh ell p : ℝ)≤ActivePrefixStageInverseBudget.scale d := by
      have hn : CompactNativeRoleTransferBudget.volume rowsCount sh ell p≤
          rowsCount*(NativePolynomialStageShape.shape sh ell p).recordWidth := by omega
      exact (Nat.cast_le.mpr hn).trans hvolume
    have hlifeR := Nat.cast_le (α:=ℝ).mpr hlife
    push_cast at hlifeR
    have hpayR := mul_le_mul_of_nonneg_left hsmall
      (Nat.cast_nonneg NativePolynomialStageHeaderBudget.constant : (0 : ℝ)≤NativePolynomialStageHeaderBudget.constant)
    have hunit := ActivePrefixStageInverseBudget.one_le_scale d
    unfold CompactNativeRoleConjugatedLifecycle.cost CompactNativeRoleConjugatedLifecycle.preparedState
    push_cast
    dsimp only [d] at hbound hpayR hunit
    linarith only [hlifeR,hpayR,hbound,hunit]


private theorem payload_set {a L K : ℕ} (u : Tapes K a) (ports : Fin L → Fin K)
    (hi : Function.Injective ports) (j : Fin L) (f : ℤ → Fin (a+4)) (head : ℤ) :
    SharedBank.payload (SharedPlacementAlphabet.setTape u (ports j) f head) ports=
      SharedPlacementAlphabet.setTape (SharedBank.payload u ports) j f head := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp [SharedBank.payload,SharedPlacementAlphabet.setTape,Function.update_apply,hi.eq_iff]

private theorem strip_set {a L K : ℕ} (u : Tapes K a) (ports : Fin L → Fin K)
    (j : Fin L) (f : ℤ → Fin (a+4)) (head : ℤ) :
    SharedBank.strip (SharedPlacementAlphabet.setTape u (ports j) f head) ports=SharedBank.strip u ports := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals by_cases h : ∃ j,ports j=i
  all_goals simp only [h,ite_true,ite_false]
  all_goals have hn : i≠ports j := fun he => h ⟨j,he.symm⟩
  all_goals simp only [SharedPlacementAlphabet.setTape,Function.update_of_ne hn]

private theorem payload_append {a L R : ℕ} (u : Tapes L a) (w : Tapes R a) :
    SharedBank.payload (u.append w) (Fin.castAdd R)=u := by
  apply congrArg₂ Tapes.mk <;> funext i <;> simp only [Tapes.append,Fin.addCases_left]

private theorem strip_append {a L R : ℕ} (u : Tapes L a) :
    SharedBank.strip (u.append (SharedBank.empty R a)) (Fin.castAdd R)=SharedBank.empty (L+R) a := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases with
  | left i => simp
  | right i =>
    have hn : ¬∃ j : Fin L,Fin.castAdd R j=Fin.natAdd L i := by
      rintro ⟨j,h⟩;have hv := congrArg Fin.val h;have := j.isLt
      simp only [Fin.val_castAdd,Fin.val_natAdd] at hv;omega
    simp [hn,Tapes.append,SharedBank.empty]

/-- Place a one-role lifecycle at its actual permanent ports. Every permanent
spectator and every appended private tape is restored at the same paid cost. -/
private theorem placed_role {a L K R q B : ℕ}
    (M : Program (L+R) q a) (ports : Fin L → Fin K) (hi : Function.Injective ports)
    (v : Tapes K a) (small : Tapes L a) (hv : SharedBank.payload v ports=small)
    (j : Fin L) (f : ℤ → Fin (a+4))
    (h : HoareTime M (fun z => z=small.append (SharedBank.empty R a))
      (fun z => z=(SharedPlacementAlphabet.setTape small j f 0).append (SharedBank.empty R a)) B) :
    HoareTime (Placement.placed M (CleanSubbank.placement (Fin.castAdd R) ports hi))
      (fun z => z=CleanSubbank.bank v)
      (fun z => z=CleanSubbank.bank (SharedPlacementAlphabet.setTape v (ports j) f 0)) B := by
  apply CleanSubbank.realizes M (Fin.castAdd R) ports (Fin.castAdd_injective L R) hi
    v (SharedPlacementAlphabet.setTape v (ports j) f 0)
    (small.append (SharedBank.empty R a))
    ((SharedPlacementAlphabet.setTape small j f 0).append (SharedBank.empty R a)) B
  · rw [payload_append,hv]
  · rw [payload_append,payload_set v ports hi,hv]
  · exact strip_append _
  · exact strip_append _
  · exact (strip_set v ports j f 0).symm
  · exact h

/-- The native pass shares exactly original raw43 and original named role
ports in the permanent bank; all fixed private workspace is appended. -/
def permanentProgram {q : ℕ} (P : Program ActivePrefixStageNative.tapes q prime)
    (s c : ℕ) (j : Fin c) (pc : Fin count) (reverse : Bool) :=
  Placement.placed (program P 44 c j pc reverse)
    (CleanSubbank.placement (Fin.castAdd CompactNativeConjugatedHeaderBank.tapes)
      (CompactComplexNativeRoleBridge.slot (s:=s+43) (c:=c))
      CompactComplexNativeRoleBridge.slot_injective)

private theorem mapped_payload {a b L K : ℕ} (e : Alphabet.Encoding a b)
    (v : Tapes K a) (ports : Fin L → Fin K) :
    SharedBank.payload (Alphabet.mapTapes e v) ports=Alphabet.mapTapes e (SharedBank.payload v ports) := rfl

/-- The actual native65/raw43/named-role bank has the exact local caller
view required by the wrapper, with controller and recursion storage retained. -/
theorem permanent_view (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar raw : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes s 2) (payload : Tapes (1+c) 2) :
    SharedBank.payload (Alphabet.mapTapes encoding
      (CompactComplexNativeCodecFrame.bank control queue scalar raw tail storage payload))
      (CompactComplexNativeRoleBridge.slot (s:=s+43) (c:=c))=
      Alphabet.mapTapes encoding (external (CompactComplexNativeRoleBridge.old control payload)
        (by decide) raw payload) := by
  rw [mapped_payload]
  exact congrArg (Alphabet.mapTapes encoding)
    (CompactComplexNativeRoleBridge.payload_bank control queue raw tail
      (storage.append (ActiveRepairRankHeadersCommands.bank scalar)) payload)


/-- The literal permanent caller and selected role ports discharge the full
physical basis wrapper; exact controller/storage/spectator tapes are retained. -/
theorem exists_permanent_program (D : ℕ) :
    ∃ q, ∃ P : Program ActivePrefixStageNative.tapes q prime, ∃ C : ℝ,0<C ∧
    ∀ (s c : ℕ) (control : Tapes 43 2) (queue : Tapes 1 2)
      (scalar : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
      (storage : Tapes s 2) (payload : Tapes (1+c) 2) (j : Fin c)
      (sh : Shape) (v : Stage sh) (rowsCount ell p : ℕ)
      (hG : 1≤sh.guard) (hGK : sh.guard+1≤sh.chunk) (hr : 0<rowsCount)
      (hpay : sh.payload=1) (hslots : v.slots=25^3) (pc : Fin count) (reverse : Bool)
      (hp : ∀ op,1<v.f → ActivePrefixStageRuntimeData.Packed
        (ActivePrefixStagePairData.changePair (NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr) op) D)
      (xs : Fin (ActivePrefixStageTripleWords.count (NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr)) →
        Fin (2^ell) → Coefficient)
      (hw : ∀ i k,(xs i k).1.length=NativePolynomialStageShape.width sh p ∧
        (xs i k).2.length=NativePolynomialStageShape.width sh p)
      (hword : payload.tape ⟨j.val+1,by omega⟩=SymbolTripleClean.word
        (List.ofFn (ActivePrefixStageNativeRows.flat (rows (NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr) xs hw))))
      (hhead : payload.head ⟨j.val+1,by omega⟩=0),
      let d := NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr
      let raw := CompactNativeRoleConjugatedLifecycle.rawState v rowsCount ell p
      let before := CompactComplexNativeCodecFrame.bank control queue scalar raw tail storage payload
      let returned := SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
        (rows d (coefficients d hslots pc reverse xs) (coefficients_width d hslots pc reverse xs hw))))
      let passTime := CompactNativeConjugatedSharedCaller.cost (callerTapes 44 c) d ell
        (nativeCost D d hslots pc reverse (symbols (2^ell) (NativePolynomialStageShape.width sh p)) hp)
      HoareTime (permanentProgram P s c j pc reverse)
        (fun z => z=CleanSubbank.bank (Alphabet.mapTapes encoding before))
        (fun z => z=CleanSubbank.bank (Alphabet.mapTapes encoding
          (SharedPlacementAlphabet.setTape before
            (CompactComplexNativeRoleBridge.roleSlot (s:=s+43) j) returned 0)))
        (CompactNativeRoleConjugatedLifecycle.cost v rowsCount ell p passTime) ∧
      (CompactNativeRoleConjugatedLifecycle.cost v rowsCount ell p passTime : ℝ)≤
        C*ActivePrefixStageInverseBudget.scale d := by
  obtain ⟨q,P,C,hC,hP⟩ := exists_program D
  refine ⟨q,P,C,hC,?_⟩
  intro s c control queue scalar tail storage payload j sh v rowsCount ell p hG hGK hr hpay hslots pc reverse hp xs hw hword hhead
  obtain ⟨hrun,hbound⟩ := hP 44 c (CompactComplexNativeRoleBridge.old control payload) (by decide)
    payload j sh v rowsCount ell p hG hGK hr hpay hslots pc reverse hp xs hw hword hhead
  constructor
  · rw [CompactNativeRoleConjugatedOutput.external_set,AlphabetTapeReplacement.map_setTape] at hrun
    have h := placed_role (program P 44 c j pc reverse)
      (CompactComplexNativeRoleBridge.slot (s:=s+43) (c:=c))
      CompactComplexNativeRoleBridge.slot_injective _ _
      (permanent_view control queue scalar _ tail storage payload) (selected 44 j) _ hrun
    have he : CompactComplexNativeRoleBridge.slot (s:=s+43) (selected 44 j)=
        CompactComplexNativeRoleBridge.roleSlot (s:=s+43) j :=
      CompactComplexNativeRoleBridge.role_slot j
    rw [he,←AlphabetTapeReplacement.map_setTape] at h
    exact h
  · exact hbound

end
end IntegerMultBounds.Machine.CompactComplexActualCallAlignment
