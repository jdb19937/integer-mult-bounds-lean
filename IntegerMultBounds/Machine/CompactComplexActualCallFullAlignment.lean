import IntegerMultBounds.Machine.CompactComplexActualCallAlignment
import IntegerMultBounds.Machine.CompactComplexSourceReadyActualTable

/-! Physical basis passes on the complete original source-ready scalar bank.
Every original tape keeps its position; the fixed local basis workspace is
appended. Actual child entry and decoded return run between the two passes. -/
namespace IntegerMultBounds.Machine.CompactComplexActualCallFullAlignment
noncomputable section
open CompactComplexActualCallAlignment
open CompactNativeRoleConjugatedPorts (encoding selected)
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open ButterflyStreamData (Coefficient)
open ActivePrefixStageNativePolynomial (rows symbols)
open CompactNativeRoleSourcePorts (external callerTapes)
open Networks.Shared50ModularControl (prime)
open CompactAllAxisPhaseDispatch (count)
variable {s c : ℕ}

abbrev localTapes (c : ℕ) := callerTapes 44 c+CompactNativeConjugatedHeaderBank.tapes
abbrev tapes (s c : ℕ) := CompactComplexSourceReadyScalarWorkspace.tapes s c+localTapes c

def prefixSlot (i : Fin (CompactComplexNativeCodecFrame.permanentTapes (10+s) c)) :
    Fin (CompactComplexSourceReadyScalarWorkspace.tapes s c) :=
  Fin.castAdd CompactComplexSourceReadyScalarWorkspace.scratch
    (Fin.castAdd 10 (Fin.castAdd CompactComplexSourceReadyWorkspace.leafTapes
      ((CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm (Fin.castAdd 9 i))))

theorem prefix_injective : Function.Injective (prefixSlot (s:=s) (c:=c)) := by
  intro i j h
  apply (Fin.castAdd_injective _ _) at h
  apply (Fin.castAdd_injective _ _) at h
  apply (Fin.castAdd_injective _ _) at h
  apply (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm.injective at h
  exact Fin.castAdd_injective _ _ h

def common (i : Fin (callerTapes 44 c)) :=
  prefixSlot (s:=s) (c:=c) (CompactComplexNativeRoleBridge.slot (s:=10+s+43) i)

theorem common_injective : Function.Injective (common (s:=s) (c:=c)) :=
  prefix_injective.comp CompactComplexNativeRoleBridge.slot_injective

def bank (permanent : Tapes (CompactComplexNativeCodecFrame.permanentTapes (10+s) c) 2)
    (frame : Tapes 9 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (work : Tapes 10 2) (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2) :=
  (CompactComplexSourceReadyWorkspace.bank
    (CompactComplexNonleafSpectatorTargetRestore.entry permanent frame) leaf work).append scratch

theorem prefix_bank (permanent : Tapes (CompactComplexNativeCodecFrame.permanentTapes (10+s) c) 2)
    (frame : Tapes 9 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (work : Tapes 10 2) (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2) :
    SharedBank.payload (bank permanent frame leaf work scratch) prefixSlot=permanent := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [bank,prefixSlot,CompactComplexSourceReadyWorkspace.bank,
    CompactComplexNonleafSpectatorTargetRestore.entry,Tapes.reindex,Tapes.append,Fin.addCases_left,
    Equiv.symm_symm,Equiv.apply_symm_apply]

private theorem mapped_chain {a b L K T : ℕ} (e : Alphabet.Encoding a b)
    (u : Tapes T a) (ps : Fin K → Fin T) (qs : Fin L → Fin K) (x : Tapes K a)
    (h : SharedBank.payload u ps=x) :
    SharedBank.payload (Alphabet.mapTapes e u) (ps ∘ qs)=
      SharedBank.payload (Alphabet.mapTapes e x) qs := by
  have he : SharedBank.payload (Alphabet.mapTapes e u) (ps ∘ qs)=
      SharedBank.payload (Alphabet.mapTapes e (SharedBank.payload u ps)) qs := rfl
  rw [he,h]

theorem caller_view (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar raw : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (payload : Tapes (1+c) 2)
    (frame : Tapes 9 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (work : Tapes 10 2) (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2) :
    SharedBank.payload (Alphabet.mapTapes encoding
      (bank (CompactComplexNativeCodecFrame.bank control queue scalar raw tail storage payload)
        frame leaf work scratch)) common=
      Alphabet.mapTapes encoding (external (CompactComplexNativeRoleBridge.old control payload)
        (by decide) raw payload) := by
  have hp := prefix_bank
    (CompactComplexNativeCodecFrame.bank control queue scalar raw tail storage payload) frame leaf work scratch
  have h := mapped_chain encoding _ prefixSlot
    (CompactComplexNativeRoleBridge.slot (s:=10+s+43) (c:=c)) _ hp
  exact h.trans (permanent_view control queue scalar raw tail storage payload)

def program {q : ℕ} (P : Program ActivePrefixStageNative.tapes q prime)
    (s c : ℕ) (j : Fin c) (pc : Fin count) (reverse : Bool) :=
  Placement.placed (CompactComplexActualCallAlignment.program P 44 c j pc reverse)
    (CleanSubbank.placement (Fin.castAdd CompactNativeConjugatedHeaderBank.tapes)
      (common (s:=s) (c:=c)) common_injective)

private theorem payload_set {a L K : ℕ} (u : Tapes K a) (ports : Fin L → Fin K)
    (hi : Function.Injective ports) (j : Fin L) (f : ℤ → Fin (a+4)) :
    SharedBank.payload (SharedPlacementAlphabet.setTape u (ports j) f 0) ports=
      SharedPlacementAlphabet.setTape (SharedBank.payload u ports) j f 0 := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp [SharedBank.payload,SharedPlacementAlphabet.setTape,Function.update_apply,hi.eq_iff]

private theorem strip_set {a L K : ℕ} (u : Tapes K a) (ports : Fin L → Fin K)
    (j : Fin L) (f : ℤ → Fin (a+4)) :
    SharedBank.strip (SharedPlacementAlphabet.setTape u (ports j) f 0) ports=SharedBank.strip u ports := by
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

/-- Actual full-bank wrapper with exact cleanup and paid runtime. -/
theorem exists_program (D : ℕ) :
    ∃ q, ∃ P : Program ActivePrefixStageNative.tapes q prime, ∃ C : ℝ,0<C ∧
    ∀ (s c : ℕ) (control : Tapes 43 2) (queue : Tapes 1 2)
      (scalar : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
      (storage : Tapes (10+s) 2) (payload : Tapes (1+c) 2) (j : Fin c)
      (frame : Tapes 9 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
      (work : Tapes 10 2) (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
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
      let before := bank (CompactComplexNativeCodecFrame.bank control queue scalar raw tail storage payload)
        frame leaf work scratch
      let returned := SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
        (rows d (coefficients d hslots pc reverse xs) (coefficients_width d hslots pc reverse xs hw))))
      let passTime := CompactNativeConjugatedSharedCaller.cost (callerTapes 44 c) d ell
        (nativeCost D d hslots pc reverse (symbols (2^ell) (NativePolynomialStageShape.width sh p)) hp)
      HoareTime (program P s c j pc reverse)
        (fun z => z=CleanSubbank.bank (Alphabet.mapTapes encoding before))
        (fun z => z=CleanSubbank.bank (Alphabet.mapTapes encoding
          (SharedPlacementAlphabet.setTape before
            (prefixSlot (s:=s) (c:=c) (CompactComplexNativeRoleBridge.roleSlot (s:=10+s+43) j)) returned 0)))
        (CompactNativeRoleConjugatedLifecycle.cost v rowsCount ell p passTime) ∧
      (CompactNativeRoleConjugatedLifecycle.cost v rowsCount ell p passTime : ℝ)≤
        C*ActivePrefixStageInverseBudget.scale d := by
  obtain ⟨q,P,C,hC,hP⟩ := CompactComplexActualCallAlignment.exists_program D
  refine ⟨q,P,C,hC,?_⟩
  intro s c control queue scalar tail storage payload j frame leaf work scratch sh v rowsCount ell p hG hGK hr hpay hslots pc reverse hp xs hw hword hhead
  obtain ⟨hrun,hbound⟩ := hP 44 c (CompactComplexNativeRoleBridge.old control payload) (by decide)
    payload j sh v rowsCount ell p hG hGK hr hpay hslots pc reverse hp xs hw hword hhead
  constructor
  · rw [CompactNativeRoleConjugatedOutput.external_set,AlphabetTapeReplacement.map_setTape] at hrun
    have hv := caller_view control queue scalar
      (CompactNativeRoleConjugatedLifecycle.rawState v rowsCount ell p) tail storage payload frame leaf work scratch
    have h := CleanSubbank.realizes (CompactComplexActualCallAlignment.program P 44 c j pc reverse)
      (Fin.castAdd CompactNativeConjugatedHeaderBank.tapes) (common (s:=s) (c:=c))
      (Fin.castAdd_injective _ _) common_injective
      (Alphabet.mapTapes encoding (bank
        (CompactComplexNativeCodecFrame.bank control queue scalar
          (CompactNativeRoleConjugatedLifecycle.rawState v rowsCount ell p) tail storage payload)
        frame leaf work scratch))
      (SharedPlacementAlphabet.setTape (Alphabet.mapTapes encoding (bank
        (CompactComplexNativeCodecFrame.bank control queue scalar
          (CompactNativeRoleConjugatedLifecycle.rawState v rowsCount ell p) tail storage payload)
        frame leaf work scratch)) (common (selected 44 j)) _ 0) _ _ _
      (by rw [payload_append,hv])
      (by rw [payload_append,payload_set _ _ common_injective,hv])
      (strip_append _) (strip_append _) (strip_set _ _ _ _).symm hrun
    have he : common (s:=s) (c:=c) (selected 44 j)=prefixSlot
        (CompactComplexNativeRoleBridge.roleSlot (s:=10+s+43) j) :=
      congrArg prefixSlot (CompactComplexNativeRoleBridge.role_slot j)
    rw [he,←AlphabetTapeReplacement.map_setTape] at h
    exact h
  · exact hbound

/-- Fixed concrete recursive call blocks retain every original tape index. -/
def child {q : ℕ} (P : Program ActivePrefixStageNative.tapes q prime)
    (headerStack pcStack liveStack : Fin s) (call : Networks.ComplexRecursiveCallSchema.Call) :
    Σ r,Program (tapes s CompactComplexSourceReadyScalarWorkspace.roles) r prime :=
  ⟨_,seq (program P s CompactComplexSourceReadyScalarWorkspace.roles
      (CompactComplexRolePhaseSite.role call.site) (CompactComplexRolePhaseSite.pc call.site) false)
    (extend (Alphabet.program encoding (CompactComplexSourceReadyActualTable.child headerStack pcStack liveStack call).2)
      (localTapes CompactComplexSourceReadyScalarWorkspace.roles))⟩

/-- The reverse original word executes after the complete real parent return,
when restored parent geometry again supplies its canonical raw caller. -/
def childReturn {q : ℕ} (P : Program ActivePrefixStageNative.tapes q prime)
    (headerStack liveStack : Fin s) (call : Networks.ComplexRecursiveCallSchema.Call) :
    Σ r,Program (tapes s CompactComplexSourceReadyScalarWorkspace.roles) r prime :=
  ⟨_,seq (extend (Alphabet.program encoding
      (CompactComplexSourceReadyActualTable.childReturn headerStack liveStack call).2)
      (localTapes CompactComplexSourceReadyScalarWorkspace.roles))
    (program P s CompactComplexSourceReadyScalarWorkspace.roles
      (CompactComplexRolePhaseSite.role call.site) (CompactComplexRolePhaseSite.pc call.site) true)⟩

end
end IntegerMultBounds.Machine.CompactComplexActualCallFullAlignment
