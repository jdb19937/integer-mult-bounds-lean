module

public import IntegerMultBounds.Machine.CompactComplexAlignedChildEntryPath
public import IntegerMultBounds.Machine.CompactComplexFixedNodeSavedReturnPath
public import IntegerMultBounds.Machine.CompactComplexSourceReadySavedCallHistory

/-! The actual prime-alphabet aligned table pops the genuine top call.
The older association and erased-cell blanks come from the physical history;
all other tapes, including the basis workspace, are retained literally. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexAlignedSavedReturnPath
noncomputable section
open Networks.Shared50ModularControl (prime)
open Networks.ComplexRecursiveCallSchema (Call)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactComplexActualCallFullAlignment (localTapes)
open CompactNativeRoleConjugatedPorts (encoding)
open SharedPlacementAlphabet (setTape)
variable {s q : ℕ}
attribute [local irreducible] Networks.ComplexRank25.program
  Networks.ComplexRecursiveCallSchema.sites CompactComplexCompletedLiveLower.schedule
  CompactComplexRolePhaseSite.roleCount CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth

private theorem encoded_bit (b : Bool) : encoding.encode (bitSymbol (a:=2) b)=bitSymbol (a:=prime) b := by
  cases b <;> rfl

private theorem encoded_word {k : ℕ} (f : ℤ → Fin 6) (p : ℤ)
    (code : FiniteReturnStack.Code k) :
    (fun z => encoding.encode (FiniteReturnStack.wordPart f p code k le_rfl z))=
      FiniteReturnStack.wordPart (fun z => encoding.encode (f z)) p code k le_rfl := by
  funext z
  unfold FiniteReturnStack.wordPart
  split_ifs <;> simp only [encoded_bit]

private theorem encoded_setTape {t : ℕ} (v : Tapes t 2) (i : Fin t) (f : ℤ → Fin 6) (p : ℤ) :
    Alphabet.mapTapes encoding (setTape v i f p)=
      setTape (Alphabet.mapTapes encoding v) i (fun z => encoding.encode (f z)) p := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext j z
    simp only [Alphabet.mapTapes,setTape,Function.update_apply]
    split_ifs <;> rfl

/-- The literal guard and pop of the actual aligned table restore precisely
an older associated stack, charging the address width plus five transitions. -/
theorem associated_return_path (P : Program ActivePrefixStageNative.tapes q prime)
    (headerStack pcStack liveStack : Fin s) (call : Call)
    (v : Tapes (CompactComplexSourceReadyScalarWorkspace.tapes s roles) 2)
    (suffix : Tapes (localTapes roles) prime) (origin : ℤ) (calls : List Call)
    (h : CompactComplexSourceReadySavedCallHistory.Associated origin (call::calls)
      (v.tape (CompactComplexSourceReadyCorrectedActualTable.savedStackSlot pcStack))
      (v.head (CompactComplexSourceReadyCorrectedActualTable.savedStackSlot pcStack))) :
    ∃ older top,
      CompactComplexSourceReadySavedCallHistory.Associated origin calls older top ∧
      CompactComplexAlignedChildEntryPath.path P headerStack pcStack liveStack 0
        ((Alphabet.mapTapes encoding v).append suffix)
        (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)+5)
        (CompactComplexScheduledPCDecode.savedPC call)
        ((Alphabet.mapTapes encoding (setTape v
          (CompactComplexSourceReadyCorrectedActualTable.savedStackSlot pcStack) older top)).append suffix) := by
  obtain ⟨older,top,ha,hb,hs,hh⟩ := CompactComplexSourceReadySavedCallHistory.top h
  refine ⟨older,top,ha,?_⟩
  have hw : 0<CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3) := by
    rw [←CompactComplexSourceReadyDirection.width_eq]
    exact CompactComplexSourceReadyOrientation.width_positive call
  have hp := CompactComplexFixedNodeSavedReturnPath.saved_return_path
    (Nat.zero_lt_of_lt (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack).isLt)
    (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack)
    (CompactComplexActualCallFullAlignment.childReturn P headerStack liveStack)
    (CompactComplexSourceReadyAlignedActualTable.controls pcStack)
    (CompactComplexSourceReadyAlignedActualTable.event P headerStack pcStack liveStack)
    (CompactComplexSourceReadyAlignedActualTable.classify pcStack) call
    ((Alphabet.mapTapes encoding v).append suffix) (fun z => encoding.encode (older z)) top hw
    (by simpa only [CompactComplexSourceReadyAlignedActualTable.savedStackSlot,
      Tapes.append,Fin.addCases_left,Alphabet.mapTapes,hs] using encoded_word older top (CompactComplexCallReturn.code call))
    (by simpa only [CompactComplexSourceReadyAlignedActualTable.savedStackSlot,
      Tapes.append,Fin.addCases_left,Alphabet.mapTapes] using hh)
    (by intro j hj;rw [hb _ (by omega)];rfl)
  rw [CompactComplexSourceReadyAlignedActualTable.savedStackSlot,
    SharedPlacementAlphabet.setTape_append_left,←encoded_setTape] at hp
  exact hp

/-- The completed public child bank can supply the genuine saved association;
physical pop retains the entire literal ready/scalar/basis layout. -/
theorem public_associated_return_path (P : Program ActivePrefixStageNative.tapes q prime)
    (headerStack pcStack liveStack : Fin s) (call : Call)
    (v : Tapes (CompactComplexNonleafRoleChildBank.tapes s roles) 2)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (suffix : Tapes (localTapes roles) prime) (origin : ℤ) (calls : List Call)
    (h : CompactComplexSourceReadySavedCallHistory.Associated origin (call::calls)
      (v.tape (CompactComplexSourceReadyCorrectedSavedReturnPath.publicSaved pcStack))
      (v.head (CompactComplexSourceReadyCorrectedSavedReturnPath.publicSaved pcStack))) :
    ∃ older top,
      CompactComplexSourceReadySavedCallHistory.Associated origin calls older top ∧
      CompactComplexAlignedChildEntryPath.path P headerStack pcStack liveStack 0
        ((Alphabet.mapTapes encoding ((CompactComplexSourceReadyWorkspace.ready v).append scalar)).append suffix)
        (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)+5)
        (CompactComplexScheduledPCDecode.savedPC call)
        ((Alphabet.mapTapes encoding ((CompactComplexSourceReadyWorkspace.ready
          (setTape v (CompactComplexSourceReadyCorrectedSavedReturnPath.publicSaved pcStack) older top)).append scalar)).append suffix) := by
  have ha := CompactComplexSourceReadySavedCallHistory.ready_associated (s:=s) pcStack origin (call::calls) v scalar h
  obtain ⟨older,top,ho,hp⟩  := associated_return_path (s:=s) (q:=q) P headerStack pcStack liveStack call
    ((CompactComplexSourceReadyWorkspace.ready v).append scalar) suffix origin calls ha
  refine ⟨older,top,ho,?_⟩
  have he := CompactComplexSourceReadyCorrectedSavedReturnPath.restored_ready (s:=s) pcStack v scalar older top
  simp only [←CompactComplexSourceReadyWorkspace.ready_leaf] at he
  rw [he] at hp
  exact hp

end
end IntegerMultBounds.Machine.CompactComplexAlignedSavedReturnPath
