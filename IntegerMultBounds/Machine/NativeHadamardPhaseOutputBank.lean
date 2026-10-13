module

public import IntegerMultBounds.Machine.NativeHadamardPhaseRootBank
public import IntegerMultBounds.Machine.NativeHadamardPhaseRootHeaders
public import IntegerMultBounds.Machine.AlphabetTapeReplacement
public import IntegerMultBounds.Machine.CompactComplexRootWorkspaceClean

/-! The same fixed phase program executes on an actual clean returned root
bank. Header/source readiness comes from that bank's execution certificate;
there is no canonical-bank reconstruction or supplied phase execution. -/

@[expose] public section
namespace IntegerMultBounds.Machine.NativeHadamardPhaseOutputBank
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactComplexSourceReadyScalarWorkspace (roles scratch)
open CompactComplexSourceReadyWorkspace (tapes publicTapes leafTapes)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexRecursiveGeometry (arity)
open SharedPlacementAlphabet (setTape)
variable {stackCount : ℕ} {shape : Shape} {rows ell : ℕ}
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount
  NativeHadamardPhaseFixed.program NativeEndpointSourceReadyPlacement.program
  CompactComplexSourceReadyAlignedActualTable.liftPair

abbrev CallerCount (stackCount : ℕ) := NativeEndpointSourceReadyPlacement.callerTapes stackCount roles
abbrev TailCount := NativeEndpointSourceReadyPlacement.tailTapes scratch

def placement : Fin (CallerCount stackCount+TailCount) ≃ Fin (tapes stackCount roles+scratch) :=
  NativeEndpointSourceReadyPlacement.placement

def caller (bank : Tapes (tapes stackCount roles) 2) : Tapes (CallerCount stackCount) 2 :=
  Placement.active placement (bank.append (SharedBank.empty scratch 2))

def tail (bank : Tapes (tapes stackCount roles) 2) : Tapes TailCount 2 :=
  Placement.extra placement (bank.append (SharedBank.empty scratch 2))

def output (stage : Stage shape) (metadataPrecision : ℕ) (input : Array shape rows ell)
    (bank : Tapes (tapes stackCount roles) 2) :=
  setTape bank CompactComplexSourceReadyOrientation.source
    (NativeZeroPadding.word (NativeZeroPaddingArray.word (NativeHadamardPhaseOriginal.result stage metadataPrecision input))) 0

private theorem source_value : (CompactComplexSourceReadyOrientation.source (s:=stackCount) (c:=roles)).val=109 := by
  simp only [CompactComplexSourceReadyOrientation.source,NativePolynomialConjugationWorkspace.source,
    CompactComplexNonleafRoleEntry.source,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd,
    show (65 : Fin 66).val=65 from rfl]

private theorem public_source_bound : 109<publicTapes stackCount roles := by
  have bound := (CompactComplexSourceReadyOrientedControlsFrame.source (s:=stackCount) (c:=roles)).isLt
  simpa only [CompactComplexSourceReadyOrientedControlsFrame.source,CompactComplexNonleafRoleEntry.source,
    CompactComplexSpectatorTargetBank.numericSlot,CompactComplexControllerNativeFrame.nativeSlot,
    Fin.val_castAdd,Fin.val_natAdd,show (65 : Fin 66).val=65 from rfl] using bound

theorem output_clean (stage : Stage shape) (metadataPrecision : ℕ) (input : Array shape rows ell)
    (bank : Tapes (tapes stackCount roles) 2) (clean : CompactComplexRootWorkspaceClean.Clean bank) :
    CompactComplexRootWorkspaceClean.Clean (output stage metadataPrecision input bank) := by
  have publicBound := public_source_bound (stackCount:=stackCount)
  rcases clean with ⟨leafClean,workClean,frameClean,roleClean⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro leafPort
    have distinct : Fin.castAdd 10 (Fin.natAdd (publicTapes stackCount roles) leafPort) ≠
        CompactComplexSourceReadyOrientation.source (s:=stackCount) (c:=roles) := by
      intro same
      have sameValue := congrArg Fin.val same
      simp only [Fin.val_castAdd,Fin.val_natAdd,source_value] at sameValue
      omega
    simpa only [output,setTape,Function.update_of_ne distinct] using leafClean leafPort
  · intro workPort
    have distinct : Fin.natAdd (publicTapes stackCount roles+leafTapes) workPort ≠
        CompactComplexSourceReadyOrientation.source (s:=stackCount) (c:=roles) := by
      intro same
      have sameValue := congrArg Fin.val same
      simp only [Fin.val_natAdd,source_value] at sameValue
      omega
    simpa only [output,setTape,Function.update_of_ne distinct] using workClean workPort
  · intro framePort
    have distinct : Fin.castAdd 10 (Fin.castAdd leafTapes
        (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes (10+stackCount) roles) framePort)) ≠
        CompactComplexSourceReadyOrientation.source (s:=stackCount) (c:=roles) := by
      intro same
      have sameValue := congrArg Fin.val same
      have sourceBound := (CompactComplexNonleafRoleEntry.source (s:=10+stackCount) (c:=roles)).isLt
      simp only [CompactComplexNonleafRoleEntry.source,CompactComplexSpectatorTargetBank.numericSlot,
        CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd,show (65 : Fin 66).val=65 from rfl] at sourceBound
      simp only [Fin.val_castAdd,Fin.val_natAdd,source_value] at sameValue
      omega
    simpa only [output,setTape,Function.update_of_ne distinct] using frameClean framePort
  · intro rolePort
    have distinct : Fin.castAdd 10 (Fin.castAdd leafTapes
        (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.roleTape (s:=10+stackCount) (c:=roles) rolePort))) ≠
        CompactComplexSourceReadyOrientation.source (s:=stackCount) (c:=roles) := by
      intro same
      have sameValue := congrArg Fin.val same
      simp only [CompactComplexNonleafRoleEntry.roleTape,CompactComplexSpectatorTargetBank.roleSlot,
        CompactComplexNativeRoleBridge.roleSlot,CompactComplexControllerNativeFrame.tapes,
        Fin.val_castAdd,Fin.val_natAdd,source_value] at sameValue
      omega
    simpa only [output,setTape,Function.update_of_ne distinct] using roleClean rolePort

theorem output_headers (stage : Stage shape) (metadataPrecision : ℕ) (input : Array shape rows ell)
    (bank : Tapes (tapes stackCount roles) 2)
    (headersReady : NativeHadamardPhaseRootHeaders.Ready stage rows ell metadataPrecision bank) :
    NativeHadamardPhaseRootHeaders.Ready stage rows ell metadataPrecision (output stage metadataPrecision input bank) := by
  intro header
  have distinct : NativeHadamardPhaseRootHeaders.slot (stackCount:=stackCount) header ≠
      CompactComplexSourceReadyOrientation.source (s:=stackCount) (c:=roles) := by
    intro same
    have sameValue := congrArg Fin.val same
    have headerBound := (NativeEndpointCharacterCopy.index header).isLt
    simp only [NativeHadamardPhaseRootHeaders.slot,CompactComplexNonleafRoleEntry.numeric,
      CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.nativeSlot,
      Fin.val_castAdd,Fin.val_natAdd,source_value] at sameValue
    omega
  simpa only [output,setTape,Function.update_of_ne distinct] using headersReady header

private theorem caller_count : CallerCount (stackCount:=stackCount)=publicTapes stackCount roles := rfl

private theorem focus_slot (header : Fin 15) :
    placement (stackCount:=stackCount) (Fin.castAdd TailCount (NativeHadamardPhaseRootBank.focus header))=
      Fin.castAdd scratch (NativeHadamardPhaseRootHeaders.slot header) := by
  apply Fin.ext
  simp only [placement,NativeEndpointSourceReadyPlacement.placement,finCongr_apply,Fin.val_cast,
    Fin.val_castAdd,NativeHadamardPhaseRootBank.focus,NativeEndpointNamedPorts.focus,
    CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.nativeSlot,Fin.val_natAdd,
    NativeHadamardPhaseRootHeaders.slot,CompactComplexNonleafRoleEntry.numeric]

private theorem source_slot :
    placement (stackCount:=stackCount) (Fin.castAdd TailCount NativeHadamardPhaseRootBank.source)=
      Fin.castAdd scratch CompactComplexSourceReadyOrientation.source := by
  apply Fin.ext
  simp only [placement,NativeEndpointSourceReadyPlacement.placement,finCongr_apply,Fin.val_cast,
    Fin.val_castAdd,NativeHadamardPhaseRootBank.source,CompactComplexSourceReadyOrientation.source,
    NativePolynomialConjugationWorkspace.source,CompactComplexNonleafRoleEntry.source,
    CompactComplexSpectatorTargetBank.numericSlot,CompactComplexControllerNativeFrame.nativeSlot,Fin.val_natAdd]

private theorem leaf_slot (index : Fin 67) :
    placement (stackCount:=stackCount) (Fin.natAdd (CallerCount stackCount)
      (⟨index.val,by
        have := index.isLt
        have := NativeHadamardPhaseRootBank.leaf_capacity
        unfold TailCount NativeEndpointSourceReadyPlacement.tailTapes
        omega⟩ : Fin TailCount))=
      Fin.castAdd scratch (Fin.castAdd 10 (Fin.natAdd (publicTapes stackCount roles)
        (⟨index.val,lt_of_lt_of_le index.isLt NativeHadamardPhaseRootBank.leaf_capacity⟩ : Fin leafTapes))) := by
  apply Fin.ext
  simp only [placement,NativeEndpointSourceReadyPlacement.placement,finCongr_apply,Fin.val_cast,
    Fin.val_natAdd,Fin.val_castAdd,caller_count]

private theorem reindex_setTape {leftCount rightCount alphabet : ℕ} (equivalence : Fin leftCount ≃ Fin rightCount)
    (bank : Tapes leftCount alphabet) (source : Fin leftCount) (word : ℤ → Fin (alphabet+4)) (head : ℤ) :
    (setTape bank source word head).reindex equivalence = setTape (bank.reindex equivalence) (equivalence source) word head := by
  apply congrArg₂ Tapes.mk <;> funext port
  all_goals simp [setTape,Tapes.reindex,Function.update_apply,equivalence.symm_apply_eq]

/-- The actual returned bank executes the fixed output phase, with every other
tape and head retained, the borrowed workspace restored and all steps paid. -/
theorem binary_runs (stage : Stage shape) (metadataPrecision : ℕ) (stageSlots : stage.slots=arity)
    (rowsPositive : 0<rows) (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes)
    (guardFits : shape.guard+1≤shape.chunk) (unitPayload : shape.payload=1)
    (input : Array shape rows ell)
    (inputWidth : ∀ index, (input index).1.length=NativePolynomialStageShape.width shape metadataPrecision ∧
      (input index).2.length=NativePolynomialStageShape.width shape metadataPrecision)
    (bank : Tapes (tapes stackCount roles) 2)
    (clean : CompactComplexRootWorkspaceClean.Clean bank)
    (headersReady : NativeHadamardPhaseRootHeaders.Ready stage rows ell metadataPrecision bank)
    (sourceWord : bank.tape CompactComplexSourceReadyOrientation.source=NativeZeroPadding.word (NativeZeroPaddingArray.word input))
    (sourceHead : bank.head CompactComplexSourceReadyOrientation.source=0) :
    HoareTime (NativeHadamardPhaseRootBank.binaryProgram (stackCount:=stackCount))
      (fun whole => whole=bank.append (SharedBank.empty scratch 2))
      (fun whole => whole=(output stage metadataPrecision input bank).append (SharedBank.empty scratch 2))
      (NativeHadamardPhaseOriginal.constant*CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision) := by
  have phaseRun := NativeHadamardPhaseFixed.runs NativeHadamardPhaseRootBank.focus NativeHadamardPhaseRootBank.source
    (caller bank) stage metadataPrecision stageSlots rowsPositive guardPositive axesPositive guardFits unitPayload input inputWidth
    (by intro header; simpa only [caller,Placement.active,focus_slot,Tapes.append,Fin.addCases_left] using (headersReady header).2)
    (by intro header; simpa only [caller,Placement.active,focus_slot,Tapes.append,Fin.addCases_left] using (headersReady header).1)
    (by simpa only [caller,Placement.active,source_slot,Tapes.append,Fin.addCases_left,NativeZeroPadding.word] using sourceWord)
    (by simpa only [caller,Placement.active,source_slot,Tapes.append,Fin.addCases_left] using sourceHead)
  have tailCapacity : 67≤TailCount := by
    have := NativeHadamardPhaseRootBank.leaf_capacity
    unfold TailCount NativeEndpointSourceReadyPlacement.tailTapes
    omega
  have tailBlank : ∀ index : Fin 67,
      (tail bank).head ⟨index.val,lt_of_lt_of_le index.isLt tailCapacity⟩=0 ∧
      (tail bank).tape ⟨index.val,lt_of_lt_of_le index.isLt tailCapacity⟩=(fun _ => blank) := by
    intro index
    simpa only [tail,Placement.extra,leaf_slot,Tapes.append,Fin.addCases_left] using
      clean.1 ⟨index.val,lt_of_lt_of_le index.isLt NativeHadamardPhaseRootBank.leaf_capacity⟩
  have localRun := NativeEndpointCharacterLeafPlacement.runs tailCapacity (caller bank)
    (NativeHadamardPhaseOriginal.resultCaller (caller bank) NativeHadamardPhaseRootBank.source stage metadataPrecision input)
    (tail bank) _ tailBlank phaseRun
  have physicalRun := hoare_reindex_eq localRun (placement (stackCount:=stackCount))
  have originalBank : ((caller bank).append (tail bank)).reindex placement=bank.append (SharedBank.empty scratch 2) :=
    Placement.view placement _
  have returnedBank : ((NativeHadamardPhaseOriginal.resultCaller (caller bank) NativeHadamardPhaseRootBank.source
      stage metadataPrecision input).append (tail bank)).reindex placement =
      (output stage metadataPrecision input bank).append (SharedBank.empty scratch 2) := by
    unfold NativeHadamardPhaseOriginal.resultCaller
    rw [←SharedPlacementAlphabet.setTape_append_left,reindex_setTape,source_slot,originalBank,
      SharedPlacementAlphabet.setTape_append_left]
    rfl
  unfold NativeHadamardPhaseRootBank.binaryProgram NativeEndpointSourceReadyPlacement.program
  apply physicalRun.consequence (fun _ equality => equality.trans originalBank.symm) _ le_rfl
  intro whole equality
  exact equality.trans returnedBank

/-- Alphabet lifting adds no transitions and preserves every appended basis
tape on this same actual post-root bank. -/
theorem runs (stage : Stage shape) (metadataPrecision : ℕ) (stageSlots : stage.slots=arity)
    (rowsPositive : 0<rows) (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes)
    (guardFits : shape.guard+1≤shape.chunk) (unitPayload : shape.payload=1)
    (input : Array shape rows ell)
    (inputWidth : ∀ index, (input index).1.length=NativePolynomialStageShape.width shape metadataPrecision ∧
      (input index).2.length=NativePolynomialStageShape.width shape metadataPrecision)
    (bank : Tapes (tapes stackCount roles) 2)
    (clean : CompactComplexRootWorkspaceClean.Clean bank)
    (headersReady : NativeHadamardPhaseRootHeaders.Ready stage rows ell metadataPrecision bank)
    (sourceWord : bank.tape CompactComplexSourceReadyOrientation.source=NativeZeroPadding.word (NativeZeroPaddingArray.word input))
    (sourceHead : bank.head CompactComplexSourceReadyOrientation.source=0) :
    HoareTime (NativeHadamardPhaseRootBank.program (stackCount:=stackCount)).2
      (fun whole => whole=CompactComplexAlignedBoundaryPaths.alignedBank (bank.append (SharedBank.empty scratch 2)))
      (fun whole => whole=CompactComplexAlignedBoundaryPaths.alignedBank
        ((output stage metadataPrecision input bank).append (SharedBank.empty scratch 2)))
      (NativeHadamardPhaseOriginal.constant*CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision) := by
  have phaseRun := binary_runs stage metadataPrecision stageSlots rowsPositive guardPositive axesPositive guardFits unitPayload
    input inputWidth bank clean headersReady sourceWord sourceHead
  exact CompactComplexSourceReadyAlignedActualTable.lift_runs _ _ _ _ phaseRun

end
end IntegerMultBounds.Machine.NativeHadamardPhaseOutputBank
