module

public import IntegerMultBounds.Machine.NativeHadamardNormalizationOriginal
public import IntegerMultBounds.Machine.NativeHadamardNormalizationRootLive
public import IntegerMultBounds.Machine.NativeHadamardPhaseOutputBank

/-! Complete normalization executes on the actual returned root bank. Original
raw/source/live readiness is projected from that same bank, borrowed leaf tapes
are reclaimed, and aligned scalar/basis suffixes remain literal frames. -/

@[expose] public section
namespace IntegerMultBounds.Machine.NativeHadamardNormalizationRootBank
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactComplexSourceReadyScalarWorkspace (roles scratch)
open CompactComplexSourceReadyWorkspace (tapes leafTapes)
open CompactSpectatorVisitGeometry (Array)
open SharedPlacementAlphabet (setTape)
open NativeHadamardPhaseOutputBank (CallerCount TailCount placement caller tail)
variable {stackCount : ℕ} {shape : Shape} {rows ell : ℕ}
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount

def current : Fin (CallerCount stackCount) := Fin.castAdd 9
  (CompactComplexSpectatorTargetBank.oldSlot (s:=10+stackCount) (c:=roles) ⟨7,by omega⟩)

theorem current_slot : placement (stackCount:=stackCount) (Fin.castAdd TailCount current)=
    Fin.castAdd scratch (NativeHadamardNormalizationRootLive.slot (stackCount:=stackCount)) := by
  apply Fin.ext
  simp only [placement,NativeEndpointSourceReadyPlacement.placement,finCongr_apply,Fin.val_cast,
    current,NativeHadamardNormalizationRootLive.slot,CompactComplexNonleafRoleChildBank.storage,
    Fin.val_castAdd,Fin.val_natAdd]

theorem source_current : NativeHadamardPhaseRootBank.source (stackCount:=stackCount)≠current := by
  intro equality
  have values := congrArg Fin.val equality
  simp only [NativeHadamardPhaseRootBank.source,current,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at values
  omega

def binaryProgram := NativeEndpointSourceReadyPlacement.program (s:=stackCount) (c:=roles) (w:=scratch)
  NativeHadamardPhaseRootBank.leaf_capacity
  (NativeHadamardNormalizationOriginal.promotedProgram NativeHadamardPhaseRootBank.focus
    NativeHadamardPhaseRootBank.source current source_current)

def program := CompactComplexSourceReadyAlignedActualTable.liftPair ⟨_,binaryProgram (stackCount:=stackCount)⟩

def output (stage : Stage shape) (live : ℕ) (coefficients : Array shape rows ell)
    (bank : Tapes (tapes stackCount roles) 2) :=
  setTape (setTape bank NativeHadamardNormalizationRootLive.slot
    (RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits (live+NativeHadamardNormalizationHeaders.increase stage))) 1)
    CompactComplexSourceReadyOrientation.source
    (putWord (fun _ => blank) 0 (NativeZeroPaddingArray.word (NativeHadamardNormalizationArray.result coefficients))) 0

private theorem live_value : (NativeHadamardNormalizationRootLive.slot (stackCount:=stackCount)).val=117 := by
  simp only [NativeHadamardNormalizationRootLive.slot,CompactComplexNonleafRoleChildBank.storage,
    CompactComplexSpectatorTargetBank.oldSlot,CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd]

private theorem live_update_clean (bank : Tapes (tapes stackCount roles) 2)
    (clean : CompactComplexRootWorkspaceClean.Clean bank) (word : ℤ → Fin 6) (head : ℤ) :
    CompactComplexRootWorkspaceClean.Clean (setTape bank NativeHadamardNormalizationRootLive.slot word head) := by
  have permanentBound := (CompactComplexSpectatorTargetBank.oldSlot (s:=10+stackCount) (c:=roles) ⟨7,by omega⟩).isLt
  have publicBound := (current (stackCount:=stackCount)).isLt
  simp only [current,CompactComplexSpectatorTargetBank.oldSlot,CompactComplexControllerNativeFrame.storageSlot,
    Fin.val_castAdd,Fin.val_natAdd] at permanentBound publicBound
  change 117<CompactComplexSourceReadyWorkspace.publicTapes stackCount roles at publicBound
  rcases clean with ⟨leafClean,workClean,frameClean,roleClean⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro port
    have distinct : Fin.castAdd 10 (Fin.natAdd (CompactComplexSourceReadyWorkspace.publicTapes stackCount roles) port)≠
        NativeHadamardNormalizationRootLive.slot (stackCount:=stackCount) := by
      intro equality
      have values := congrArg Fin.val equality
      simp only [Fin.val_castAdd,Fin.val_natAdd,live_value] at values
      omega
    simpa only [setTape,Function.update_of_ne distinct] using leafClean port
  · intro port
    have distinct : Fin.natAdd (CompactComplexSourceReadyWorkspace.publicTapes stackCount roles+leafTapes) port≠
        NativeHadamardNormalizationRootLive.slot (stackCount:=stackCount) := by
      intro equality
      have values := congrArg Fin.val equality
      simp only [Fin.val_natAdd,live_value] at values
      omega
    simpa only [setTape,Function.update_of_ne distinct] using workClean port
  · intro port
    have distinct : Fin.castAdd 10 (Fin.castAdd leafTapes
        (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes (10+stackCount) roles) port))≠
        NativeHadamardNormalizationRootLive.slot (stackCount:=stackCount) := by
      intro equality
      have values := congrArg Fin.val equality
      simp only [Fin.val_castAdd,Fin.val_natAdd,live_value,CompactComplexNonleafRoleEntry.tapes] at values
      omega
    simpa only [setTape,Function.update_of_ne distinct] using frameClean port
  · intro port
    have distinct : Fin.castAdd 10 (Fin.castAdd leafTapes
        (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.roleTape (s:=10+stackCount) (c:=roles) port)))≠
        NativeHadamardNormalizationRootLive.slot (stackCount:=stackCount) := by
      intro equality
      have values := congrArg Fin.val equality
      simp only [CompactComplexNonleafRoleEntry.roleTape,CompactComplexSpectatorTargetBank.roleSlot,
        CompactComplexNativeRoleBridge.roleSlot,CompactComplexControllerNativeFrame.tapes,
        Fin.val_castAdd,Fin.val_natAdd,live_value] at values
      omega
    simpa only [setTape,Function.update_of_ne distinct] using roleClean port

theorem output_clean (stage : Stage shape) (live : ℕ) (coefficients : Array shape rows ell)
    (bank : Tapes (tapes stackCount roles) 2) (clean : CompactComplexRootWorkspaceClean.Clean bank) :
    CompactComplexRootWorkspaceClean.Clean (output stage live coefficients bank) :=
  NativeHadamardPhaseOutputBank.source_update_clean _ (live_update_clean bank clean _ 1) _ 0

theorem output_live (stage : Stage shape) (live : ℕ) (coefficients : Array shape rows ell)
    (bank : Tapes (tapes stackCount roles) 2) :
    NativeHadamardNormalizationRootLive.Ready (live+NativeHadamardNormalizationHeaders.increase stage)
      (output stage live coefficients bank) := by
  simp only [NativeHadamardNormalizationRootLive.Ready,output,setTape,
    Function.update_of_ne NativeHadamardNormalizationRootLive.slot_ne_source,Function.update_self,and_self]

theorem output_headers (stage : Stage shape) (metadataPrecision live : ℕ) (coefficients : Array shape rows ell)
    (bank : Tapes (tapes stackCount roles) 2)
    (headersReady : NativeHadamardPhaseRootHeaders.Ready stage rows ell metadataPrecision bank) :
    NativeHadamardPhaseRootHeaders.Ready stage rows ell metadataPrecision (output stage live coefficients bank) := by
  intro header
  have distinctSource : NativeHadamardPhaseRootHeaders.slot (stackCount:=stackCount) header≠
      CompactComplexSourceReadyOrientation.source (s:=stackCount) (c:=roles) := by
    intro equality
    have values := congrArg Fin.val equality
    have headerBound := (NativeEndpointCharacterCopy.index header).isLt
    simp only [NativeHadamardPhaseRootHeaders.slot,CompactComplexNonleafRoleEntry.numeric,
      CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.nativeSlot,
      CompactComplexSourceReadyOrientation.source,NativePolynomialConjugationWorkspace.source,
      CompactComplexNonleafRoleEntry.source,CompactComplexSpectatorTargetBank.numericSlot,
      Fin.val_castAdd,Fin.val_natAdd] at values
    omega
  have distinctLive : NativeHadamardPhaseRootHeaders.slot (stackCount:=stackCount) header≠
      NativeHadamardNormalizationRootLive.slot (stackCount:=stackCount) := by
    intro equality
    have values := congrArg Fin.val equality
    have headerBound := (NativeEndpointCharacterCopy.index header).isLt
    simp only [NativeHadamardPhaseRootHeaders.slot,CompactComplexNonleafRoleEntry.numeric,
      CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.nativeSlot,
      Fin.val_castAdd,Fin.val_natAdd,live_value] at values
    omega
  simpa only [output,setTape,Function.update_of_ne distinctSource,Function.update_of_ne distinctLive] using headersReady header

/-- Original header/source and literal live certificates on the reached bank
execute normalization in the existing borrowed leaf workspace. No canonical
returned-bank equality, count/target or execution provider is assumed. -/
theorem binary_runs (stage : Stage shape) (metadataPrecision live : ℕ)
    (rowsPositive : 0<rows) (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes)
    (chunkPositive : 0<shape.chunk) (unitPayload : shape.payload=1)
    (selectedFits : stage.slots*stage.f≤shape.bits)
    (liveFits : live≤CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision)
    (coefficients : Array shape rows ell)
    (coefficientWidths : ∀ index,(coefficients index).1.length=NativePolynomialStageShape.width shape metadataPrecision ∧
      (coefficients index).2.length=NativePolynomialStageShape.width shape metadataPrecision)
    (bank : Tapes (tapes stackCount roles) 2) (clean : CompactComplexRootWorkspaceClean.Clean bank)
    (headersReady : NativeHadamardPhaseRootHeaders.Ready stage rows ell metadataPrecision bank)
    (sourceWord : bank.tape CompactComplexSourceReadyOrientation.source=putWord (fun _ => blank) 0 (NativeZeroPaddingArray.word coefficients))
    (sourceHead : bank.head CompactComplexSourceReadyOrientation.source=0)
    (liveReady : NativeHadamardNormalizationRootLive.Ready live bank) :
    HoareTime binaryProgram (fun whole => whole=bank.append (SharedBank.empty scratch 2))
      (fun whole => whole=(output stage live coefficients bank).append (SharedBank.empty scratch 2))
      (NativeHadamardNormalizationOriginal.constant*CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision) := by
  have normalizationRun := NativeHadamardNormalizationOriginal.runs_linear NativeHadamardPhaseRootBank.focus
    NativeHadamardPhaseRootBank.source current source_current (caller bank) stage metadataPrecision live rowsPositive
    guardPositive axesPositive chunkPositive unitPayload selectedFits liveFits coefficients coefficientWidths
    (by intro header; simpa only [caller,Placement.active,NativeHadamardPhaseOutputBank.focus_slot,Tapes.append,Fin.addCases_left]
          using (headersReady header).2)
    (by intro header; simpa only [caller,Placement.active,NativeHadamardPhaseOutputBank.focus_slot,Tapes.append,Fin.addCases_left]
          using (headersReady header).1)
    (by simpa only [caller,Placement.active,NativeHadamardPhaseOutputBank.source_slot,Tapes.append,Fin.addCases_left] using sourceWord)
    (by simpa only [caller,Placement.active,NativeHadamardPhaseOutputBank.source_slot,Tapes.append,Fin.addCases_left] using sourceHead)
    (by simpa only [caller,Placement.active,current_slot,Tapes.append,Fin.addCases_left] using liveReady.2)
    (by simpa only [caller,Placement.active,current_slot,Tapes.append,Fin.addCases_left] using liveReady.1)
  let finalCaller := NativeHadamardNormalizationOriginal.resultCaller (caller bank) NativeHadamardPhaseRootBank.source
    current stage live coefficients
  have promoted := NativeHadamardNormalizationOriginal.promote_runs NativeHadamardPhaseRootBank.focus
    NativeHadamardPhaseRootBank.source current source_current (caller bank) finalCaller _ normalizationRun
  have tailCapacity : 67≤TailCount := by
    have := NativeHadamardPhaseRootBank.leaf_capacity
    unfold TailCount NativeEndpointSourceReadyPlacement.tailTapes
    omega
  have tailBlank : ∀ index : Fin 67,
      (tail bank).head ⟨index.val,lt_of_lt_of_le index.isLt tailCapacity⟩=0 ∧
      (tail bank).tape ⟨index.val,lt_of_lt_of_le index.isLt tailCapacity⟩=(fun _ => blank) := by
    intro index
    simpa only [tail,Placement.extra,NativeHadamardPhaseOutputBank.leaf_slot,Tapes.append,Fin.addCases_left] using
      clean.1 ⟨index.val,lt_of_lt_of_le index.isLt NativeHadamardPhaseRootBank.leaf_capacity⟩
  have localRun := NativeEndpointCharacterLeafPlacement.runs tailCapacity (caller bank) finalCaller (tail bank) _ tailBlank promoted
  have physicalRun := hoare_reindex_eq localRun (placement (stackCount:=stackCount))
  have originalBank : ((caller bank).append (tail bank)).reindex placement=bank.append (SharedBank.empty scratch 2) :=
    Placement.view placement _
  have finalBank : (finalCaller.append (tail bank)).reindex placement=
      (output stage live coefficients bank).append (SharedBank.empty scratch 2) := by
    dsimp only [finalCaller,NativeHadamardNormalizationOriginal.resultCaller]
    rw [←SharedPlacementAlphabet.setTape_append_left,←SharedPlacementAlphabet.setTape_append_left,
      NativeHadamardPhaseOutputBank.reindex_setTape,NativeHadamardPhaseOutputBank.reindex_setTape,
      NativeHadamardPhaseOutputBank.source_slot,current_slot,originalBank,
      SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left]
    rfl
  unfold binaryProgram NativeEndpointSourceReadyPlacement.program
  apply physicalRun.consequence (fun _ equality => equality.trans originalBank.symm) _ le_rfl
  intro whole equality
  exact equality.trans finalBank

/-- Alphabet lifting preserves every scalar/basis suffix and adds no steps.
The same actual root source/live words are installed and all borrowed tapes
are reclaimed, at one fixed native-volume allowance. -/
theorem runs (stage : Stage shape) (metadataPrecision live : ℕ)
    (rowsPositive : 0<rows) (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes)
    (chunkPositive : 0<shape.chunk) (unitPayload : shape.payload=1)
    (selectedFits : stage.slots*stage.f≤shape.bits)
    (liveFits : live≤CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision)
    (coefficients : Array shape rows ell)
    (coefficientWidths : ∀ index,(coefficients index).1.length=NativePolynomialStageShape.width shape metadataPrecision ∧
      (coefficients index).2.length=NativePolynomialStageShape.width shape metadataPrecision)
    (bank : Tapes (tapes stackCount roles) 2) (clean : CompactComplexRootWorkspaceClean.Clean bank)
    (headersReady : NativeHadamardPhaseRootHeaders.Ready stage rows ell metadataPrecision bank)
    (sourceWord : bank.tape CompactComplexSourceReadyOrientation.source=putWord (fun _ => blank) 0 (NativeZeroPaddingArray.word coefficients))
    (sourceHead : bank.head CompactComplexSourceReadyOrientation.source=0)
    (liveReady : NativeHadamardNormalizationRootLive.Ready live bank) :
    HoareTime program.2
      (fun whole => whole=CompactComplexAlignedBoundaryPaths.alignedBank (bank.append (SharedBank.empty scratch 2)))
      (fun whole => whole=CompactComplexAlignedBoundaryPaths.alignedBank
        ((output stage live coefficients bank).append (SharedBank.empty scratch 2)))
      (NativeHadamardNormalizationOriginal.constant*CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision) := by
  exact CompactComplexSourceReadyAlignedActualTable.lift_runs _ _ _ _
    (binary_runs stage metadataPrecision live rowsPositive guardPositive axesPositive chunkPositive unitPayload selectedFits
      liveFits coefficients coefficientWidths bank clean headersReady sourceWord sourceHead liveReady)

end
end IntegerMultBounds.Machine.NativeHadamardNormalizationRootBank
