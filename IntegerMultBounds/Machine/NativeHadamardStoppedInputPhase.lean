module

public import IntegerMultBounds.Machine.NativeHadamardStoppedRootPorts

/-! Original positive stopped-root readiness survives the actual input phase.
This produces both its execution and the exact phase-modified leaf input; no
phase execution or corrected-input readiness is supplied by the caller. -/

@[expose] public section
namespace IntegerMultBounds.Machine.NativeHadamardStoppedInputPhase
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Grid Width half)
open CompactComplexSourceReadyScalarWorkspace (roles scratch)
open CompactComplexSourceReadyWorkspace (publicTapes ready)
open NativeHadamardStoppedRootPorts (phased)
variable {stackCount : ℕ} {shape : Shape} {rows ell : ℕ}
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount NativeHadamardPhaseRootBank.program

structure Certificate (stage : Stage shape) (precision baseline growthConstant live : ℕ)
    {left exponent levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path shape.active left exponent levels frames returned)
    (pcStack : Fin stackCount) (inputBank : Tapes (publicTapes stackCount roles) 2)
    (coefficients : Array shape rows ell) : Prop where
  execution : HoareTime (NativeHadamardPhaseRootBank.program (stackCount:=stackCount)).2
    (fun bank => bank=CompactComplexAlignedBoundaryPaths.alignedBank ((ready inputBank).append (SharedBank.empty scratch 2)))
    (fun bank => bank=CompactComplexAlignedBoundaryPaths.alignedBank
      ((ready (phased stage (ButterflyIndependentGuardHeaders.reservation shape.bits precision) coefficients inputBank)).append (SharedBank.empty scratch 2)))
    (NativeHadamardPhaseOriginal.constant*CompactNativeRoleTransferBudget.volume rows shape ell (ButterflyIndependentGuardHeaders.reservation shape.bits precision))
  widths : ∀ index,
    (NativeHadamardPhaseOriginal.result stage (ButterflyIndependentGuardHeaders.reservation shape.bits precision) coefficients index).1.length=
      CompactNativeRoleHeaders.recordWidth shape (ButterflyIndependentGuardHeaders.reservation shape.bits precision) ∧
    (NativeHadamardPhaseOriginal.result stage (ButterflyIndependentGuardHeaders.reservation shape.bits precision) coefficients index).2.length=
      CompactNativeRoleHeaders.recordWidth shape (ButterflyIndependentGuardHeaders.reservation shape.bits precision)
  grid : Grid shape rows ell precision live (CompactRecursiveGridBudget.bound baseline growthConstant levels (frames+2*returned))
    (NativeHadamardPhaseOriginal.result stage (ButterflyIndependentGuardHeaders.reservation shape.bits precision) coefficients)
  raw : Placement.active CompactComplexNonleafRoleEntry.headerPlacement
    (CompactComplexNonleafRoleSourceReturn.base (phased stage (ButterflyIndependentGuardHeaders.reservation shape.bits precision) coefficients inputBank))=
    ActiveRepairRankHeadersCommands.bank (NativeEndpointCharacterPrepare.raw stage rows ell (ButterflyIndependentGuardHeaders.reservation shape.bits precision))
  stackEmpty : (ready (phased stage (ButterflyIndependentGuardHeaders.reservation shape.bits precision) coefficients inputBank)).tape
    (CompactComplexSourceReadyOrientationInvariants.savedSlot pcStack)
    ((ready (phased stage (ButterflyIndependentGuardHeaders.reservation shape.bits precision) coefficients inputBank)).head
      (CompactComplexSourceReadyOrientationInvariants.savedSlot pcStack)-1)=blank
  guardReady : CompactComplexSourceReadyGuard.Ready (phased stage (ButterflyIndependentGuardHeaders.reservation shape.bits precision) coefficients inputBank)
  dimension : let next := phased stage (ButterflyIndependentGuardHeaders.reservation shape.bits precision) coefficients inputBank
    next.head CompactComplexSourceReadyGuard.dimension=1 ∧ next.tape CompactComplexSourceReadyGuard.dimension=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits shape.axes)
  source : let next := phased stage (ButterflyIndependentGuardHeaders.reservation shape.bits precision) coefficients inputBank
    next.head (NativeHadamardStoppedRootPorts.source (stackCount:=stackCount))=0 ∧
    next.tape (NativeHadamardStoppedRootPorts.source (stackCount:=stackCount))=CompactSpectatorLeafAxis.word
      (NativeHadamardPhaseOriginal.result stage (ButterflyIndependentGuardHeaders.reservation shape.bits precision) coefficients)
  current : let next := phased stage (ButterflyIndependentGuardHeaders.reservation shape.bits precision) coefficients inputBank
    next.head CompactComplexNonleafRoleChildBank.current=1 ∧ next.tape CompactComplexNonleafRoleChildBank.current=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits live)
  target : let next := phased stage (ButterflyIndependentGuardHeaders.reservation shape.bits precision) coefficients inputBank
    next.head CompactComplexNonleafRoleChildBank.target=0 ∧ next.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank)
  exponentWord : (phased stage (ButterflyIndependentGuardHeaders.reservation shape.bits precision) coefficients inputBank).tape
    (CompactComplexNonleafRoleChildBank.control 1)=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits exponent)
  exponentHead : (phased stage (ButterflyIndependentGuardHeaders.reservation shape.bits precision) coefficients inputBank).head
    (CompactComplexNonleafRoleChildBank.control 1)=1
  clean : CompactComplexStoppedRootWorkspaceClean.PublicClean (phased stage (ButterflyIndependentGuardHeaders.reservation shape.bits precision) coefficients inputBank)

/-- One physical input-phase call produces every genuine stopped-leaf input
certificate, with full private cleanup and a fixed native-volume allowance. -/
theorem prepares (stage : Stage shape) (precision baseline growthConstant live : ℕ)
    {left exponent levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path shape.active left exponent levels frames returned)
    (pcStack : Fin stackCount) (inputBank : Tapes (publicTapes stackCount roles) 2) (coefficients : Array shape rows ell)
    (stageSlots : stage.slots=CompactComplexRecursiveGeometry.arity)
    (rowsPositive : 0<rows) (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes)
    (guardFitsChunk : shape.guard+1≤shape.chunk) (unitPayload : shape.payload=1)
    (baselineFits : baseline≤precision)
    (dependencyFits : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant≤shape.chunk)
    (sourceWidth : Width shape rows ell precision coefficients)
    (inputGrid : Grid shape rows ell precision live (CompactRecursiveGridBudget.bound baseline growthConstant levels (frames+2*returned)) coefficients)
    (rawHeaders : Placement.active CompactComplexNonleafRoleEntry.headerPlacement (CompactComplexNonleafRoleSourceReturn.base inputBank)=
      ActiveRepairRankHeadersCommands.bank (NativeEndpointCharacterPrepare.raw stage rows ell (ButterflyIndependentGuardHeaders.reservation shape.bits precision)))
    (stackEmpty : (ready inputBank).tape (CompactComplexSourceReadyOrientationInvariants.savedSlot pcStack)
      ((ready inputBank).head (CompactComplexSourceReadyOrientationInvariants.savedSlot pcStack)-1)=blank)
    (guardReady : CompactComplexSourceReadyGuard.Ready inputBank)
    (dimensionReady : inputBank.head CompactComplexSourceReadyGuard.dimension=1 ∧ inputBank.tape CompactComplexSourceReadyGuard.dimension=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits shape.axes))
    (publicSourceReady : inputBank.head (NativeHadamardStoppedRootPorts.source (stackCount:=stackCount))=0 ∧
      inputBank.tape (NativeHadamardStoppedRootPorts.source (stackCount:=stackCount))=CompactSpectatorLeafAxis.word coefficients)
    (liveReady : inputBank.head CompactComplexNonleafRoleChildBank.current=1 ∧ inputBank.tape CompactComplexNonleafRoleChildBank.current=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits live))
    (targetBlank : inputBank.head CompactComplexNonleafRoleChildBank.target=0 ∧ inputBank.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank))
    (exponentWord : inputBank.tape (CompactComplexNonleafRoleChildBank.control 1)=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits exponent))
    (exponentHead : inputBank.head (CompactComplexNonleafRoleChildBank.control 1)=1)
    (publicClean : CompactComplexStoppedRootWorkspaceClean.PublicClean inputBank) :
    Certificate stage precision baseline growthConstant live path pcStack inputBank coefficients := by
  let metadataPrecision := ButterflyIndependentGuardHeaders.reservation shape.bits precision
  let phaseArray := NativeHadamardPhaseOriginal.result stage metadataPrecision coefficients
  let phaseBank := phased stage metadataPrecision coefficients inputBank
  have nativeWidth : ∀ index,(coefficients index).1.length=NativePolynomialStageShape.width shape metadataPrecision ∧
      (coefficients index).2.length=NativePolynomialStageShape.width shape metadataPrecision := by
    intro index
    simpa only [NativePolynomialStageShape.width,metadataPrecision,ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using sourceWidth index
  have storedWidths : ∀ index,(coefficients index).1.length=half shape precision+1 ∧ (coefficients index).2.length=half shape precision+1 := by
    intro index
    simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using sourceWidth index
  have headers := NativeHadamardStoppedRootPorts.headers_ready stage rows ell metadataPrecision inputBank rawHeaders
  have execution := NativeHadamardPhaseOutputBank.runs stage metadataPrecision stageSlots rowsPositive guardPositive axesPositive guardFitsChunk
    unitPayload coefficients nativeWidth (ready inputBank) (CompactComplexStoppedRootWorkspaceClean.ready_clean inputBank publicClean) headers
    (by simpa only [NativeHadamardStoppedRootPorts.source,CompactComplexSourceReadyOrientation.source,NativePolynomialConjugationWorkspace.source,
      CompactComplexSourceReadyLeafPhase.source,CompactSpectatorLeafAxis.word,ButterflyStreamData.full,NativeZeroPadding.word,NativeZeroPaddingArray.word,
      ready,CompactComplexSourceReadyWorkspace.bank,Tapes.append,Fin.addCases_left] using publicSourceReady.2)
    (by simpa only [NativeHadamardStoppedRootPorts.source,CompactComplexSourceReadyOrientation.source,NativePolynomialConjugationWorkspace.source,
      CompactComplexSourceReadyLeafPhase.source,ready,CompactComplexSourceReadyWorkspace.bank,Tapes.append,Fin.addCases_left] using publicSourceReady.1)
  rw [←NativeHadamardStoppedRootPorts.phased_ready] at execution
  have phaseWidth := NativeHadamardPhaseOriginal.result_width stage metadataPrecision (half shape precision+1) coefficients storedWidths
  have saved := NativeHadamardStoppedRootPorts.saved_source_update inputBank pcStack (putWord (fun _ => blank) 0 (NativeZeroPaddingArray.word phaseArray)) 0
  have current := NativeHadamardStoppedRootPorts.source_update_retained inputBank
    (putWord (fun _ => blank) 0 (NativeZeroPaddingArray.word phaseArray)) 0 _ NativeHadamardStoppedRootPorts.current_ne_source
  have target := NativeHadamardStoppedRootPorts.source_update_retained inputBank
    (putWord (fun _ => blank) 0 (NativeZeroPaddingArray.word phaseArray)) 0 _ NativeHadamardStoppedRootPorts.target_ne_source
  have dimension := NativeHadamardStoppedRootPorts.source_update_retained inputBank
    (putWord (fun _ => blank) 0 (NativeZeroPaddingArray.word phaseArray)) 0 _ NativeHadamardStoppedRootPorts.dimension_ne_source
  have exponentPort := NativeHadamardStoppedRootPorts.source_update_retained inputBank
    (putWord (fun _ => blank) 0 (NativeZeroPaddingArray.word phaseArray)) 0 _ (NativeHadamardStoppedRootPorts.control_ne_source 1)
  refine ⟨execution,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro index
    simpa only [CompactNativeRoleHeaders.recordWidth,metadataPrecision,ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using phaseWidth index
  · exact NativeHadamardPhaseOriginal.grid_from_path stage precision baseline growthConstant live path baselineFits dependencyFits coefficients sourceWidth inputGrid
  · exact (NativeHadamardStoppedRootPorts.raw_source_update inputBank (putWord (fun _ => blank) 0 (NativeZeroPaddingArray.word phaseArray)) 0).trans rawHeaders
  · change (ready phaseBank).tape _ ((ready phaseBank).head _-1)=blank
    dsimp only [phaseBank,phased]
    rw [saved.1,saved.2]
    exact stackEmpty
  · exact NativeHadamardStoppedRootPorts.guard_source_update inputBank guardReady _ 0
  · exact ⟨dimension.1.trans dimensionReady.1,dimension.2.trans dimensionReady.2⟩
  · simp only [phased,SharedPlacementAlphabet.setTape,Function.update_self]
    constructor
    · trivial
    · rfl
  · exact ⟨current.1.trans liveReady.1,current.2.trans liveReady.2⟩
  · exact ⟨target.1.trans targetBlank.1,target.2.trans targetBlank.2⟩
  · exact exponentPort.2.trans exponentWord
  · exact exponentPort.1.trans exponentHead
  · exact NativeHadamardStoppedRootPorts.phased_clean stage metadataPrecision coefficients inputBank publicClean

end
end IntegerMultBounds.Machine.NativeHadamardStoppedInputPhase
