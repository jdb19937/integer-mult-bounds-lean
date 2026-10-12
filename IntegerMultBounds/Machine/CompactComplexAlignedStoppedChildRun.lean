module

public import IntegerMultBounds.Machine.CompactComplexAlignedSavedReturnPath
public import IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedInstalledResult
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedStoppedChildRun

/-! The actual classifier marker and complete stopped leaf branch execute on
the same prime-alphabet basis-aligned fixed table. Mapping and extension retain
the original halt state; every control join and decoded saved-PC pop is paid. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexAlignedStoppedChildRun
noncomputable section
open Networks
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactRecursiveDependencyBudget (Path)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Width Grid decoded)
open CompactComplexSourceReadyStoppedLeaf (publicTapes ready)
open CompactComplexSourceReadyWorkspace (bank leafTapes)
open CompactComplexSourceReadyOrientationInvariants (savedSlot oriented)
open CompactComplexSourceReadyOrientedControlsFrame (output)
open CompactComplexScheduledPCLayout (originalCount)
open CompactComplexCompletedLiveLower (schedule)
open CompactNativeRoleConjugatedPorts (encoding)
open CompactComplexActualCallFullAlignment (localTapes)
open CompactComplexNonleafRoleSourceReturn (base)
open CompactComplexNonleafRoleEntry (headerPlacement)
open RecursiveChildQuotientsConstant (bits)
open SharedPlacementAlphabet (setTape)
variable {stackCount basisStateCount : ℕ}
local notation "roleCount" => CompactComplexSourceReadyScalarWorkspace.roles
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites schedule
  CompactComplexRolePhaseSite.roleCount CompactComplexSourceReadyDirection.width
  CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth
  CompactComplexSourceReadyStoppedLeafDispatchBudget.constant
  CompactComplexFixedNodeTable.returnDestination CompactComplexFixedNodeTable.eventDestination
open CompactComplexFixedNodeTable

namespace Marker
private theorem endpoint {Value : Type*} (predicate : Value → Prop) {sourceValue targetValue : Value}
    (sourceHolds : predicate sourceValue) (endpointEquality : sourceValue=targetValue) : predicate targetValue := endpointEquality ▸ sourceHolds

private theorem family_block {tapeCount alphabetSize returnCount extraCount addressBits : ℕ} (stack : Fin tapeCount)
    (stateCounts : Fin (returnCount+extraCount) → ℕ) (programBlocks : ∀ programCounter,Program tapeCount (stateCounts programCounter) alphabetSize) (programCounter : Fin (returnCount+extraCount)) :
    (⟨GuardedFiniteReturnExtraFlow.states (k:=addressBits) stateCounts programCounter.succ.succ,
      GuardedFiniteReturnExtraFlow.family (k:=addressBits) stack stateCounts programBlocks programCounter.succ.succ⟩ : Σ stateCount,Program tapeCount stateCount alphabetSize)=
      ⟨stateCounts programCounter,programBlocks programCounter⟩ := by
  simp [GuardedFiniteReturnExtraFlow.family,GuardedFiniteReturnExtraFlow.states,
    Fin.cases,Fin.induction,Fin.induction.go]

private theorem sigma_run {tapeCount alphabetSize : ℕ} {sourceProgram targetProgram : Σ stateCount,Program tapeCount stateCount alphabetSize} (programEquality : sourceProgram=targetProgram)
    (inputBank : Tapes tapeCount alphabetSize) (elapsedSteps : ℕ) (haltedConfiguration : Config tapeCount targetProgram.1 alphabetSize)
    (runSucceeded : run targetProgram.2 elapsedSteps (inputBank.start targetProgram.2)=some haltedConfiguration) :
    run sourceProgram.2 elapsedSteps (inputBank.start sourceProgram.2)=some (haltedConfiguration.mapState (Fin.cast (congrArg Sigma.fst programEquality).symm)) := by
  cases programEquality
  simpa only [Fin.cast_refl,Config.mapState,id_eq] using runSucceeded

private theorem sigma_halt {tapeCount alphabetSize : ℕ} {sourceProgram targetProgram : Σ stateCount,Program tapeCount stateCount alphabetSize} (programEquality : sourceProgram=targetProgram)
    (haltedConfiguration : Config tapeCount targetProgram.1 alphabetSize) (halted : step targetProgram.2 haltedConfiguration=none) :
    step sourceProgram.2 (haltedConfiguration.mapState (Fin.cast (congrArg Sigma.fst programEquality).symm))=none := by
  cases programEquality
  simpa only [Fin.cast_refl,Config.mapState,id_eq] using halted

private theorem next_block {returnCount extraCount addressBits : ℕ} (addressCapacity : returnCount≤2^addressBits)
    (stateCounts : Fin (returnCount+extraCount) → ℕ)
    (machineEdges : ∀ programCounter,Fin (stateCounts programCounter) → Option (Fin (returnCount+extraCount+2))) (programCounter : Fin (returnCount+extraCount)) :
    (⟨GuardedFiniteReturnExtraFlow.states (k:=addressBits) stateCounts programCounter.succ.succ,
      GuardedFiniteReturnExtraFlow.next addressCapacity stateCounts machineEdges programCounter.succ.succ⟩ :
        Σ stateCount,Fin stateCount → Option (Fin (returnCount+extraCount+2)))=⟨stateCounts programCounter,machineEdges programCounter⟩ := by
  simp [GuardedFiniteReturnExtraFlow.next,GuardedFiniteReturnExtraFlow.states,
    Fin.cases,Fin.induction,Fin.induction.go]

private theorem sigma_apply {programCounterCount : ℕ}
    {sourceProgram targetProgram : Σ stateCount,Fin stateCount → Option (Fin programCounterCount)} (programEquality : sourceProgram=targetProgram) (haltState : Fin targetProgram.1) :
    sourceProgram.2 (Fin.cast (congrArg Sigma.fst programEquality).symm haltState)=targetProgram.2 haltState := by
  cases programEquality
  rfl

private theorem sigma_mpr {sourceStateCount targetStateCount programCounterCount : ℕ}
    (programEquality : (Fin sourceStateCount → Option (Fin programCounterCount))=(Fin targetStateCount → Option (Fin programCounterCount))) (stateCountEquality : sourceStateCount=targetStateCount)
    (edgeFunction : Fin targetStateCount → Option (Fin programCounterCount)) :
    (⟨sourceStateCount,Eq.mpr programEquality edgeFunction⟩ : Σ stateCount,Fin stateCount → Option (Fin programCounterCount))=⟨targetStateCount,edgeFunction⟩ := by
  subst targetStateCount
  have castProofIdentity : programEquality=rfl := Subsingleton.elim _ _
  cases castProofIdentity
  rfl

private theorem edge_control_block {tapeCount alphabetSize returnCount length : ℕ}
    (returnPrograms : Fin returnCount → Σ stateCount,Program tapeCount stateCount alphabetSize)
    (controlPrograms : Fin 4 → Σ stateCount,Program tapeCount stateCount alphabetSize) (eventPrograms : Fin length → Σ stateCount,Program tapeCount stateCount alphabetSize)
    (returnEdges : ∀ programCounter,Fin (returnPrograms programCounter).1 → Option (Fin (returnCount+(4+length)+2)))
    (controlEdges : ∀ programCounter,Fin (controlPrograms programCounter).1 → Option (Fin (returnCount+(4+length)+2)))
    (eventEdges : ∀ programCounter,Fin (eventPrograms programCounter).1 → Option (Fin (returnCount+(4+length)+2))) (tag : Fin 4) :
    (⟨(tableProgramsWith returnPrograms controlPrograms eventPrograms (Fin.natAdd returnCount (Fin.castAdd length tag))).1,
      tableEdgesWith returnPrograms controlPrograms eventPrograms returnEdges controlEdges eventEdges (Fin.natAdd returnCount (Fin.castAdd length tag))⟩ :
        Σ stateCount,Fin stateCount → Option (Fin (returnCount+(4+length)+2)))=⟨(controlPrograms tag).1,controlEdges tag⟩ := by
  simp only [tableEdgesWith,Fin.addCases_right,Fin.addCases_left]
  generalize_proofs programEquality
  exact sigma_mpr programEquality (by simp only [tableProgramsWith,Fin.addCases_right,Fin.addCases_left]) _


private theorem halted_path {tapeCount alphabetSize returnCount length addressBits : ℕ} (addressCapacity : returnCount≤2^addressBits) (stack : Fin tapeCount)
    (returnPrograms : Fin returnCount → Σ stateCount,Program tapeCount stateCount alphabetSize) (controlPrograms : Fin 4 → Σ stateCount,Program tapeCount stateCount alphabetSize)
    (eventPrograms : Fin length → Σ stateCount,Program tapeCount stateCount alphabetSize)
    (returnEdges : ∀ programCounter,Fin (returnPrograms programCounter).1 → Option (Fin (returnCount+(4+length)+2)))
    (eventEdges : ∀ programCounter,Fin (eventPrograms programCounter).1 → Option (Fin (returnCount+(4+length)+2)))
    (classifier : Fin (controlPrograms 0).1 → Bool) (inputBank : Tapes tapeCount alphabetSize) (elapsedSteps : ℕ)
    (haltedConfiguration : Config tapeCount (controlPrograms 0).1 alphabetSize) (runSucceeded : run (controlPrograms 0).2 elapsedSteps (inputBank.start (controlPrograms 0).2)=some haltedConfiguration)
    (halted : step (controlPrograms 0).2 haltedConfiguration=none) (outcome : Bool) (classifierOutcome : classifier haltedConfiguration.state=outcome) :
    FiniteFlowPath.Path
      (GuardedFiniteReturnExtraFlow.family (k:=addressBits) stack
        (fun programCounter => (tableProgramsWith returnPrograms controlPrograms eventPrograms programCounter).1)
        (fun programCounter => (tableProgramsWith returnPrograms controlPrograms eventPrograms programCounter).2))
      (GuardedFiniteReturnExtraFlow.next addressCapacity
        (fun programCounter => (tableProgramsWith returnPrograms controlPrograms eventPrograms programCounter).1)
        (tableEdgesWith returnPrograms controlPrograms eventPrograms returnEdges (controlEdgesWith controlPrograms classifier) eventEdges))
      (controlPCFor returnCount length 0) inputBank (elapsedSteps+1)
      (controlPCFor returnCount length (if outcome then 1 else 2)) haltedConfiguration.tapes := by
  let programCounter : Fin (returnCount+(4+length)) := Fin.natAdd returnCount (Fin.castAdd length (0 : Fin 4))
  let scheduledPrograms := tableProgramsWith returnPrograms controlPrograms eventPrograms
  let machineStateCounts := fun programCounter => (scheduledPrograms programCounter).1
  let programBlocks := fun programCounter => (scheduledPrograms programCounter).2
  let machineEdges := tableEdgesWith returnPrograms controlPrograms eventPrograms returnEdges (controlEdgesWith controlPrograms classifier) eventEdges
  let machineFamily := GuardedFiniteReturnExtraFlow.family (k:=addressBits) stack machineStateCounts programBlocks
  let machineNext := GuardedFiniteReturnExtraFlow.next addressCapacity machineStateCounts machineEdges
  have blockIdentity : (⟨GuardedFiniteReturnExtraFlow.states (k:=addressBits) machineStateCounts programCounter.succ.succ,
      machineFamily programCounter.succ.succ⟩ : Σ stateCount,Program tapeCount stateCount alphabetSize)=controlPrograms 0 := by
    rw [show (⟨GuardedFiniteReturnExtraFlow.states (k:=addressBits) machineStateCounts programCounter.succ.succ,
      machineFamily programCounter.succ.succ⟩ : Σ stateCount,Program tapeCount stateCount alphabetSize)=⟨machineStateCounts programCounter,programBlocks programCounter⟩ from family_block stack machineStateCounts programBlocks programCounter]
    change tableProgramsWith returnPrograms controlPrograms eventPrograms programCounter=controlPrograms 0
    simp only [tableProgramsWith,programCounter,Fin.addCases_right,Fin.addCases_left]
  let castConfiguration := haltedConfiguration.mapState (Fin.cast (congrArg Sigma.fst blockIdentity).symm)
  have castRunSucceeded := sigma_run blockIdentity inputBank elapsedSteps haltedConfiguration runSucceeded
  have castHalted := sigma_halt blockIdentity haltedConfiguration halted
  have nextIdentity : (⟨GuardedFiniteReturnExtraFlow.states (k:=addressBits) machineStateCounts programCounter.succ.succ,
      machineNext programCounter.succ.succ⟩ : Σ stateCount,Fin stateCount → Option (Fin (returnCount+(4+length)+2)))=
      ⟨(controlPrograms 0).1,fun haltState => some (if classifier haltState then controlPCFor returnCount length 1 else controlPCFor returnCount length 2)⟩ := by
    exact (next_block addressCapacity machineStateCounts machineEdges programCounter).trans
      (edge_control_block returnPrograms controlPrograms eventPrograms returnEdges (controlEdgesWith controlPrograms classifier) eventEdges 0)
  have edgeIdentity : machineNext programCounter.succ.succ castConfiguration.state=some (controlPCFor returnCount length (if outcome then 1 else 2)) := by
    have evaluatedEdge := sigma_apply nextIdentity haltedConfiguration.state
    change machineNext programCounter.succ.succ castConfiguration.state=some
      (if classifier haltedConfiguration.state then controlPCFor returnCount length 1 else controlPCFor returnCount length 2) at evaluatedEdge
    rw [classifierOutcome] at evaluatedEdge
    cases outcome <;> exact evaluatedEdge
  exact FiniteFlowPath.block_path (family:=machineFamily) (next:=machineNext) programCounter.succ.succ _ inputBank elapsedSteps castConfiguration castRunSucceeded castHalted edgeIdentity
private theorem canonical_path {tapeCount alphabetSize : ℕ} (tapesPositive : 0<tapeCount) (stack : Fin tapeCount)
    (childReturns : ComplexRecursiveCallSchema.Call → Σ stateCount,Program tapeCount stateCount alphabetSize)
    (controlPrograms : Fin 4 → Σ stateCount,Program tapeCount stateCount alphabetSize)
    (eventPrograms : CompactComplexCompletedLiveLower.Event → Σ stateCount,Program tapeCount stateCount alphabetSize)
    (classifier : Fin (controlPrograms 0).1 → Bool) (inputBank : Tapes tapeCount alphabetSize) (elapsedSteps : ℕ)
    (haltedConfiguration : Config tapeCount (controlPrograms 0).1 alphabetSize)
    (runSucceeded : run (controlPrograms 0).2 elapsedSteps (inputBank.start (controlPrograms 0).2)=some haltedConfiguration)
    (halted : step (controlPrograms 0).2 haltedConfiguration=none) (outcome : Bool) (classifierOutcome : classifier haltedConfiguration.state=outcome) :
    CompactComplexFixedNodePaths.nodePath tapesPositive stack childReturns controlPrograms eventPrograms classifier
      (controlPCFor originalCount schedule.length 0) inputBank (elapsedSteps+1)
      (controlPCFor originalCount schedule.length (if outcome then 1 else 2)) haltedConfiguration.tapes := by
  exact halted_path (returnCount:=originalCount) (length:=schedule.length)
    (CompactComplexCallReturn.roomFor ComplexRecursiveCallSchema.sites.length (25^3)) stack
    (CompactComplexFixedNodeTable.returnPrograms tapesPositive childReturns) controlPrograms (fun tapeIndex => eventPrograms (schedule.get tapeIndex))
    (fun address _ => returnDestination address) (fun tapeIndex _ => eventDestination tapeIndex)
    classifier inputBank elapsedSteps haltedConfiguration runSucceeded halted outcome classifierOutcome
end Marker

/-- The old classifier halt marker is preserved exactly by alphabet mapping
and the appended basis workspace, including its final finite state. -/
private theorem lift_marker {controlStateCount elapsedSteps : ℕ}
    (controlProgram : Program (CompactComplexSourceReadyScalarWorkspace.tapes stackCount roleCount) controlStateCount 2)
    (inputBank : Tapes (CompactComplexSourceReadyScalarWorkspace.tapes stackCount roleCount) 2)
    (suffix : Tapes (localTapes roleCount) prime)
    (haltedConfiguration : Config (CompactComplexSourceReadyScalarWorkspace.tapes stackCount roleCount) controlStateCount 2)
    (runSucceeded : run controlProgram elapsedSteps (inputBank.start controlProgram)=some haltedConfiguration) (halted : step controlProgram haltedConfiguration=none) :
    run (CompactComplexSourceReadyAlignedActualTable.liftPair ⟨controlStateCount,controlProgram⟩).2 elapsedSteps
      (((Alphabet.mapTapes encoding inputBank).append suffix).start
        (CompactComplexSourceReadyAlignedActualTable.liftPair ⟨controlStateCount,controlProgram⟩).2)=
      some ((Alphabet.mapConfig encoding haltedConfiguration).extend suffix) ∧
    step (CompactComplexSourceReadyAlignedActualTable.liftPair ⟨controlStateCount,controlProgram⟩).2
      ((Alphabet.mapConfig encoding haltedConfiguration).extend suffix)=none := by
  exact ⟨extend_run (Alphabet.program encoding controlProgram) suffix (Alphabet.map_success encoding controlProgram runSucceeded),
    extend_halt (Alphabet.program encoding controlProgram) suffix ((Alphabet.map_halt_iff encoding controlProgram haltedConfiguration).mpr halted)⟩

theorem classifier_path {shape : Shape} {rows polynomialExponent payloadPrecision childLeft nodeExponent levels frames returned : ℕ}
    (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (headerStack pcStack liveStack : Fin stackCount) (call : ComplexRecursiveCallSchema.Call)
    (inputBank : Tapes (publicTapes stackCount roleCount) 2) (leaf : Tapes leafTapes 2) (work : Tapes 10 2)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (suffix : Tapes (localTapes roleCount) prime)
    (olderWord : ℤ → Fin 6) (stackOrigin : ℤ)
    (savedStackReady : Placement.active (FiniteReturnStackAt.placement (savedSlot pcStack)) (bank inputBank leaf work)=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart olderWord stackOrigin (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (stackOrigin+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)))
    (dependency : CompactRecursiveDependencyBudget.Path shape.active childLeft nodeExponent levels frames returned)
    (precision growthConstant liveDenominator : ℕ) (metadataFits : precision≤payloadPrecision) (dependencyFitsChunk : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant≤shape.chunk)
    (rowsPositive : 0<rows) (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes) (activeFitsAxes : shape.active≤shape.axes)
    (sourceArray : Array shape rows polynomialExponent) (sourceWidth : CompactSpectatorInheritedGrid.Width shape rows polynomialExponent payloadPrecision sourceArray)
    (sourceGrid : CompactSpectatorInheritedGrid.Grid shape rows polynomialExponent payloadPrecision liveDenominator
      (CompactRecursiveGridBudget.bound precision growthConstant levels (frames+2*returned)) sourceArray)
    (sourceReady : inputBank.tape CompactComplexSourceReadyOrientedControlsFrame.source=
      NativeZeroPadding.word (NativeZeroPaddingArray.word sourceArray))
    (sourceHeadReady : inputBank.head CompactComplexSourceReadyOrientedControlsFrame.source=0)
    (guardReady : CompactComplexSourceReadyGuard.Ready inputBank)
    (dimensionReady : inputBank.head CompactComplexSourceReadyGuard.dimension=1 ∧
      inputBank.tape CompactComplexSourceReadyGuard.dimension=RadixZeroFill.encodedBinary (bits shape.axes))
    (exponentReady : inputBank.head CompactComplexSourceReadyGuard.exponent=1 ∧
      inputBank.tape CompactComplexSourceReadyGuard.exponent=RadixZeroFill.encodedBinary (bits nodeExponent)) :
    ∃ elapsedSteps≤(CompactComplexSourceReadyOrientationInvariants.constant+
        4*CompactComplexSourceReadyGuard.guardConstant+1)*
        CompactNativeRoleTransferBudget.volume rows shape polynomialExponent (ButterflyIndependentGuardHeaders.reservation shape.bits payloadPrecision)+1,CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
      (controlPCFor originalCount schedule.length 0) ((Alphabet.mapTapes encoding ((bank inputBank leaf work).append scalar)).append suffix) elapsedSteps
      (controlPCFor originalCount schedule.length (if ComplexRecursiveCallSchema.stopped shape.axes nodeExponent then 1 else 2)) ((Alphabet.mapTapes encoding ((bank (CompactComplexSourceReadyOrientedControlsFrame.output call inputBank sourceArray) leaf work).append scalar)).append suffix) := by
  obtain ⟨elapsedSteps,classifierTimeBound,haltedConfiguration,classifierRunSucceeded,classifierHalted,classifierEndpoint,classifierOutcome⟩ := CompactComplexSourceReadyOrientedControlsEntry.runs_from_path
    pcStack call inputBank leaf work scalar olderWord stackOrigin savedStackReady dependency precision growthConstant liveDenominator metadataFits dependencyFitsChunk rowsPositive guardPositive axesPositive activeFitsAxes sourceArray sourceWidth sourceGrid sourceReady sourceHeadReady guardReady dimensionReady exponentReady
  obtain ⟨mappedRunSucceeded,mappedHalted⟩ := lift_marker
    (CompactComplexSourceReadyOrientedControls.entry pcStack).2 ((bank inputBank leaf work).append scalar)
    suffix haltedConfiguration classifierRunSucceeded classifierHalted
  have classifierPath := Marker.canonical_path
    (Nat.zero_lt_of_lt (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack).isLt)
    (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack)
    (CompactComplexActualCallFullAlignment.childReturn basisProgram headerStack liveStack)
    (CompactComplexSourceReadyAlignedActualTable.controls pcStack)
    (CompactComplexSourceReadyAlignedActualTable.event basisProgram headerStack pcStack liveStack)
    (CompactComplexSourceReadyAlignedActualTable.classify pcStack)
    ((Alphabet.mapTapes encoding ((bank inputBank leaf work).append scalar)).append suffix) elapsedSteps
    ((Alphabet.mapConfig encoding haltedConfiguration).extend suffix) mappedRunSucceeded mappedHalted
    (ComplexRecursiveCallSchema.stopped shape.axes nodeExponent) classifierOutcome
  refine ⟨elapsedSteps+1,Nat.add_le_add_right classifierTimeBound 1,?_⟩
  exact Marker.endpoint _ classifierPath
    (congrArg (fun candidateBank => (Alphabet.mapTapes encoding candidateBank).append suffix) classifierEndpoint)

theorem positive_path_installed (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (headerStack pcStack liveStack : Fin stackCount) (call : ComplexRecursiveCallSchema.Call)
    (shape : Shape) (rows polynomialExponent precision : ℕ) (chunkIndex : Fin shape.chunk)
    {childLeft childExponent levels frames count : ℕ} (dependency : Path shape.active childLeft (childExponent+1) levels frames count)
    (right sourceRole targetRole liveDenominator : ℕ) (inputBank : Tapes (publicTapes stackCount roleCount) 2)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (suffix : Tapes (localTapes roleCount) prime)
    (olderWord : ℤ → Fin 6) (stackOrigin : ℤ)
    (savedStackReady : Placement.active (FiniteReturnStackAt.placement (savedSlot pcStack)) (ready inputBank)=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart olderWord stackOrigin (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (stackOrigin+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)))
    (sourceArray : CompactSpectatorVisitGeometry.Array (NativePolynomialStageShape.shape shape polynomialExponent precision) rows polynomialExponent)
    (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes) (rowsPositive : 0<rows) (metadataFits : 2*shape.bits≤precision)
    (sourceWidth : ∀ tapeIndex,(sourceArray tapeIndex).1.length=CompactNativeRoleHeaders.recordWidth shape precision ∧
      (sourceArray tapeIndex).2.length=CompactNativeRoleHeaders.recordWidth shape precision)
    (rawHeaders : Placement.active headerPlacement (base inputBank)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw shape rows polynomialExponent precision chunkIndex.val childLeft (arity^childExponent) arity right sourceRole targetRole))
    (publicSourceReady : inputBank.head (CompactComplexSourceReadyLeafPhase.source (s:=10+stackCount))=0 ∧
      inputBank.tape (CompactComplexSourceReadyLeafPhase.source (s:=10+stackCount))=CompactSpectatorLeafAxis.word sourceArray)
    (liveReady : inputBank.head CompactComplexNonleafRoleChildBank.current=1 ∧
      inputBank.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (bits liveDenominator))
    (targetBlank : inputBank.head CompactComplexNonleafRoleChildBank.target=0 ∧
      inputBank.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank))
    (exponentWord : inputBank.tape (CompactComplexNonleafRoleChildBank.control 1)=RadixZeroFill.encodedBinary (bits (childExponent+1)))
    (exponentHead : inputBank.head (CompactComplexNonleafRoleChildBank.control 1)=1)
    (scalarRowLimit basePrecision usedRows : ℕ) (unitPayload : shape.payload=1)
    (rightFitsActive : right≤shape.active) (sourceRoleFits : sourceRole≤arity) (targetRoleFits : targetRole≤arity)
    (baselineFits : basePrecision≤precision-2*shape.bits) (rowsUsedBound : usedRows≤scalarRowLimit)
    (denominatorRoom : CompactComplexDenominatorCapacity.room scalarRowLimit≤shape.chunk)
    (liveLedgerBound : liveDenominator≤CompactComplexDenominatorCapacity.ledger scalarRowLimit basePrecision levels frames count usedRows) :
    let result := CompactSpectatorLeafGuardOriginal.result .forward shape
      rows polynomialExponent (precision-2*shape.bits) chunkIndex dependency.visit sourceArray
    ∃ elapsedSteps≤((CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+
        CompactComplexSourceReadyOrientationInvariants.constant+1)*
        CompactNativeRoleTransferBudget.volume rows shape polynomialExponent precision*(arity^(childExponent+1)))+1,CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
      (CompactComplexFixedNodeTable.controlPCFor originalCount schedule.length 1)
      ((Alphabet.mapTapes encoding ((ready inputBank).append scalar)).append suffix) elapsedSteps 0 ((Alphabet.mapTapes encoding ((ready (CompactComplexSourceReadyStoppedLeafCount.returned inputBank (CompactSpectatorLeafAxis.word (oriented call result))
        (CompactComplexDenominatorPolicy.leafTarget liveDenominator (childExponent+1)))).append scalar)).append suffix) := by
  dsimp only
  have localExecution := CompactComplexSourceReadyOrientedControlsStopped.positive_runs pcStack call shape rows polynomialExponent precision chunkIndex
    dependency right sourceRole targetRole liveDenominator inputBank scalar olderWord stackOrigin savedStackReady sourceArray guardPositive axesPositive rowsPositive metadataFits sourceWidth rawHeaders publicSourceReady
    liveReady targetBlank exponentWord exponentHead scalarRowLimit basePrecision usedRows unitPayload rightFitsActive sourceRoleFits targetRoleFits baselineFits rowsUsedBound denominatorRoom liveLedgerBound
  dsimp only at localExecution
  rw [CompactComplexSourceReadyStoppedInstalledResult.oriented_endpoint,
    CompactComplexSourceReadyStoppedInstalledResult.polynomial_leaf_result shape rows polynomialExponent precision chunkIndex dependency.visit sourceArray] at localExecution
  have liftedExecution := CompactComplexSourceReadyAlignedActualTable.lift_runs _ _ _ suffix localExecution
  exact CompactComplexFixedNodePaths.terminal_control_path
    (ht:=Nat.zero_lt_of_lt (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack).isLt)
    (stack:=CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack)
    (childReturn:=CompactComplexActualCallFullAlignment.childReturn basisProgram headerStack liveStack)
    (controls:=CompactComplexSourceReadyAlignedActualTable.controls pcStack)
    (event:=CompactComplexSourceReadyAlignedActualTable.event basisProgram headerStack pcStack liveStack)
    (isStopped:=CompactComplexSourceReadyAlignedActualTable.classify pcStack)
    1 (Or.inl rfl) _ _ _ liftedExecution


private theorem numeric_ne (tapeIndex : Fin 43) :
    Fin.castAdd 7 (CompactComplexNonleafRoleEntry.numeric (s:=10+stackCount) (c:=roleCount) tapeIndex)≠
      CompactComplexSourceReadyOrientedControlsFrame.source := by
  intro indexEquality
  have indexValues := congrArg Fin.val indexEquality
  have outsideNumeric := tapeIndex.isLt
  simp only [CompactComplexSourceReadyOrientedControlsFrame.source,
    CompactComplexNonleafRoleEntry.source,CompactComplexNonleafRoleEntry.numeric,
    CompactComplexSpectatorTargetBank.numericSlot,CompactComplexNativeCodecFrame.headerSlot,
    CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at indexValues
  omega

private theorem control_ne (tapeIndex : Fin 43) :
    CompactComplexNonleafRoleChildBank.control (s:=stackCount) (c:=roleCount) tapeIndex≠
      CompactComplexSourceReadyOrientedControlsFrame.source := by
  intro indexEquality
  have indexValues := congrArg Fin.val indexEquality
  have outsideNumeric := tapeIndex.isLt
  simp only [CompactComplexSourceReadyOrientedControlsFrame.source,
    CompactComplexNonleafRoleEntry.source,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.nativeSlot,CompactComplexNonleafRoleChildBank.control,
    Fin.val_mk,Fin.val_castAdd,Fin.val_natAdd] at indexValues
  omega

private theorem storage_ne (tapeIndex : Fin (10+stackCount)) :
    CompactComplexNonleafRoleChildBank.storage (c:=roleCount) tapeIndex≠
      CompactComplexSourceReadyOrientedControlsFrame.source := by
  intro indexEquality
  have indexValues := congrArg Fin.val indexEquality
  simp only [CompactComplexSourceReadyOrientedControlsFrame.source,
    CompactComplexNonleafRoleEntry.source,CompactComplexNonleafRoleChildBank.storage,
    CompactComplexSpectatorTargetBank.oldSlot,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.nativeSlot,CompactComplexControllerNativeFrame.storageSlot,
    Fin.val_castAdd,Fin.val_natAdd] at indexValues
  omega

private theorem output_headers {coefficientCount : ℕ} (call : ComplexRecursiveCallSchema.Call)
    (inputBank : Tapes (publicTapes stackCount roleCount) 2) (sourceArray : Fin coefficientCount → ButterflyStreamData.Coefficient) :
    Placement.active headerPlacement (base (output call inputBank sourceArray))=
      Placement.active headerPlacement (base inputBank) := by
  have headerSlotIdentity (tapeIndex : Fin 43) : headerPlacement (s:=10+stackCount) (c:=roleCount)
      (Fin.castAdd (CompactComplexNonleafRoleEntry.tapes (10+stackCount) roleCount-43) tapeIndex)=
      CompactComplexNonleafRoleEntry.numeric tapeIndex := by
    unfold headerPlacement
    exact InjectivePlacement.active_slot _ _ _ _
  apply congrArg₂ Tapes.mk <;> funext tapeIndex
  · change (output call inputBank sourceArray).head (Fin.castAdd 7 (headerPlacement (Fin.castAdd _ tapeIndex)))=_
    rw [headerSlotIdentity]
    exact (CompactComplexSourceReadyOrientedControlsFrame.frame call inputBank sourceArray _ (numeric_ne tapeIndex)).1
  · change (output call inputBank sourceArray).tape (Fin.castAdd 7 (headerPlacement (Fin.castAdd _ tapeIndex)))=_
    rw [headerSlotIdentity]
    exact (CompactComplexSourceReadyOrientedControlsFrame.frame call inputBank sourceArray _ (numeric_ne tapeIndex)).2

private theorem ready_output {coefficientCount : ℕ} (call : ComplexRecursiveCallSchema.Call)
    (inputBank : Tapes (publicTapes stackCount roleCount) 2) (sourceArray : Fin coefficientCount → ButterflyStreamData.Coefficient) :
    CompactComplexSourceReadyOrientation.output call (ready inputBank) sourceArray=ready (output call inputBank sourceArray) := by
  simpa only [ready,CompactComplexSourceReadyLeafPhase.ready,CompactComplexSourceReadyWorkspace.bank]
    using CompactComplexSourceReadyOrientedControlsFrame.node_output call inputBank
      (SharedBank.empty _ 2) (SharedBank.empty _ 2) sourceArray

theorem stopped_child_return (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (headerStack pcStack liveStack : Fin stackCount) (call : ComplexRecursiveCallSchema.Call)
    (shape : Shape) (rows polynomialExponent precision : ℕ) (chunkIndex : Fin shape.chunk)
    {childLeft childExponent levels frames count : ℕ} (dependency : Path shape.active childLeft (childExponent+1) levels frames count)
    (right sourceRole targetRole liveDenominator : ℕ) (inputBank : Tapes (publicTapes stackCount roleCount) 2)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (suffix : Tapes (localTapes roleCount) prime)
    (stackOrigin : ℤ) (calls : List ComplexRecursiveCallSchema.Call)
    (reachedAssociation : CompactComplexSourceReadySavedCallHistory.Reached pcStack stackOrigin (call::calls)
      ((ready inputBank).append scalar))
    (sourceArray : Array shape rows polynomialExponent)
    (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes) (rowsPositive : 0<rows) (metadataFits : 2*shape.bits≤precision)
    (sourceWidth : Width shape rows polynomialExponent (precision-2*shape.bits) sourceArray)
    (basePrecision growthConstant : ℕ) (dependencyFitsChunk : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant≤shape.chunk)
    (sourceGrid : Grid shape rows polynomialExponent (precision-2*shape.bits) liveDenominator
      (CompactRecursiveGridBudget.bound basePrecision growthConstant levels (frames+2*count)) sourceArray)
    (rawHeaders : Placement.active headerPlacement (base inputBank)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw shape rows polynomialExponent precision chunkIndex.val childLeft (arity^childExponent) arity right sourceRole targetRole))
    (publicSourceReady : inputBank.head (CompactComplexSourceReadyLeafPhase.source (s:=10+stackCount))=0 ∧
      inputBank.tape (CompactComplexSourceReadyLeafPhase.source (s:=10+stackCount))=CompactSpectatorLeafAxis.word sourceArray)
    (liveReady : inputBank.head CompactComplexNonleafRoleChildBank.current=1 ∧
      inputBank.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (bits liveDenominator))
    (targetBlank : inputBank.head CompactComplexNonleafRoleChildBank.target=0 ∧
      inputBank.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank))
    (exponentWord : inputBank.tape (CompactComplexNonleafRoleChildBank.control 1)=RadixZeroFill.encodedBinary (bits (childExponent+1)))
    (exponentHead : inputBank.head (CompactComplexNonleafRoleChildBank.control 1)=1)
    (scalarRowLimit usedRows : ℕ) (unitPayload : shape.payload=1)
    (rightFitsActive : right≤shape.active) (sourceRoleFits : sourceRole≤arity) (targetRoleFits : targetRole≤arity)
    (baselineFits : basePrecision≤precision-2*shape.bits) (rowsUsedBound : usedRows≤scalarRowLimit)
    (denominatorRoom : CompactComplexDenominatorCapacity.room scalarRowLimit≤shape.chunk)
    (liveLedgerBound : liveDenominator≤CompactComplexDenominatorCapacity.ledger scalarRowLimit basePrecision levels frames count usedRows)
    (activeFitsAxes : shape.active≤shape.axes)
    (guardReady : CompactComplexSourceReadyGuard.Ready inputBank)
    (dimensionReady : inputBank.head CompactComplexSourceReadyGuard.dimension=1 ∧
      inputBank.tape CompactComplexSourceReadyGuard.dimension=RadixZeroFill.encodedBinary (bits shape.axes))
    (childStopped : ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=true) :
    let orientedInput := output call inputBank sourceArray
    let installedChild := CompactComplexCorrectedStoppedChildGridSemantics.installed call rows polynomialExponent
      (precision-2*shape.bits) chunkIndex dependency.visit (oriented call sourceArray)
    let completedBank := CompactComplexSourceReadyStoppedLeafCount.returned orientedInput
      (CompactSpectatorLeafAxis.word installedChild) (CompactComplexDenominatorPolicy.leafTarget liveDenominator (childExponent+1))
    ∃ olderWord olderHead,
      CompactComplexSourceReadySavedCallHistory.Associated stackOrigin calls olderWord olderHead ∧
      ∃ elapsedSteps≤(CompactComplexSourceReadyOrientationInvariants.constant+
        4*CompactComplexSourceReadyGuard.guardConstant+1)*
        CompactNativeRoleTransferBudget.volume rows shape polynomialExponent precision+1+
        (((CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+
          CompactComplexSourceReadyOrientationInvariants.constant+1)*
          CompactNativeRoleTransferBudget.volume rows shape polynomialExponent precision*(arity^(childExponent+1)))+1+
          (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)+5)),
        CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
          (controlPCFor originalCount schedule.length 0)
          ((Alphabet.mapTapes encoding ((ready inputBank).append scalar)).append suffix) elapsedSteps
          (CompactComplexScheduledPCDecode.savedPC call)
          ((Alphabet.mapTapes encoding ((ready (setTape completedBank
            (CompactComplexSourceReadyCorrectedSavedReturnPath.publicSaved pcStack) olderWord olderHead)).append scalar)).append suffix) := by
  dsimp only
  have initialSavedPorts := CompactComplexSourceReadyCorrectedSavedReturnPath.ready_saved pcStack inputBank scalar
  have publicAssociation := reachedAssociation
  unfold CompactComplexSourceReadySavedCallHistory.Reached at publicAssociation
  rw [initialSavedPorts.1,initialSavedPorts.2] at publicAssociation
  obtain ⟨initialOlderWord,initialHead,olderAssociation,_,initialSavedWord,initialSavedHead⟩ := CompactComplexSourceReadySavedCallHistory.top publicAssociation
  have savedStackReady : Placement.active (FiniteReturnStackAt.placement (savedSlot pcStack)) (ready inputBank)=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart initialOlderWord initialHead (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (initialHead+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) := by
    rw [FiniteReturnStackAt.active_bank]
    simp only [ready,CompactComplexSourceReadyLeafPhase.ready,savedSlot,Tapes.append,Fin.addCases_left]
    exact congrArg₂ FiniteReturnStack.bank initialSavedWord initialSavedHead
  let orientedInput := output call inputBank sourceArray
  let installedChild := CompactComplexCorrectedStoppedChildGridSemantics.installed call rows polynomialExponent
    (precision-2*shape.bits) chunkIndex dependency.visit (oriented call sourceArray)
  let completedBank := CompactComplexSourceReadyStoppedLeafCount.returned orientedInput
    (CompactSpectatorLeafAxis.word installedChild) (CompactComplexDenominatorPolicy.leafTarget liveDenominator (childExponent+1))
  have sourceReady := CompactComplexCorrectedStoppedClassifierTensor.classifier_source call inputBank sourceArray publicSourceReady.2 publicSourceReady.1
  have orientationRetainsSavedStack := CompactComplexSourceReadyOrientationInvariants.retained_savedSlot pcStack call (ready inputBank) sourceArray
  rw [ready_output] at orientationRetainsSavedStack
  have orientedSavedStackReady : Placement.active (FiniteReturnStackAt.placement (savedSlot pcStack)) (ready orientedInput)=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart initialOlderWord initialHead (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (initialHead+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) :=
    orientationRetainsSavedStack.trans savedStackReady
  have physicalWidthIdentity : CompactNativeRoleHeaders.recordWidth shape precision=
      ButterflyGuard.width (ButterflyIndependentGuardHeaders.reservation shape.bits (precision-2*shape.bits)) shape.bits := by
    unfold CompactNativeRoleHeaders.recordWidth ButterflyGuard.width ButterflyGuard.halfWidth
      ButterflyIndependentGuardHeaders.reservation
    omega
  have orientedWidth := CompactComplexSourceReadyOrientationInvariants.oriented_width call shape rows polynomialExponent (precision-2*shape.bits) sourceArray sourceWidth
  have physicalWidth : ∀ tapeIndex,((oriented call sourceArray) tapeIndex).1.length=CompactNativeRoleHeaders.recordWidth shape precision ∧
      ((oriented call sourceArray) tapeIndex).2.length=CompactNativeRoleHeaders.recordWidth shape precision := by
    intro tapeIndex
    rw [physicalWidthIdentity]
    exact orientedWidth tapeIndex
  have orientedHeaders := (output_headers call inputBank sourceArray).trans rawHeaders
  have orientationRetainsLive := CompactComplexSourceReadyOrientedControlsFrame.frame call inputBank sourceArray
    CompactComplexNonleafRoleChildBank.current (storage_ne _)
  have orientationRetainsTarget := CompactComplexSourceReadyOrientedControlsFrame.frame call inputBank sourceArray
    CompactComplexNonleafRoleChildBank.target (storage_ne _)
  have orientationRetainsExponent := CompactComplexSourceReadyOrientedControlsFrame.frame call inputBank sourceArray
    (CompactComplexNonleafRoleChildBank.control 1) (control_ne 1)
  obtain ⟨classifierSteps,classifierTimeBound,classifiedPath⟩ := classifier_path basisProgram headerStack pcStack liveStack call inputBank
    (SharedBank.empty _ 2) (SharedBank.empty _ 2) scalar suffix initialOlderWord initialHead savedStackReady
    dependency basePrecision growthConstant liveDenominator baselineFits dependencyFitsChunk rowsPositive guardPositive axesPositive activeFitsAxes sourceArray sourceWidth sourceGrid
    publicSourceReady.2 publicSourceReady.1 guardReady dimensionReady ⟨exponentHead,exponentWord⟩
  have reservationEqualsPrecision : ButterflyIndependentGuardHeaders.reservation shape.bits (precision-2*shape.bits)=precision := by
    unfold ButterflyIndependentGuardHeaders.reservation
    omega
  rw [reservationEqualsPrecision] at classifierTimeBound
  rw [childStopped,ite_eq_left rfl] at classifiedPath
  obtain ⟨leafSteps,leafTimeBound,leafPath⟩ := positive_path_installed basisProgram headerStack pcStack liveStack call shape rows polynomialExponent precision chunkIndex
    dependency right sourceRole targetRole liveDenominator orientedInput scalar suffix initialOlderWord initialHead orientedSavedStackReady (oriented call sourceArray)
    guardPositive axesPositive rowsPositive metadataFits physicalWidth orientedHeaders sourceReady
    ⟨orientationRetainsLive.1.trans liveReady.1,orientationRetainsLive.2.trans liveReady.2⟩
    ⟨orientationRetainsTarget.1.trans targetBlank.1,orientationRetainsTarget.2.trans targetBlank.2⟩
    (orientationRetainsExponent.2.trans exponentWord) (orientationRetainsExponent.1.trans exponentHead)
    scalarRowLimit basePrecision usedRows unitPayload rightFitsActive sourceRoleFits targetRoleFits baselineFits rowsUsedBound denominatorRoom liveLedgerBound
  have completedSavedStack := (CompactComplexSourceReadyOrientedControlsStopped.returned_saved pcStack orientedInput
    (CompactSpectatorLeafAxis.word installedChild) (CompactComplexDenominatorPolicy.leafTarget liveDenominator (childExponent+1))).trans orientedSavedStackReady
  have completedSavedHead := congrArg (fun bankView : Tapes 1 2 => bankView.head 0) completedSavedStack
  have completedSavedWord := congrArg (fun bankView : Tapes 1 2 => bankView.tape 0) completedSavedStack
  rw [FiniteReturnStackAt.active_bank] at completedSavedHead completedSavedWord
  have completedHeadIdentity : completedBank.head (CompactComplexSourceReadyCorrectedSavedReturnPath.publicSaved pcStack)=
      initialHead+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3) := by
    simpa only [ready,CompactComplexSourceReadyLeafPhase.ready,savedSlot,Tapes.append,
      Fin.addCases_left,FiniteReturnStack.bank,CompactComplexSourceReadyCorrectedSavedReturnPath.publicSaved] using completedSavedHead
  have completedWordIdentity : completedBank.tape (CompactComplexSourceReadyCorrectedSavedReturnPath.publicSaved pcStack)=
      FiniteReturnStack.wordPart initialOlderWord initialHead (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl := by
    simpa only [ready,CompactComplexSourceReadyLeafPhase.ready,savedSlot,Tapes.append,
      Fin.addCases_left,FiniteReturnStack.bank,CompactComplexSourceReadyCorrectedSavedReturnPath.publicSaved] using completedSavedWord
  have completedAssociation := CompactComplexSourceReadySavedCallHistory.Associated.push olderAssociation call
  rw [←completedWordIdentity,←completedHeadIdentity] at completedAssociation
  obtain ⟨olderWord,olderHead,restoredAssociation,popPath⟩ := CompactComplexAlignedSavedReturnPath.public_associated_return_path basisProgram
    headerStack pcStack liveStack call completedBank scalar suffix stackOrigin calls completedAssociation
  refine ⟨olderWord,olderHead,restoredAssociation,classifierSteps+(leafSteps+(CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)+5)),
    Nat.add_le_add classifierTimeBound (Nat.add_le_add_right leafTimeBound _),?_⟩
  exact FiniteFlowPath.append classifiedPath (FiniteFlowPath.append leafPath popPath)

theorem classifier_path_width {shape : Shape} {rows polynomialExponent payloadPrecision childLeft nodeExponent levels frames returned : ℕ}
    (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (headerStack pcStack liveStack : Fin stackCount) (call : ComplexRecursiveCallSchema.Call)
    (inputBank : Tapes (publicTapes stackCount roleCount) 2) (leaf : Tapes leafTapes 2) (work : Tapes 10 2)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (suffix : Tapes (localTapes roleCount) prime)
    (olderWord : ℤ → Fin 6) (stackOrigin : ℤ)
    (savedStackReady : Placement.active (FiniteReturnStackAt.placement (savedSlot pcStack)) (bank inputBank leaf work)=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart olderWord stackOrigin (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (stackOrigin+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)))
    (dependency : CompactRecursiveDependencyBudget.Path shape.active childLeft nodeExponent levels frames returned)
    (rowsPositive : 0<rows) (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes) (activeFitsAxes : shape.active≤shape.axes)
    (sourceArray : Array shape rows polynomialExponent) (sourceWidth : CompactSpectatorInheritedGrid.Width shape rows polynomialExponent payloadPrecision sourceArray)
    (sourceReady : inputBank.tape CompactComplexSourceReadyOrientedControlsFrame.source=
      NativeZeroPadding.word (NativeZeroPaddingArray.word sourceArray))
    (sourceHeadReady : inputBank.head CompactComplexSourceReadyOrientedControlsFrame.source=0)
    (guardReady : CompactComplexSourceReadyGuard.Ready inputBank)
    (dimensionReady : inputBank.head CompactComplexSourceReadyGuard.dimension=1 ∧
      inputBank.tape CompactComplexSourceReadyGuard.dimension=RadixZeroFill.encodedBinary (bits shape.axes))
    (exponentReady : inputBank.head CompactComplexSourceReadyGuard.exponent=1 ∧
      inputBank.tape CompactComplexSourceReadyGuard.exponent=RadixZeroFill.encodedBinary (bits nodeExponent)) :
    ∃ elapsedSteps≤(CompactComplexSourceReadyOrientationInvariants.constant+
        4*CompactComplexSourceReadyGuard.guardConstant+1)*
        CompactNativeRoleTransferBudget.volume rows shape polynomialExponent (ButterflyIndependentGuardHeaders.reservation shape.bits payloadPrecision)+1,CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
      (controlPCFor originalCount schedule.length 0) ((Alphabet.mapTapes encoding ((bank inputBank leaf work).append scalar)).append suffix) elapsedSteps
      (controlPCFor originalCount schedule.length (if ComplexRecursiveCallSchema.stopped shape.axes nodeExponent then 1 else 2)) ((Alphabet.mapTapes encoding ((bank (CompactComplexSourceReadyOrientedControlsFrame.output call inputBank sourceArray) leaf work).append scalar)).append suffix) := by
  obtain ⟨elapsedSteps,classifierTimeBound,haltedConfiguration,classifierRunSucceeded,classifierHalted,classifierEndpoint,classifierOutcome⟩ := CompactComplexSourceReadyOrientedControlsEntry.runs_width
    pcStack call inputBank leaf work scalar olderWord stackOrigin savedStackReady dependency rowsPositive guardPositive axesPositive activeFitsAxes sourceArray sourceWidth sourceReady sourceHeadReady guardReady dimensionReady exponentReady
  obtain ⟨mappedRunSucceeded,mappedHalted⟩ := lift_marker
    (CompactComplexSourceReadyOrientedControls.entry pcStack).2 ((bank inputBank leaf work).append scalar)
    suffix haltedConfiguration classifierRunSucceeded classifierHalted
  have classifierPath := Marker.canonical_path
    (Nat.zero_lt_of_lt (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack).isLt)
    (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack)
    (CompactComplexActualCallFullAlignment.childReturn basisProgram headerStack liveStack)
    (CompactComplexSourceReadyAlignedActualTable.controls pcStack)
    (CompactComplexSourceReadyAlignedActualTable.event basisProgram headerStack pcStack liveStack)
    (CompactComplexSourceReadyAlignedActualTable.classify pcStack)
    ((Alphabet.mapTapes encoding ((bank inputBank leaf work).append scalar)).append suffix) elapsedSteps
    ((Alphabet.mapConfig encoding haltedConfiguration).extend suffix) mappedRunSucceeded mappedHalted
    (ComplexRecursiveCallSchema.stopped shape.axes nodeExponent) classifierOutcome
  refine ⟨elapsedSteps+1,Nat.add_le_add_right classifierTimeBound 1,?_⟩
  exact Marker.endpoint _ classifierPath
    (congrArg (fun candidateBank => (Alphabet.mapTapes encoding candidateBank).append suffix) classifierEndpoint)

theorem stopped_child_return_width (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (headerStack pcStack liveStack : Fin stackCount) (call : ComplexRecursiveCallSchema.Call)
    (shape : Shape) (rows polynomialExponent precision : ℕ) (chunkIndex : Fin shape.chunk)
    {childLeft childExponent levels frames count : ℕ} (dependency : Path shape.active childLeft (childExponent+1) levels frames count)
    (right sourceRole targetRole liveDenominator : ℕ) (inputBank : Tapes (publicTapes stackCount roleCount) 2)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (suffix : Tapes (localTapes roleCount) prime)
    (stackOrigin : ℤ) (calls : List ComplexRecursiveCallSchema.Call)
    (reachedAssociation : CompactComplexSourceReadySavedCallHistory.Reached pcStack stackOrigin (call::calls)
      ((ready inputBank).append scalar))
    (sourceArray : Array shape rows polynomialExponent)
    (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes) (rowsPositive : 0<rows) (metadataFits : 2*shape.bits≤precision)
    (sourceWidth : Width shape rows polynomialExponent (precision-2*shape.bits) sourceArray)
    (basePrecision : ℕ)
    (rawHeaders : Placement.active headerPlacement (base inputBank)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw shape rows polynomialExponent precision chunkIndex.val childLeft (arity^childExponent) arity right sourceRole targetRole))
    (publicSourceReady : inputBank.head (CompactComplexSourceReadyLeafPhase.source (s:=10+stackCount))=0 ∧
      inputBank.tape (CompactComplexSourceReadyLeafPhase.source (s:=10+stackCount))=CompactSpectatorLeafAxis.word sourceArray)
    (liveReady : inputBank.head CompactComplexNonleafRoleChildBank.current=1 ∧
      inputBank.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (bits liveDenominator))
    (targetBlank : inputBank.head CompactComplexNonleafRoleChildBank.target=0 ∧
      inputBank.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank))
    (exponentWord : inputBank.tape (CompactComplexNonleafRoleChildBank.control 1)=RadixZeroFill.encodedBinary (bits (childExponent+1)))
    (exponentHead : inputBank.head (CompactComplexNonleafRoleChildBank.control 1)=1)
    (scalarRowLimit usedRows : ℕ) (unitPayload : shape.payload=1)
    (rightFitsActive : right≤shape.active) (sourceRoleFits : sourceRole≤arity) (targetRoleFits : targetRole≤arity)
    (baselineFits : basePrecision≤precision-2*shape.bits) (rowsUsedBound : usedRows≤scalarRowLimit)
    (denominatorRoom : CompactComplexDenominatorCapacity.room scalarRowLimit≤shape.chunk)
    (liveLedgerBound : liveDenominator≤CompactComplexDenominatorCapacity.ledger scalarRowLimit basePrecision levels frames count usedRows)
    (activeFitsAxes : shape.active≤shape.axes)
    (guardReady : CompactComplexSourceReadyGuard.Ready inputBank)
    (dimensionReady : inputBank.head CompactComplexSourceReadyGuard.dimension=1 ∧
      inputBank.tape CompactComplexSourceReadyGuard.dimension=RadixZeroFill.encodedBinary (bits shape.axes))
    (childStopped : ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=true) :
    let orientedInput := output call inputBank sourceArray
    let installedChild := CompactComplexCorrectedStoppedChildGridSemantics.installed call rows polynomialExponent
      (precision-2*shape.bits) chunkIndex dependency.visit (oriented call sourceArray)
    let completedBank := CompactComplexSourceReadyStoppedLeafCount.returned orientedInput
      (CompactSpectatorLeafAxis.word installedChild) (CompactComplexDenominatorPolicy.leafTarget liveDenominator (childExponent+1))
    ∃ olderWord olderHead,
      CompactComplexSourceReadySavedCallHistory.Associated stackOrigin calls olderWord olderHead ∧
      ∃ elapsedSteps≤(CompactComplexSourceReadyOrientationInvariants.constant+
        4*CompactComplexSourceReadyGuard.guardConstant+1)*
        CompactNativeRoleTransferBudget.volume rows shape polynomialExponent precision+1+
        (((CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+
          CompactComplexSourceReadyOrientationInvariants.constant+1)*
          CompactNativeRoleTransferBudget.volume rows shape polynomialExponent precision*(arity^(childExponent+1)))+1+
          (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)+5)),
        CompactComplexAlignedChildEntryPath.path basisProgram headerStack pcStack liveStack
          (controlPCFor originalCount schedule.length 0)
          ((Alphabet.mapTapes encoding ((ready inputBank).append scalar)).append suffix) elapsedSteps
          (CompactComplexScheduledPCDecode.savedPC call)
          ((Alphabet.mapTapes encoding ((ready (setTape completedBank
            (CompactComplexSourceReadyCorrectedSavedReturnPath.publicSaved pcStack) olderWord olderHead)).append scalar)).append suffix) := by
  dsimp only
  have initialSavedPorts := CompactComplexSourceReadyCorrectedSavedReturnPath.ready_saved pcStack inputBank scalar
  have publicAssociation := reachedAssociation
  unfold CompactComplexSourceReadySavedCallHistory.Reached at publicAssociation
  rw [initialSavedPorts.1,initialSavedPorts.2] at publicAssociation
  obtain ⟨initialOlderWord,initialHead,olderAssociation,_,initialSavedWord,initialSavedHead⟩ := CompactComplexSourceReadySavedCallHistory.top publicAssociation
  have savedStackReady : Placement.active (FiniteReturnStackAt.placement (savedSlot pcStack)) (ready inputBank)=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart initialOlderWord initialHead (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (initialHead+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) := by
    rw [FiniteReturnStackAt.active_bank]
    simp only [ready,CompactComplexSourceReadyLeafPhase.ready,savedSlot,Tapes.append,Fin.addCases_left]
    exact congrArg₂ FiniteReturnStack.bank initialSavedWord initialSavedHead
  let orientedInput := output call inputBank sourceArray
  let installedChild := CompactComplexCorrectedStoppedChildGridSemantics.installed call rows polynomialExponent
    (precision-2*shape.bits) chunkIndex dependency.visit (oriented call sourceArray)
  let completedBank := CompactComplexSourceReadyStoppedLeafCount.returned orientedInput
    (CompactSpectatorLeafAxis.word installedChild) (CompactComplexDenominatorPolicy.leafTarget liveDenominator (childExponent+1))
  have sourceReady := CompactComplexCorrectedStoppedClassifierTensor.classifier_source call inputBank sourceArray publicSourceReady.2 publicSourceReady.1
  have orientationRetainsSavedStack := CompactComplexSourceReadyOrientationInvariants.retained_savedSlot pcStack call (ready inputBank) sourceArray
  rw [ready_output] at orientationRetainsSavedStack
  have orientedSavedStackReady : Placement.active (FiniteReturnStackAt.placement (savedSlot pcStack)) (ready orientedInput)=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart initialOlderWord initialHead (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (initialHead+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) :=
    orientationRetainsSavedStack.trans savedStackReady
  have physicalWidthIdentity : CompactNativeRoleHeaders.recordWidth shape precision=
      ButterflyGuard.width (ButterflyIndependentGuardHeaders.reservation shape.bits (precision-2*shape.bits)) shape.bits := by
    unfold CompactNativeRoleHeaders.recordWidth ButterflyGuard.width ButterflyGuard.halfWidth
      ButterflyIndependentGuardHeaders.reservation
    omega
  have orientedWidth := CompactComplexSourceReadyOrientationInvariants.oriented_width call shape rows polynomialExponent (precision-2*shape.bits) sourceArray sourceWidth
  have physicalWidth : ∀ tapeIndex,((oriented call sourceArray) tapeIndex).1.length=CompactNativeRoleHeaders.recordWidth shape precision ∧
      ((oriented call sourceArray) tapeIndex).2.length=CompactNativeRoleHeaders.recordWidth shape precision := by
    intro tapeIndex
    rw [physicalWidthIdentity]
    exact orientedWidth tapeIndex
  have orientedHeaders := (output_headers call inputBank sourceArray).trans rawHeaders
  have orientationRetainsLive := CompactComplexSourceReadyOrientedControlsFrame.frame call inputBank sourceArray
    CompactComplexNonleafRoleChildBank.current (storage_ne _)
  have orientationRetainsTarget := CompactComplexSourceReadyOrientedControlsFrame.frame call inputBank sourceArray
    CompactComplexNonleafRoleChildBank.target (storage_ne _)
  have orientationRetainsExponent := CompactComplexSourceReadyOrientedControlsFrame.frame call inputBank sourceArray
    (CompactComplexNonleafRoleChildBank.control 1) (control_ne 1)
  obtain ⟨classifierSteps,classifierTimeBound,classifiedPath⟩ := classifier_path_width basisProgram headerStack pcStack liveStack call inputBank
    (SharedBank.empty _ 2) (SharedBank.empty _ 2) scalar suffix initialOlderWord initialHead savedStackReady
    dependency rowsPositive guardPositive axesPositive activeFitsAxes sourceArray sourceWidth
    publicSourceReady.2 publicSourceReady.1 guardReady dimensionReady ⟨exponentHead,exponentWord⟩
  have reservationEqualsPrecision : ButterflyIndependentGuardHeaders.reservation shape.bits (precision-2*shape.bits)=precision := by
    unfold ButterflyIndependentGuardHeaders.reservation
    omega
  rw [reservationEqualsPrecision] at classifierTimeBound
  rw [childStopped,ite_eq_left rfl] at classifiedPath
  obtain ⟨leafSteps,leafTimeBound,leafPath⟩ := positive_path_installed basisProgram headerStack pcStack liveStack call shape rows polynomialExponent precision chunkIndex
    dependency right sourceRole targetRole liveDenominator orientedInput scalar suffix initialOlderWord initialHead orientedSavedStackReady (oriented call sourceArray)
    guardPositive axesPositive rowsPositive metadataFits physicalWidth orientedHeaders sourceReady
    ⟨orientationRetainsLive.1.trans liveReady.1,orientationRetainsLive.2.trans liveReady.2⟩
    ⟨orientationRetainsTarget.1.trans targetBlank.1,orientationRetainsTarget.2.trans targetBlank.2⟩
    (orientationRetainsExponent.2.trans exponentWord) (orientationRetainsExponent.1.trans exponentHead)
    scalarRowLimit basePrecision usedRows unitPayload rightFitsActive sourceRoleFits targetRoleFits baselineFits rowsUsedBound denominatorRoom liveLedgerBound
  have completedSavedStack := (CompactComplexSourceReadyOrientedControlsStopped.returned_saved pcStack orientedInput
    (CompactSpectatorLeafAxis.word installedChild) (CompactComplexDenominatorPolicy.leafTarget liveDenominator (childExponent+1))).trans orientedSavedStackReady
  have completedSavedHead := congrArg (fun bankView : Tapes 1 2 => bankView.head 0) completedSavedStack
  have completedSavedWord := congrArg (fun bankView : Tapes 1 2 => bankView.tape 0) completedSavedStack
  rw [FiniteReturnStackAt.active_bank] at completedSavedHead completedSavedWord
  have completedHeadIdentity : completedBank.head (CompactComplexSourceReadyCorrectedSavedReturnPath.publicSaved pcStack)=
      initialHead+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3) := by
    simpa only [ready,CompactComplexSourceReadyLeafPhase.ready,savedSlot,Tapes.append,
      Fin.addCases_left,FiniteReturnStack.bank,CompactComplexSourceReadyCorrectedSavedReturnPath.publicSaved] using completedSavedHead
  have completedWordIdentity : completedBank.tape (CompactComplexSourceReadyCorrectedSavedReturnPath.publicSaved pcStack)=
      FiniteReturnStack.wordPart initialOlderWord initialHead (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl := by
    simpa only [ready,CompactComplexSourceReadyLeafPhase.ready,savedSlot,Tapes.append,
      Fin.addCases_left,FiniteReturnStack.bank,CompactComplexSourceReadyCorrectedSavedReturnPath.publicSaved] using completedSavedWord
  have completedAssociation := CompactComplexSourceReadySavedCallHistory.Associated.push olderAssociation call
  rw [←completedWordIdentity,←completedHeadIdentity] at completedAssociation
  obtain ⟨olderWord,olderHead,restoredAssociation,popPath⟩ := CompactComplexAlignedSavedReturnPath.public_associated_return_path basisProgram
    headerStack pcStack liveStack call completedBank scalar suffix stackOrigin calls completedAssociation
  refine ⟨olderWord,olderHead,restoredAssociation,classifierSteps+(leafSteps+(CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)+5)),
    Nat.add_le_add classifierTimeBound (Nat.add_le_add_right leafTimeBound _),?_⟩
  exact FiniteFlowPath.append classifiedPath (FiniteFlowPath.append leafPath popPath)

end
end IntegerMultBounds.Machine.CompactComplexAlignedStoppedChildRun
