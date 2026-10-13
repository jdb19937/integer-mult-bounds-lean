module

public import IntegerMultBounds.Machine.CompactComplexAlignedBoundaryPaths
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventTrace
public import IntegerMultBounds.Machine.CompactComplexCorrectedEntryGeometryReadiness

/-! The unchanged physical source split and source correction enter the actual
cursor-zero State constructed from the same original coefficients and ports.
Only the original blank target port is added to that node's readiness premises. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexAlignedReachedNodeEntryPath
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexChildHeadersData (parent)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactComplexSourceReadyReachedEventTrace (State physicalBank cursorPC cursorPCFor)
open CompactComplexSourceReadyReachedEventInvariant (canonical)
open CompactComplexAlignedBoundaryPaths (alignedBank)
open Networks.Shared50ModularControl (prime)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  CompactComplexCompletedLiveLower.schedule CompactComplexRolePhaseSite.roleCount

/-- The split destination is the first real event cursor even for an empty schedule. -/
theorem first_event_cursor (originalCount eventCount : ℕ) :
    CompactComplexSourceReadyCorrectedEntryTablePath.firstEventPC originalCount eventCount=
      cursorPCFor originalCount eventCount 0 := by
  unfold CompactComplexSourceReadyCorrectedEntryTablePath.firstEventPC cursorPCFor
  split_ifs <;> rfl

/-- Static paid source split, source correction, and their actual table joins. -/
def entryCost (shape : Shape) (rows ell metadataPrecision : ℕ) :=
  CompactComplexSourceReadyNonleafTargetSplit.constant roles*
    CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision+1+
  NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor*
    CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision+1

/-- The literal full source bank before the unchanged aligned tag-two program. -/
def originalBank {stackCount : ℕ} {shape : Shape} (stage : ActivePrefixStageParameters.Stage shape)
    (rows ell metadataPrecision : ℕ)
    (original : CompactSpectatorVisitGeometry.Array shape rows ell)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+stackCount) 2) (auxiliary : Tapes 2 2) :=
  alignedBank ((CompactComplexSourceReadyNonleafContraction.ready
    (CompactComplexNativeCodecFrame.bank control queue scalar (CompactComplexNativeCodec.raw stage rows ell metadataPrecision)
      tail storage (CompactNativeRoleReservedBridge.sourcePayload shape rows ell original roles))
    (auxiliary.append (SharedBank.empty 7 2))
    (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2)).append
    (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))

section Node
variable {stackCount basisStateCount : ℕ} {shape : Shape}
  {nodeLeft childExponent dependencyLevels frameVolume entryReturned : ℕ}
  {rowCount polynomialExponent inputPrecision baselinePrecision growthConstant baselineLive initialLive : ℕ}
  {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
  (phaseCoordinate : Fin shape.chunk)
  (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+2)
    dependencyLevels frameVolume entryReturned)
  (activeFits : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))

/-- The literal original whole-array input bank executes tag two and reaches
that same constructed physical initial State, with its source corrections paid. -/
theorem runs
    (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (headerStack liveStack : Fin stackCount)
    (originalCoefficients : CompactSpectatorVisitGeometry.Array shape rowCount polynomialExponent)
    (inputWidth : CompactSpectatorInheritedGrid.Width shape rowCount polynomialExponent inputPrecision originalCoefficients)
    (baselineFitsPrecision : baselinePrecision ≤ inputPrecision) (baselineFits : baselineLive≤baselinePrecision)
    (controlBank : Tapes 43 2) (queueBank : Tapes 1 2) (scalarHeaders : ActiveRepairRankHeadersCommands.State)
    (tailBank : Tapes 22 2) (originalStorage : Tapes (10+stackCount) 2) (auxiliaryBank : Tapes 2 2)
    (currentReady : originalStorage.head ⟨7,by omega⟩=1 ∧ originalStorage.tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits initialLive))
    (targetBlank : originalStorage.head ⟨8,by omega⟩=0 ∧ originalStorage.tape ⟨8,by omega⟩=(fun _ => blank))
    (initialLedger : initialLive≤CompactComplexDenominatorCapacity.ledger CompactComplexDenominatorCapacity.scalarRows
      baselineLive dependencyLevels frameVolume entryReturned (CompactFramedScalarGrid.rows 0).length)
    (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk)
    (rowsPositive : 0<rowCount) (rolesDivideRows : roles∣rowCount) (unitPayload : shape.payload=1)
    (parentSlots : (parent phaseCoordinate entryPath.visit activeFits pair).slots=25^3)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤shape.chunk)
    (axesPositive : 0<shape.axes)
    (initialState : State (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=savedCalls) 0 initialLive)
    (entryBank : initialState.bank=canonical
      (CompactComplexCorrectedEntryGeometryReadiness.permanent (parent phaseCoordinate entryPath.visit activeFits pair)
        parentSlots rowCount polynomialExponent (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
        initialLive (childExponent+1) rolesDivideRows originalCoefficients controlBank queueBank scalarHeaders tailBank originalStorage)
      auxiliaryBank) :
    ∃ elapsed≤entryCost shape rowCount polynomialExponent
        (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision),
      CompactComplexAlignedScalarEventPath.path basisProgram headerStack pcStack liveStack
        (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount
          CompactComplexCompletedLiveLower.schedule.length 2)
        (originalBank (parent phaseCoordinate entryPath.visit activeFits pair) rowCount polynomialExponent
          (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) originalCoefficients
          controlBank queueBank scalarHeaders tailBank originalStorage auxiliaryBank)
        elapsed (cursorPC 0) (physicalBank initialState) := by
  let stage := parent phaseCoordinate entryPath.visit activeFits pair
  let metadataPrecision := ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision
  have metadataFits : 2*shape.bits≤metadataPrecision := by
    dsimp only [metadataPrecision,ButterflyIndependentGuardHeaders.reservation]
    omega
  have storagePrecision : metadataPrecision-2*shape.bits=inputPrecision := by
    dsimp only [metadataPrecision,ButterflyIndependentGuardHeaders.reservation]
    omega
  have originalWidths : ∀ index,
      (originalCoefficients index).1.length=CompactNativeRoleHeaders.recordWidth shape metadataPrecision ∧
      (originalCoefficients index).2.length=CompactNativeRoleHeaders.recordWidth shape metadataPrecision := by
    intro index
    rw [CompactNativeRoleChildPrecision.stored_width shape metadataPrecision metadataFits,storagePrecision]
    obtain ⟨realWidth,imaginaryWidth⟩ := inputWidth index
    dsimp only [ButterflyGuard.width,ButterflyGuard.halfWidth] at realWidth imaginaryWidth
    dsimp only [ButterflyAxisHeadersData.width]
    constructor <;> omega
  have baselineFitsStorage : baselineLive≤metadataPrecision-2*shape.bits := by
    rw [storagePrecision]
    exact baselineFits.trans baselineFitsPrecision
  have parentWidth : stage.f=arity^(childExponent+1) := rfl
  have sourceDependency : CompactRecursiveDependencyBudget.Path shape.active stage.left (childExponent+2)
      dependencyLevels frameVolume entryReturned := entryPath
  obtain ⟨elapsed,elapsedBound,entryPathActual⟩ := CompactComplexAlignedBoundaryPaths.tag2_path
    basisProgram headerStack pcStack liveStack stage (childExponent+1) rowCount polynomialExponent metadataPrecision initialLive
    parentSlots parentWidth rowsPositive rolesDivideRows (by omega) axesPositive guardFitsChunk unitPayload metadataFits
    controlBank queueBank scalarHeaders tailBank originalStorage auxiliaryBank currentReady targetBlank
    originalCoefficients originalWidths sourceDependency CompactComplexDenominatorCapacity.scalarRows baselineLive
    (CompactFramedScalarGrid.rows 0).length baselineFitsStorage
    (CompactComplexDenominatorCapacity.actual_prefix 0) denominatorRoom initialLedger
    (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)
  have outputFull := CompactComplexCorrectedEntryGeometryReadiness.full_eq_caller
    stage parentSlots rowCount polynomialExponent metadataPrecision initialLive (childExponent+1) rolesDivideRows
    originalCoefficients controlBank queueBank scalarHeaders tailBank originalStorage auxiliaryBank
    (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)
  have outputCanonical : CompactComplexCorrectedEntryGeometryReadiness.full stage parentSlots rowCount polynomialExponent
      metadataPrecision initialLive (childExponent+1) rolesDivideRows originalCoefficients controlBank queueBank
      scalarHeaders tailBank originalStorage auxiliaryBank (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)=
      CompactComplexSourceReadyScalarWorkspace.ready initialState.bank := by
    rw [outputFull,entryBank]
    rfl
  refine ⟨elapsed,elapsedBound,?_⟩
  change CompactComplexAlignedScalarEventPath.path basisProgram headerStack pcStack liveStack _ _ elapsed
    (CompactComplexSourceReadyCorrectedEntryTablePath.firstEventPC CompactComplexScheduledPCLayout.originalCount
      CompactComplexCompletedLiveLower.schedule.length)
    (alignedBank (CompactComplexCorrectedEntryGeometryReadiness.full stage parentSlots rowCount polynomialExponent
      metadataPrecision initialLive (childExponent+1) rolesDivideRows originalCoefficients controlBank queueBank
      scalarHeaders tailBank originalStorage auxiliaryBank (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)))
      at entryPathActual
  rw [first_event_cursor,outputCanonical] at entryPathActual
  exact entryPathActual

end Node
end
end IntegerMultBounds.Machine.CompactComplexAlignedReachedNodeEntryPath
