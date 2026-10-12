module

public import IntegerMultBounds.Machine.CompactComplexSourceReadySiblingGuards
public import IntegerMultBounds.Machine.CompactComplexSourceReadyScalarGeometryEventPath

/-! The physical scalar successor after counted siblings uses the original
entry dependency Path. Its current live capacity and Gaussian reserve derive
from real prefix accounting; no advanced Path or execution callback is needed. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadySiblingScalarPath
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexScalarIntegerRows (GroupIndex gates)
open CompactComplexScalarSegmentRows (block)
open CompactComplexScalarCallerEndpoint (storageOutput emitted)
open CompactComplexScalarPolynomialSequence (execute)
open CompactComplexScalarSequenceSemantics (values circuit)
open CompactComplexNativeCodecFrame (bank)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes permanent ready output)
open CompactComplexSourceReadyReachedEventInvariant (Reached nextCaller canonical_output)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexDenominatorCapacity (ledger scalarRows)
open Networks
open Networks.GaussianPrecision (BoundedGrid)
attribute [local irreducible] ComplexRank25.program CompactComplexRolePhaseSite.roleCount
  CompactComplexScalarIntegerRows.gates CompactComplexCompletedLiveLower.schedule
  ComplexFramedExecution.rows CompactComplexDenominatorCapacity.scalarRows
  CompactRecursiveDependencyBudget.volumeCoefficient CompactRecursiveDependencyBudget.callCapacity

private theorem ledger_capacity_arithmetic
    (active rowBound volumeCoefficient dependencyLevels frameVolume returnedVolume usedRows
      baselineLive baselinePrecision parentLive metadataPrecision bitCount : ℕ)
    (levelsFit : dependencyLevels+1≤active)
    (volumesFit : frameVolume+2*returnedVolume≤volumeCoefficient*active)
    (rowsFit : usedRows≤rowBound)
    (liveLedger : parentLive≤baselineLive+dependencyLevels*rowBound+frameVolume+2*returnedVolume+usedRows)
    (roomFits : (rowBound+volumeCoefficient+2)*active≤bitCount)
    (baselineFits : baselineLive≤baselinePrecision)
    (precisionReserve : baselinePrecision+2*bitCount≤metadataPrecision) :
    parentLive≤ButterflyGuard.halfWidth metadataPrecision bitCount+1 := by
  have levelCharge := Nat.mul_le_mul_right rowBound levelsFit
  have liveBound : parentLive≤baselineLive+(rowBound+volumeCoefficient)*active := by
    nlinarith
  unfold ButterflyGuard.halfWidth
  nlinarith

private theorem active_chunk_le_bits (shape : Shape) :
    shape.active*shape.chunk≤shape.bits := by
  unfold Shape.bits
  omega

private theorem room_eq (rowBound : ℕ) :
    CompactComplexDenominatorCapacity.room rowBound=
      rowBound+CompactRecursiveDependencyBudget.volumeCoefficient+2 := rfl

private theorem returned_cursor_eq (entryReturned eventIndex childVolume : ℕ) :
    returnedCursor entryReturned eventIndex childVolume=
      entryReturned+(CompactComplexCompletedLiveLower.childNames
        (CompactComplexCompletedLiveLower.schedule.take eventIndex)).length*childVolume := rfl

section Parent
variable {extraTapes : ℕ} {shape : Shape} {stage : ActivePrefixStageParameters.Stage shape}
    {nodeLeft nodeExponent dependencyLevels frameVolume entryReturned eventIndex childVolume : ℕ}
    {parentRows polynomialExponent metadataPrecision baselinePrecision growthConstant completedAxes baselineLive parentLive : ℕ}
    {pcStack : Fin extraTapes} {origin : ℤ} {calls : List ComplexRecursiveCallSchema.Call}
    {parentBank : Tapes (nodeTapes extraTapes roles) 2}
    (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft nodeExponent
      dependencyLevels frameVolume entryReturned)
    (childFitsNode : childVolume≤arity^nodeExponent) (group : GroupIndex)
    (parentReached : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent
      baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume
      (returnedCursor entryReturned eventIndex childVolume) group.val parentLive pcStack origin calls parentBank)

include entryPath childFitsNode group parentReached

/-- The counted sibling ledger fits the actual retained live field, paid by
the unchanged original denominator room. -/
theorem current_capacity (baselineFits : baselineLive≤baselinePrecision)
    (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision)
    (denominatorRoom : CompactComplexDenominatorCapacity.room scalarRows≤shape.chunk) :
    parentLive≤ButterflyGuard.halfWidth metadataPrecision shape.bits+1 := by
  have levelPotential := entryPath.levels_le
  have nodeVolumePositive : 0<arity^nodeExponent := pow_pos (by decide) _
  have levelsFit : dependencyLevels+1≤shape.active :=
    Nat.succ_le_of_lt ((Nat.lt_add_of_pos_right nodeVolumePositive).trans_le levelPotential)
  have volumesFit := CompactComplexSourceReadyEventScheduleSemantics.schedule_prefix_volume_bound
    entryPath eventIndex childVolume childFitsNode
  have rowsFit := CompactComplexDenominatorCapacity.actual_prefix group.val
  have liveLedger := parentReached.upper_ledger
  unfold ledger at liveLedger
  have roomCharge := Nat.mul_le_mul_right shape.active denominatorRoom
  have roomFits : CompactComplexDenominatorCapacity.room scalarRows*shape.active≤shape.bits := by
    exact roomCharge.trans ((Nat.le_of_eq (Nat.mul_comm _ _)).trans (active_chunk_le_bits shape))
  rw [←returned_cursor_eq entryReturned eventIndex childVolume] at volumesFit
  rw [room_eq] at roomFits
  exact ledger_capacity_arithmetic shape.active scalarRows CompactRecursiveDependencyBudget.volumeCoefficient
    dependencyLevels frameVolume (returnedCursor entryReturned eventIndex childVolume)
    (CompactFramedScalarGrid.rows group.val).length baselineLive baselinePrecision parentLive metadataPrecision shape.bits
    levelsFit volumesFit rowsFit liveLedger
    roomFits baselineFits precisionReserve

/-- The exact next original scalar prefix is certified from the sibling
reserve and the actual emitted sequence, retaining its common live denominator. -/
theorem group_grid (activePositive : 0<shape.active)
    (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision)
    (axesFit : completedAxes≤shape.bits)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      (gates group).length*CompactComplexScalarIntegerRows.guardBits≤shape.chunk) :
    ∀ coefficient wire,BoundedGrid (parentLive+(gates group).length)
      (CompactFramedScalarGrid.bound (group.val+1)
        (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels
          (frameVolume+2*returnedCursor entryReturned eventIndex childVolume+completedAxes)))
      (values (ButterflyGuard.halfWidth metadataPrecision shape.bits) (parentLive+(gates group).length)
        (execute (block group) parentReached.data) coefficient wire) := by
  obtain ⟨numeratorReserve,rowReserve⟩ := CompactComplexSourceReadySiblingGuards.scalar_reserve
    entryPath childFitsNode group parentReached activePositive precisionReserve axesFit growthReserve chunkRoom
  intro coefficient wire
  have emittedGrid := CompactComplexScalarSequenceGrid.sequence_grid (block group) parentReached.data
    (ButterflyGuard.halfWidth metadataPrecision shape.bits)
    (CompactComplexScalarPathGuard.power shape baselinePrecision growthConstant completedAxes)
    parentLive _ parentReached.width numeratorReserve rowReserve parentReached.grid coefficient wire
  let numeratorBound := CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels
    (frameVolume+2*returnedCursor entryReturned eventIndex childVolume+completedAxes)
  have prefixEquation := congrArg (fun gateProgram => GaussianPrecision.scalarBound 1 52 gateProgram numeratorBound)
    (CompactComplexScalarSegmentRows.prefix_complete group)
  rw [GaussianPrecision.scalarBound_append] at prefixEquation
  change GaussianPrecision.scalarBound 1 52 (circuit (block group))
    (CompactFramedScalarGrid.bound group.val numeratorBound)=
    CompactFramedScalarGrid.bound (group.val+1) numeratorBound at prefixEquation
  rw [prefixEquation,CompactComplexScalarSegmentRows.block_length] at emittedGrid
  exact emittedGrid

/-- The actual scalar lifecycle produces its full Reached successor after
counted sibling calls, with physical runtime and all tape readiness derived. -/
theorem scalar_successor (rowsPositive : 0<parentRows/roles) (guardPositive : 0<shape.guard)
    (chunkPositive : 0<shape.chunk) (activePositive : 0<shape.active)
    (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision)
    (axesFit : completedAxes≤shape.bits)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      (gates group).length*CompactComplexScalarIntegerRows.guardBits≤shape.chunk)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (baselineFits : baselineLive≤baselinePrecision)
    (denominatorRoom : CompactComplexDenominatorCapacity.room scalarRows≤shape.chunk) :
    HoareTime (CompactComplexSourceReadyActualTable.scalar (s:=extraTapes) group).2
      (fun result => result=ready parentBank)
      (fun result => result=ready (output parentBank (nextCaller parentReached group)))
      (CompactComplexScalarCountLifecycle.roleTimeConstant (block group)*
        (parentRows*2^shape.bits*2^polynomialExponent)*(ButterflyGuard.halfWidth metadataPrecision shape.bits+2)) ∧
    ∃ nextReached : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent
      baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume
      (returnedCursor entryReturned eventIndex childVolume) (group.val+1)
      (parentLive+(gates group).length) pcStack origin calls (output parentBank (nextCaller parentReached group)),
      nextReached.data=execute (block group) parentReached.data := by
  have permanentEquation : permanent parentBank=bank parentReached.control parentReached.queue parentReached.scalar
      (CompactComplexNativeCodec.raw stage parentRows polynomialExponent metadataPrecision)
      parentReached.tail parentReached.storage parentReached.payload :=
    (congrArg permanent parentReached.canonical_bank).trans
      (CompactComplexSourceReadyReachedEventInvariant.canonical_permanent _ _)
  have liveFieldCapacity := current_capacity entryPath childFitsNode group parentReached
    baselineFits precisionReserve denominatorRoom
  have roleRuns := CompactComplexSourceReadyScalarGeometryLifecycle.role_runs_linear stage
    parentRows polynomialExponent metadataPrecision rowsPositive guardPositive chunkPositive
    (by omega : 7<10+extraTapes) CompactComplexSourceReadyActualTable.countHeader
    CompactComplexSourceReadyActualTable.countHeader_ne_live (block group)
    (ButterflyGuard.halfWidth metadataPrecision shape.bits+1) parentLive
    parentReached.control parentReached.queue parentReached.scalar parentReached.tail
    parentReached.storage parentReached.payload parentReached.data parentReached.width parentReached.count_blank
    parentReached.role_words parentReached.live liveFieldCapacity
  have callerEndpoint := CompactComplexScalarCallerEndpoint.output_bank (by omega : 7<10+extraTapes)
    CompactComplexSourceReadyActualTable.countHeader CompactComplexSourceReadyActualTable.countHeader_ne_live
    parentReached.control parentReached.queue parentReached.scalar
    (CompactComplexNativeCodec.raw stage parentRows polynomialExponent metadataPrecision)
    parentReached.tail parentReached.storage parentReached.payload (execute (block group) parentReached.data)
    (parentLive+(block group).length) parentReached.count_blank
  dsimp only at roleRuns
  rw [callerEndpoint,CompactComplexScalarSegmentRows.block_length,←permanentEquation] at roleRuns
  have physicalRuns := CompactComplexSourceReadyScalarWorkspace.role_realizes (s:=extraTapes)
    CompactComplexSourceReadyActualTable.countHeader CompactComplexSourceReadyActualTable.countHeader_ne_live
    (block group) parentBank _ roleRuns
  have nextWidth := CompactComplexScalarLifecycleGrid.output_width (block group) parentReached.data _ parentReached.width
  have nextGrid := group_grid entryPath childFitsNode group parentReached
    activePositive precisionReserve axesFit growthReserve chunkRoom
  have nextLedger := CompactComplexRecursiveLiveProgress.scalar_segment_bound baselineLive dependencyLevels frameVolume
    (returnedCursor entryReturned eventIndex childVolume) (CompactFramedScalarGrid.rows group.val).length
    parentLive (block group) parentReached.upper_ledger
  rw [←CompactComplexScalarSegmentRows.prefix_length,CompactComplexScalarSegmentRows.block_length] at nextLedger
  have nextReadiness := CompactComplexSourceReadyScalarGeometryEventPath.next_ready parentRows polynomialExponent
    (by omega : 7<10+extraTapes) CompactComplexSourceReadyActualTable.countHeader
    CompactComplexSourceReadyActualTable.countHeader_ne_live parentReached.control parentReached.queue parentReached.scalar
    (CompactComplexNativeCodec.raw stage parentRows polynomialExponent metadataPrecision) parentReached.tail parentReached.storage parentReached.payload
    (execute (block group) parentReached.data) (parentLive+(gates group).length) parentReached.count_blank
  have nextSavedHistory := CompactComplexSourceReadyScalarSavedCallHistory.output_reached pcStack
    (by omega : 7<10+extraTapes) parentReached.control parentReached.queue parentReached.scalar
    (CompactComplexNativeCodec.raw stage parentRows polynomialExponent metadataPrecision) parentReached.tail parentReached.storage parentReached.payload
    (fun role => CompactSpectatorLeafAxis.word
      (execute (block group) parentReached.data (CompactComplexScalarRolePorts.roleIndex.symm role)))
    (parentLive+(gates group).length) origin calls parentBank permanentEquation parentReached.saved_calls
  refine ⟨physicalRuns,?_⟩
  refine ⟨{
    control := parentReached.control, queue := parentReached.queue, scalar := parentReached.scalar, tail := parentReached.tail,
    storage := storageOutput (by omega) parentReached.storage (parentLive+(gates group).length),
    payload := emitted parentReached.payload (fun role => CompactSpectatorLeafAxis.word
      (execute (block group) parentReached.data (CompactComplexScalarRolePorts.roleIndex.symm role))),
    aux := parentReached.aux, data := execute (block group) parentReached.data,
    canonical_bank := ?_, width := nextWidth, count_blank := ⟨nextReadiness.1,nextReadiness.2.1⟩,
    role_words := nextReadiness.2.2, source_blank := ?_, clock_blank := parentReached.clock_blank,
    aux_free := parentReached.aux_free, exponentValue := parentReached.exponentValue, exponentValue_eq := parentReached.exponentValue_eq, exponent := parentReached.exponent, control28_blank := parentReached.control28_blank,
    control29_blank := parentReached.control29_blank, live := ?_, targetValue := parentReached.targetValue,
    target := ?_, target_growth := by have targetGrowth := parentReached.target_growth; omega, upper_ledger := nextLedger,
    grid := fun wire coefficient => nextGrid coefficient wire, saved_calls := nextSavedHistory },rfl⟩
  · exact (congrArg (fun z => output z (nextCaller parentReached group)) parentReached.canonical_bank).trans
      (canonical_output _ _ _)
  · change (emitted parentReached.payload _).head (Fin.castAdd roles (0 : Fin 1))=0 ∧
      (emitted parentReached.payload _).tape (Fin.castAdd roles (0 : Fin 1))=(fun _ => blank)
    simpa only [emitted,Fin.addCases_left] using parentReached.source_blank
  · simp only [storageOutput,SharedPlacementAlphabet.setTape,Function.update_self,and_self]
  · have targetDistinct : (⟨8,by omega⟩ : Fin (10+extraTapes))≠⟨7,by omega⟩ := by
      intro portEquation; have permanentEquation := congrArg Fin.val portEquation; change (8 : ℕ)=7 at permanentEquation; omega
    simpa only [storageOutput,SharedPlacementAlphabet.setTape,Function.update_of_ne targetDistinct] using parentReached.target


end Parent
end
end IntegerMultBounds.Machine.CompactComplexSourceReadySiblingScalarPath
