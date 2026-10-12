module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyEventScheduleSemantics

/-! A genuine node-entry dependency Path pays the actual scalar action after
the counted schedule-prefix siblings. The current Reached returned counter is
the entry counter plus actual processed child volumes; no advanced Path is
assumed and the original signed-width reservation is unchanged. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadySiblingGuards
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexScalarIntegerRows (GroupIndex gates wireIndex)
open CompactComplexScalarSegmentRows (block)
open CompactComplexScalarSequenceSemantics (Bound values)
open CompactComplexScalarPolynomialSequence (execute)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
open CompactComplexSourceReadyChildEventSemantics (stored)
open CompactComplexCompletedLiveLower (schedule childNames)
open Networks
attribute [local irreducible] ComplexRank25.program CompactComplexRolePhaseSite.roleCount
  CompactComplexScalarIntegerRows.gates schedule

def returnedCursor (entryReturned eventIndex childVolume : ℕ) :=
  entryReturned+(childNames (schedule.take eventIndex)).length*childVolume

private theorem run_gates (columns : ℕ) (gateProgram : Circuit.Program ComplexFramedExecution.Wire ℚ)
    (bank : CompactComplexActualEventNetwork.Stored columns) :
    FramedFactorExecution.run (gateProgram.map FramedFactorExecution.Instruction.gate) bank=
      FramedCircuit.run (gateProgram.map FramedCircuit.Instruction.gate) bank := by
  induction gateProgram generalizing bank with
  | nil => rfl
  | cons gate remaining inductionHypothesis => exact inductionHypothesis _

private theorem gates_module (columns : ℕ) (gateProgram : Circuit.Program ComplexFramedExecution.Wire ℚ)
    (bank : CompactComplexActualEventNetwork.Stored columns) :
    FramedCircuit.run (gateProgram.map FramedCircuit.Instruction.gate) bank=
      FramedCircuit.moduleRun gateProgram bank := by
  induction gateProgram generalizing bank with
  | nil => rfl
  | cons gate remaining inductionHypothesis => exact inductionHypothesis _

section Parent
variable {extraTapes : ℕ} {shape : Shape} {stage : ActivePrefixStageParameters.Stage shape}
    {parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive : ℕ}
    {dependencyLevels frameVolume entryReturned eventIndex childVolume parentLive : ℕ}
    {pcStack : Fin extraTapes} {origin : ℤ} {calls : List ComplexRecursiveCallSchema.Call}
    {parentBank : Tapes (nodeTapes extraTapes roles) 2}

/-- The actual schedule prefix and original entry Path supply every uniform
signed numerator bound and scalar row reserve for the current readiness bank. -/
theorem scalar_reserve {nodeLeft : ℕ}
    (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft nodeExponent
      dependencyLevels frameVolume entryReturned)
    (childFitsNode : childVolume≤arity^nodeExponent) (group : GroupIndex)
    (parentReached : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent
      baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume
      (returnedCursor entryReturned eventIndex childVolume) group.val parentLive pcStack origin calls parentBank)
    (activePositive : 0<shape.active)
    (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision)
    (axesFit : completedAxes≤shape.bits)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      (gates group).length*CompactComplexScalarIntegerRows.guardBits≤shape.chunk) :
    Bound (ButterflyGuard.halfWidth metadataPrecision shape.bits)
      (CompactComplexScalarPathGuard.power shape baselinePrecision growthConstant completedAxes) parentReached.data ∧
    CompactComplexScalarPathGuard.power shape baselinePrecision growthConstant completedAxes+
      (block group).length*CompactComplexScalarIntegerRows.guardBits≤
      ButterflyGuard.halfWidth metadataPrecision shape.bits := by
  have prefixBound := CompactFramedScalarGrid.bound_le group.val
    (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels
      (frameVolume+2*returnedCursor entryReturned eventIndex childVolume+completedAxes)) growthConstant growthReserve
  have scalarBudget : CompactFramedScalarGrid.bound group.val
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels
        (frameVolume+2*returnedCursor entryReturned eventIndex childVolume+completedAxes))≤
      CompactComplexScalarPathGuard.budget baselinePrecision growthConstant dependencyLevels frameVolume
        (returnedCursor entryReturned eventIndex childVolume) completedAxes :=
    prefixBound.trans_eq (CompactRecursiveGridBudget.scalar_step baselinePrecision growthConstant dependencyLevels _)
  have growthPower := CompactComplexSourceReadyEventScheduleSemantics.sibling_growth_power entryPath
    (childNames (schedule.take eventIndex)).length childVolume baselinePrecision growthConstant completedAxes
    (CompactComplexSourceReadyEventScheduleSemantics.processed_calls_le_capacity eventIndex) childFitsNode
  constructor
  · intro role coefficient
    have represented := ButterflyGuard.represented_bound _ _ parentLive _
      (GaussianPrecision.bound_mono scalarBudget (parentReached.grid (wireIndex.symm role) coefficient))
    simp only [Equiv.apply_symm_apply] at represented
    have numeratorReserve := Int.ofNat_le.mpr growthPower.le
    exact ⟨represented.1.trans numeratorReserve,represented.2.trans numeratorReserve⟩
  · apply CompactComplexScalarRoleSemantics.stored_reserve shape baselinePrecision growthConstant completedAxes
      metadataPrecision (block group).length activePositive precisionReserve axesFit
    simpa only [CompactComplexScalarSegmentRows.block_length] using chunkRoom

/-- The current actual scalar data has original gate semantics even when
its returned counter includes siblings absent from the entry Path index. -/
theorem computed_scalar_semantics {nodeLeft sliceLeft childExponent : ℕ}
    (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft nodeExponent
      dependencyLevels frameVolume entryReturned)
    (childFitsNode : childVolume≤arity^nodeExponent)
    (phaseCoordinate : Fin shape.chunk) (visit : Visit shape.active sliceLeft (childExponent+2))
    (group : GroupIndex)
    (parentReached : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent
      baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume
      (returnedCursor entryReturned eventIndex childVolume) group.val parentLive pcStack origin calls parentBank)
    (activePositive : 0<shape.active)
    (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision)
    (axesFit : completedAxes≤shape.bits)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      (gates group).length*CompactComplexScalarIntegerRows.guardBits≤shape.chunk)
    (row : Fin (parentRows/roles)) (polynomialIndex : Fin (2^polynomialExponent))
    (anchor : BinaryWalsh.Address shape.bits) :
    stored phaseCoordinate visit (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits)
      (parentLive+(gates group).length) (execute (block group) parentReached.data) row polynomialIndex anchor=
    FramedFactorExecution.run
      (CompactComplexActualInterleavedNetwork.instructions (arity^(childExponent+1)) (.scalar group))
      (stored phaseCoordinate visit (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits)
        parentLive parentReached.data row polynomialIndex anchor) := by
  obtain ⟨numeratorReserve,rowReserve⟩ := scalar_reserve entryPath childFitsNode group parentReached
    activePositive precisionReserve axesFit growthReserve chunkRoom
  change _=FramedFactorExecution.run ((gates group).map FramedFactorExecution.Instruction.gate) _
  rw [run_gates,gates_module]
  funext wire tensorAddress
  have scalarValues := CompactComplexScalarSequenceSemantics.sequence_values (block group) parentReached.data
    (ButterflyGuard.halfWidth metadataPrecision shape.bits)
    (CompactComplexScalarPathGuard.power shape baselinePrecision growthConstant completedAxes)
    parentLive parentReached.width numeratorReserve rowReserve
    (RecursiveInterchangeRows.pack row (FlatCoordinateLayout.index
      (CompactComplexNonleafChildAddress.insert phaseCoordinate visit anchor tensorAddress) polynomialIndex))
  rw [CompactComplexScalarSegmentRows.block_circuit,CompactComplexScalarSegmentRows.block_length] at scalarValues
  unfold CompactComplexScalarSequenceSemantics.values at scalarValues
  have metadataFits : 2*shape.bits≤metadataPrecision := by omega
  have widthEquation := CompactComplexSourceReadyReachedReturnInvariant.inherited_half_eq metadataFits
  have pointwise := RationalScalarGrid.run_pointwise (gates group)
    (stored phaseCoordinate visit (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits)
      parentLive parentReached.data row polynomialIndex anchor) wire tensorAddress
  refine Eq.trans ?_ pointwise.symm
  simpa only [stored,CompactComplexStoppedLeafTensorSemantics.slice,
    CompactComplexActualBasisPullback.nativeField,CompactSpectatorInheritedGrid.decoded,
    CompactComplexScalarSequenceSemantics.values,ButterflyStreamSemantics.decode,widthEquation]
    using (congrFun scalarValues wire)

/-- An actual scalar-successor readiness witness uses the original node-entry
Path after arbitrary counted sibling calls. Its emitted data equation suffices;
no fictitious Path with an advanced returned counter is required. -/
theorem reached_scalar_semantics {nodeLeft sliceLeft childExponent : ℕ}
    (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft nodeExponent
      dependencyLevels frameVolume entryReturned)
    (childFitsNode : childVolume≤arity^nodeExponent)
    (phaseCoordinate : Fin shape.chunk) (visit : Visit shape.active sliceLeft (childExponent+2))
    (group : GroupIndex)
    (parentReached : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent
      baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume
      (returnedCursor entryReturned eventIndex childVolume) group.val parentLive pcStack origin calls parentBank)
    (nextReached : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent
      baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume
      (returnedCursor entryReturned eventIndex childVolume) (group.val+1) (parentLive+(gates group).length)
      pcStack origin calls (CompactComplexSourceReadyScalarWorkspace.output parentBank
        (CompactComplexSourceReadyReachedEventInvariant.nextCaller parentReached group)))
    (dataEquation : nextReached.data=execute (block group) parentReached.data)
    (activePositive : 0<shape.active)
    (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision)
    (axesFit : completedAxes≤shape.bits)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      (gates group).length*CompactComplexScalarIntegerRows.guardBits≤shape.chunk)
    (row : Fin (parentRows/roles)) (polynomialIndex : Fin (2^polynomialExponent))
    (anchor : BinaryWalsh.Address shape.bits) :
    stored phaseCoordinate visit (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits)
      (parentLive+(gates group).length) nextReached.data row polynomialIndex anchor=
    FramedFactorExecution.run
      (CompactComplexActualInterleavedNetwork.instructions (arity^(childExponent+1)) (.scalar group))
      (stored phaseCoordinate visit (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits)
        parentLive parentReached.data row polynomialIndex anchor) := by
  rw [dataEquation]
  exact computed_scalar_semantics entryPath childFitsNode phaseCoordinate visit group parentReached
    activePositive precisionReserve axesFit growthReserve chunkRoom row polynomialIndex anchor

end Parent
end
end IntegerMultBounds.Machine.CompactComplexSourceReadySiblingGuards
