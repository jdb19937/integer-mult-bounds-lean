module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyChildEventSemantics
public import IntegerMultBounds.Machine.CompactComplexActualInterleavedNetwork

/-! The actual scalar successor acts on the literal decoded stored slices by
its original named gate block. Its guards follow from genuine parent readiness
and dependency geometry, without arrayIndex supplied original-network prefix equality. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyScalarEventSemantics
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexScalarIntegerRows (GroupIndex gates wireIndex)
open CompactComplexScalarRowBlock (wireCount)
open CompactComplexScalarPolynomialSequence (execute)
open CompactComplexScalarSegmentRows (block)
open CompactComplexSourceReadyChildEventSemantics (stored)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes ready output)
open CompactComplexSourceReadyReachedEventInvariant (Reached nextCaller)
open CompactComplexNonleafChildAddress (insert)
open RecursiveInterchangeRows (pack)
open Networks
attribute [local irreducible] ComplexRank25.program CompactComplexRolePhaseSite.roleCount
  CompactComplexScalarIntegerRows.gates CompactComplexCompletedLiveLower.schedule

private theorem run_gates (columns : ℕ) (gateProgram : Circuit.Program ComplexFramedExecution.Wire ℚ)
    (bank : CompactComplexActualEventNetwork.Stored columns) :
    FramedFactorExecution.run (gateProgram.map FramedFactorExecution.Instruction.gate) bank=
      FramedCircuit.run (gateProgram.map FramedCircuit.Instruction.gate) bank := by
  induction gateProgram generalizing bank with
  | nil => rfl
  | cons group gateProgram ih => exact ih _

/-- The abstract gate bank is the actual row, polynomial and spectator slice
of serialized role coefficients at the inherited metadata width. -/
theorem bank_stored {shape : Shape} {dependencyLeft childExponent : ℕ} (phaseCoordinate : Fin shape.chunk)
    (visit : Visit shape.active dependencyLeft (childExponent+2)) (rowCount polynomialExponent metadataPrecision parentLive : ℕ)
    (metadataFits : 2*shape.bits≤metadataPrecision) (data : Fin wireCount → Array shape rowCount polynomialExponent)
    (row : Fin rowCount) (polynomialIndex : Fin (2^polynomialExponent)) (anchor : BinaryWalsh.Address shape.bits) :
    CompactComplexActualScalarNetworkPrefix.bank (arity^(childExponent+1))
      (ButterflyGuard.halfWidth metadataPrecision shape.bits) parentLive data
      (fun arrayIndex => pack row (FlatCoordinateLayout.index (insert phaseCoordinate visit anchor arrayIndex) polynomialIndex))=
    stored phaseCoordinate visit rowCount polynomialExponent (metadataPrecision-2*shape.bits) parentLive data row polynomialIndex anchor := by
  rw [←CompactComplexSourceReadyReachedReturnInvariant.inherited_half_eq metadataFits]
  rfl

section Reached
variable {extraTapes : ℕ} {shape : Shape} {stage : ActivePrefixStageParameters.Stage shape}
    {parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume returnedVolume parentLive : ℕ}
    {pcStack : Fin extraTapes} {origin : ℤ} {calls : List ComplexRecursiveCallSchema.Call}
    {v : Tapes (nodeTapes extraTapes roles) 2}

/-- The computed integer scalar block has the original single-event action
on every genuine stored slice, without requiring AlignedPrefix. -/
theorem computed_scalar_semantics {dependencyLeft nodeLeft childExponent : ℕ}
    (path : CompactRecursiveDependencyBudget.Path shape.active dependencyLeft nodeExponent dependencyLevels frameVolume returnedVolume)
    (phaseCoordinate : Fin shape.chunk) (visit : Visit shape.active nodeLeft (childExponent+2)) (group : GroupIndex)
    (parentReached : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume returnedVolume group.val parentLive pcStack origin calls v)
    (activePositive : 0<shape.active) (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision) (axesFit : completedAxes≤shape.bits)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      (gates group).length*CompactComplexScalarIntegerRows.guardBits≤shape.chunk)
    (row : Fin (parentRows/roles)) (polynomialIndex : Fin (2^polynomialExponent)) (anchor : BinaryWalsh.Address shape.bits) :
    stored phaseCoordinate visit (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits) (parentLive+(gates group).length)
      (execute (block group) parentReached.data) row polynomialIndex anchor=
    FramedFactorExecution.run
      (CompactComplexActualInterleavedNetwork.instructions (arity^(childExponent+1)) (.scalar group))
      (stored phaseCoordinate visit (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits) parentLive parentReached.data row polynomialIndex anchor) := by
  have blockChunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      (block group).length*CompactComplexScalarIntegerRows.guardBits≤shape.chunk := by
    simpa only [CompactComplexScalarSegmentRows.block_length] using chunkRoom
  have metadataFits : 2*shape.bits≤metadataPrecision := by omega
  have gateSemantics := CompactComplexActualScalarNetworkPrefix.group_gate_values path (arity^(childExponent+1)) group parentReached.data
    (fun arrayIndex => pack row (FlatCoordinateLayout.index (insert phaseCoordinate visit anchor arrayIndex) polynomialIndex))
    baselinePrecision growthConstant completedAxes metadataPrecision parentLive activePositive precisionReserve axesFit growthReserve blockChunkRoom parentReached.width parentReached.grid
  rw [CompactComplexScalarSegmentRows.block_length] at gateSemantics
  rw [bank_stored phaseCoordinate visit (parentRows/roles) polynomialExponent metadataPrecision _ metadataFits,
    bank_stored phaseCoordinate visit (parentRows/roles) polynomialExponent metadataPrecision _ metadataFits] at gateSemantics
  rw [←run_gates] at gateSemantics
  exact gateSemantics

/-- The actual readiness witness data equation specializes the computed
scalar semantics to its exact physical successor bank. -/
theorem reached_scalar_semantics {dependencyLeft nodeLeft childExponent : ℕ}
    (path : CompactRecursiveDependencyBudget.Path shape.active dependencyLeft nodeExponent dependencyLevels frameVolume returnedVolume)
    (phaseCoordinate : Fin shape.chunk) (visit : Visit shape.active nodeLeft (childExponent+2)) (group : GroupIndex)
    (parentReached : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume returnedVolume group.val parentLive pcStack origin calls v)
    (nextReached : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume returnedVolume (group.val+1)
      (parentLive+(gates group).length) pcStack origin calls (output v (nextCaller parentReached group)))
    (dataEquation : nextReached.data=execute (block group) parentReached.data)
    (activePositive : 0<shape.active) (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision) (axesFit : completedAxes≤shape.bits)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      (gates group).length*CompactComplexScalarIntegerRows.guardBits≤shape.chunk)
    (row : Fin (parentRows/roles)) (polynomialIndex : Fin (2^polynomialExponent)) (anchor : BinaryWalsh.Address shape.bits) :
    stored phaseCoordinate visit (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits) (parentLive+(gates group).length)
      nextReached.data row polynomialIndex anchor=
    FramedFactorExecution.run
      (CompactComplexActualInterleavedNetwork.instructions (arity^(childExponent+1)) (.scalar group))
      (stored phaseCoordinate visit (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits) parentLive parentReached.data row polynomialIndex anchor) := by
  rw [dataEquation]
  exact computed_scalar_semantics path phaseCoordinate visit group parentReached activePositive precisionReserve axesFit growthReserve chunkRoom row polynomialIndex anchor

/-- The physical scalar lifecycle itself produces the exact successor and
its named event semantics, retaining the proved real runtime. -/
theorem scalar_successor_semantics {dependencyLeft nodeLeft childExponent : ℕ}
    (path : CompactRecursiveDependencyBudget.Path shape.active dependencyLeft nodeExponent dependencyLevels frameVolume returnedVolume)
    (phaseCoordinate : Fin shape.chunk) (visit : Visit shape.active nodeLeft (childExponent+2)) (group : GroupIndex)
    (parentReached : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume returnedVolume group.val parentLive pcStack origin calls v)
    (rowsPositive : 0<parentRows/roles) (guardPositive : 0<shape.guard) (chunkPositive : 0<shape.chunk)
    (activePositive : 0<shape.active) (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision) (axesFit : completedAxes≤shape.bits)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      (gates group).length*CompactComplexScalarIntegerRows.guardBits≤shape.chunk)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant) (baselineFits : baselineLive≤baselinePrecision)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤shape.chunk) :
    HoareTime (CompactComplexSourceReadyActualTable.scalar (s:=extraTapes) group).2
      (fun z => z=ready v) (fun z => z=ready (output v (nextCaller parentReached group)))
      (CompactComplexScalarCountLifecycle.roleTimeConstant (block group)*
        (parentRows*2^shape.bits*2^polynomialExponent)*(ButterflyGuard.halfWidth metadataPrecision shape.bits+2)) ∧
    ∃ nextReached : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume returnedVolume (group.val+1)
      (parentLive+(gates group).length) pcStack origin calls (output v (nextCaller parentReached group)),
      nextReached.data=execute (block group) parentReached.data ∧
      ∀ (row : Fin (parentRows/roles)) (polynomialIndex : Fin (2^polynomialExponent)) (anchor : BinaryWalsh.Address shape.bits),
        stored phaseCoordinate visit (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits) (parentLive+(gates group).length)
          nextReached.data row polynomialIndex anchor=
        FramedFactorExecution.run
          (CompactComplexActualInterleavedNetwork.instructions (arity^(childExponent+1)) (.scalar group))
          (stored phaseCoordinate visit (parentRows/roles) polynomialExponent (metadataPrecision-2*shape.bits) parentLive parentReached.data row polynomialIndex anchor) := by
  obtain ⟨scalarRuns,nextReached,dataEquation⟩ := CompactComplexSourceReadyReachedEventInvariant.scalar_successor
    path group parentReached rowsPositive guardPositive chunkPositive activePositive precisionReserve axesFit chunkRoom growthReserve baselineFits denominatorRoom
  refine ⟨scalarRuns,nextReached,dataEquation,?_⟩
  intro row polynomialIndex anchor
  exact reached_scalar_semantics path phaseCoordinate visit group parentReached nextReached dataEquation activePositive precisionReserve axesFit growthReserve chunkRoom row polynomialIndex anchor

end Reached
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyScalarEventSemantics
