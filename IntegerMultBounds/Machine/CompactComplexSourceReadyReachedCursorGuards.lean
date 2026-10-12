module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventTrace
public import IntegerMultBounds.Machine.CompactComplexSourceReadySiblingScalarPath

/-! Signed and live-field capacities at every actual reached schedule cursor,
including the terminal cursor. All bounds use the original entry dependency
Path and actual scalar-prefix/sibling accounting, without an advanced Path. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedCursorGuards
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexSourceReadyReachedEventTrace (State)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexActualScalarOrdinal (scalarGroups)
open CompactComplexCompletedLiveLower (schedule childNames)
open CompactComplexDenominatorCapacity (ledger scalarRows)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexFramedExecution.rows
  Networks.ComplexRecursiveCallSchema.sites Networks.ComplexRecursiveCallSchema.calls schedule
  CompactComplexRolePhaseSite.roleCount scalarRows CompactRecursiveDependencyBudget.volumeCoefficient
  CompactRecursiveDependencyBudget.callCapacity

private theorem ledger_capacity_arithmetic
    (active rowBound volumeCoefficient dependencyLevels frameVolume returnedVolume usedRows
      baselineLive baselinePrecision live metadataPrecision bitCount : ℕ)
    (levelsFit : dependencyLevels+1≤active)
    (volumesFit : frameVolume+2*returnedVolume≤volumeCoefficient*active)
    (rowsFit : usedRows≤rowBound)
    (liveLedger : live≤baselineLive+dependencyLevels*rowBound+frameVolume+2*returnedVolume+usedRows)
    (roomFits : (rowBound+volumeCoefficient+2)*active≤bitCount)
    (baselineFits : baselineLive≤baselinePrecision)
    (precisionReserve : baselinePrecision+2*bitCount≤metadataPrecision) :
    live≤ButterflyGuard.halfWidth metadataPrecision bitCount+1 := by
  have levelCharge := Nat.mul_le_mul_right rowBound levelsFit
  have liveBound : live≤baselineLive+(rowBound+volumeCoefficient)*active := by nlinarith
  unfold ButterflyGuard.halfWidth
  nlinarith

private theorem active_chunk_le_bits (shape : Shape) : shape.active*shape.chunk≤shape.bits := by
  unfold Shape.bits
  omega

private theorem room_eq (rowBound : ℕ) : CompactComplexDenominatorCapacity.room rowBound=
    rowBound+CompactRecursiveDependencyBudget.volumeCoefficient+2 := rfl

section Node
variable {stackCount : ℕ} {shape : Shape} {stage : ActivePrefixStageParameters.Stage shape}
  {nodeLeft rowCount polynomialExponent metadataPrecision baselinePrecision growthConstant completedAxes baselineLive
    dependencyLevels frameVolume entryReturned childExponent eventIndex live : ℕ}
  {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
  (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+1)
    dependencyLevels frameVolume entryReturned)
  (state : State (stage:=stage) (rowCount:=rowCount) (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=metadataPrecision) (baselinePrecision:=baselinePrecision)
      (growthConstant:=growthConstant) (completedAxes:=completedAxes) (baselineLive:=baselineLive)
      (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume) (entryReturned:=entryReturned)
      (childExponent:=childExponent) (pcStack:=pcStack) (origin:=origin) (savedCalls:=savedCalls) eventIndex live)

include entryPath state

/-- The exact numerator bound of this actual reached prefix fits its inherited
signed half-width, even after all scalar groups and all children have run. -/
theorem signed_grid_reserve
    (activePositive : 0<shape.active)
    (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision) (axesFit : completedAxes≤shape.bits)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      CompactComplexScalarIntegerRows.guardBits≤shape.chunk) :
    CompactFramedScalarGrid.bound (scalarGroups (schedule.take eventIndex)).length
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels
        (frameVolume+2*returnedCursor entryReturned eventIndex (arity^childExponent)+completedAxes))<
      2^(CompactSpectatorInheritedGrid.half shape (metadataPrecision-2*shape.bits)) := by
  have prefixBound := CompactFramedScalarGrid.bound_le (scalarGroups (schedule.take eventIndex)).length
    (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels
      (frameVolume+2*returnedCursor entryReturned eventIndex (arity^childExponent)+completedAxes)) growthConstant growthReserve
  have budgetBound : CompactFramedScalarGrid.bound (scalarGroups (schedule.take eventIndex)).length
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels
        (frameVolume+2*returnedCursor entryReturned eventIndex (arity^childExponent)+completedAxes))≤
      CompactComplexScalarPathGuard.budget baselinePrecision growthConstant dependencyLevels frameVolume
        (returnedCursor entryReturned eventIndex (arity^childExponent)) completedAxes :=
    prefixBound.trans_eq (CompactRecursiveGridBudget.scalar_step baselinePrecision growthConstant dependencyLevels _)
  have childFitsNode : arity^childExponent≤arity^(childExponent+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have growthPower := CompactComplexSourceReadyEventScheduleSemantics.sibling_growth_power entryPath
    (childNames (schedule.take eventIndex)).length (arity^childExponent) baselinePrecision growthConstant completedAxes
    (CompactComplexSourceReadyEventScheduleSemantics.processed_calls_le_capacity eventIndex) childFitsNode
  change CompactComplexScalarPathGuard.budget baselinePrecision growthConstant dependencyLevels frameVolume
    (returnedCursor entryReturned eventIndex (arity^childExponent)) completedAxes<
    2^(CompactComplexScalarPathGuard.power shape baselinePrecision growthConstant completedAxes) at growthPower
  have storedReserve := CompactComplexScalarPathGuard.stored_guard shape baselinePrecision growthConstant completedAxes
    metadataPrecision activePositive precisionReserve axesFit chunkRoom
  have metadataFits : 2*shape.bits≤metadataPrecision := by omega
  have powerFits : CompactComplexScalarPathGuard.power shape baselinePrecision growthConstant completedAxes≤
      CompactSpectatorInheritedGrid.half shape (metadataPrecision-2*shape.bits) := by
    rw [CompactComplexSourceReadyReachedReturnInvariant.inherited_half_eq metadataFits]
    omega
  exact (budgetBound.trans_lt growthPower).trans_le (Nat.pow_le_pow_right (by decide) powerFits)

/-- The literal live descriptor fits the retained field at every prefix.
Actual scalar rows and counted siblings pay the same original room reserve. -/
theorem current_capacity (baselineFits : baselineLive≤baselinePrecision)
    (precisionReserve : baselinePrecision+2*shape.bits≤metadataPrecision)
    (denominatorRoom : CompactComplexDenominatorCapacity.room scalarRows≤shape.chunk) :
    live≤ButterflyGuard.halfWidth metadataPrecision shape.bits+1 := by
  have levelPotential := entryPath.levels_le
  have nodeVolumePositive : 0<arity^(childExponent+1) := pow_pos (by decide) _
  have levelsFit : dependencyLevels+1≤shape.active :=
    Nat.succ_le_of_lt ((Nat.lt_add_of_pos_right nodeVolumePositive).trans_le levelPotential)
  have childFitsNode : arity^childExponent≤arity^(childExponent+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have volumesFit := CompactComplexSourceReadyEventScheduleSemantics.schedule_prefix_volume_bound
    entryPath eventIndex (arity^childExponent) childFitsNode
  change frameVolume+2*returnedCursor entryReturned eventIndex (arity^childExponent)≤
    CompactRecursiveDependencyBudget.volumeCoefficient*shape.active at volumesFit
  have rowsFit := CompactComplexDenominatorCapacity.actual_prefix (scalarGroups (schedule.take eventIndex)).length
  have liveLedger := state.reached.upper_ledger
  unfold ledger at liveLedger
  have roomCharge := Nat.mul_le_mul_right shape.active denominatorRoom
  have roomFits : CompactComplexDenominatorCapacity.room scalarRows*shape.active≤shape.bits :=
    roomCharge.trans ((Nat.le_of_eq (Nat.mul_comm _ _)).trans (active_chunk_le_bits shape))
  rw [room_eq] at roomFits
  exact ledger_capacity_arithmetic shape.active scalarRows CompactRecursiveDependencyBudget.volumeCoefficient
    dependencyLevels frameVolume (returnedCursor entryReturned eventIndex (arity^childExponent))
    (CompactFramedScalarGrid.rows (scalarGroups (schedule.take eventIndex)).length).length
    baselineLive baselinePrecision live metadataPrecision shape.bits levelsFit volumesFit rowsFit liveLedger
    roomFits baselineFits precisionReserve

end Node
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedCursorGuards
