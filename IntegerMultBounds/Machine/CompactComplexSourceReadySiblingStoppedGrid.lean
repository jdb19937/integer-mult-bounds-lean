module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedReturnGrid
public import IntegerMultBounds.Machine.CompactComplexCorrectedStoppedChildGridSemantics
public import IntegerMultBounds.Machine.CompactComplexSourceReadySiblingGuards

/-! The actual stopped result has its parent scalar-prefix grid after counted
sibling returns. All signed guards use the original entry dependency Path;
the current returned cursor is numerical accounting, not another Path. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadySiblingStoppedGrid
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
open CompactComplexSourceReadyReachedReturnInvariant (roleData)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open CompactComplexCompletedLiveLower (schedule childNames)
open CompactSpectatorInheritedGrid (Grid half)
attribute [local irreducible] Networks.ComplexRank25.program
  CompactComplexRolePhaseSite.roleCount schedule

/-- The original retained width pays the stopped leaf and both conjugations,
including every actually processed sibling's numerator growth. -/
theorem stopped_guard {shape : Shape}
    {nodeLeft nodeExponent dependencyLevels frameVolume entryReturned : ℕ}
    (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft nodeExponent
      dependencyLevels frameVolume entryReturned)
    (eventIndex childVolume scalarPrefix baselinePrecision growthConstant completedAxes
      denominatorAdvance metadataPrecision : ℕ)
    (childFitsNode : childVolume ≤ arity ^ nodeExponent)
    (activePositive : 0 < shape.active)
    (precisionReserve : baselinePrecision + 2 * shape.bits ≤ metadataPrecision)
    (axesFit : completedAxes + denominatorAdvance ≤ shape.bits)
    (growthReserve : CompactFramedScalarGrid.growthConstant ≤ growthConstant)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant +
      Nat.clog 2 (growthConstant + 1) + CompactComplexScalarIntegerRows.guardBits ≤ shape.chunk) :
    4 * (CompactFramedScalarGrid.bound scalarPrefix
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels
        (frameVolume + 2 * returnedCursor entryReturned eventIndex childVolume + completedAxes)) *
      4 ^ denominatorAdvance) < 2 ^ half shape (metadataPrecision - 2 * shape.bits) := by
  have prefixBound := CompactFramedScalarGrid.bound_le scalarPrefix
    (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels
      (frameVolume + 2 * returnedCursor entryReturned eventIndex childVolume + completedAxes))
    growthConstant growthReserve
  have budgetEquation : CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels
      (frameVolume + 2 * returnedCursor entryReturned eventIndex childVolume + completedAxes) *
      growthConstant * 4 ^ denominatorAdvance = CompactComplexScalarPathGuard.budget
        baselinePrecision growthConstant dependencyLevels frameVolume
        (returnedCursor entryReturned eventIndex childVolume) (completedAxes + denominatorAdvance) := by
    unfold CompactComplexScalarPathGuard.budget CompactRecursiveGridBudget.bound
    rw [pow_succ, pow_add, pow_add]
    ring
  have growthPower := CompactComplexSourceReadyEventScheduleSemantics.sibling_growth_power entryPath
    (childNames (schedule.take eventIndex)).length childVolume baselinePrecision growthConstant
    (completedAxes + denominatorAdvance)
    (CompactComplexSourceReadyEventScheduleSemantics.processed_calls_le_capacity eventIndex) childFitsNode
  change CompactComplexScalarPathGuard.budget baselinePrecision growthConstant dependencyLevels frameVolume
    (returnedCursor entryReturned eventIndex childVolume) (completedAxes + denominatorAdvance) < _ at growthPower
  have storedReserve := CompactComplexScalarPathGuard.stored_guard shape baselinePrecision growthConstant
    (completedAxes + denominatorAdvance) metadataPrecision activePositive precisionReserve axesFit chunkRoom
  have twoGuardBits : 2 ≤ CompactComplexScalarIntegerRows.guardBits := by
    unfold CompactComplexScalarIntegerRows.guardBits
    have growthAtLeastThree : 3 ≤ CompactComplexScalarIntegerRows.growthConstant + 1 := by
      unfold CompactComplexScalarIntegerRows.growthConstant
      omega
    have growthFits := Nat.le_pow_clog (by decide : 1 < 2)
      (CompactComplexScalarIntegerRows.growthConstant + 1)
    by_contra fewerBits
    have bitsAtMostOne : Nat.clog 2 (CompactComplexScalarIntegerRows.growthConstant + 1) ≤ 1 := by omega
    have powerAtMostTwo := Nat.pow_le_pow_right (by decide : 0 < 2) bitsAtMostOne
    norm_num at powerAtMostTwo
    omega
  have metadataFits : 2 * shape.bits ≤ metadataPrecision := by omega
  have halfEquation := CompactComplexSourceReadyReachedReturnInvariant.inherited_half_eq metadataFits
  have storedPowerFits : CompactComplexScalarPathGuard.power shape baselinePrecision growthConstant
      (completedAxes + denominatorAdvance) + 2 ≤ half shape (metadataPrecision - 2 * shape.bits) := by
    rw [halfEquation]
    omega
  calc
    _ ≤ 4 * (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels
        (frameVolume + 2 * returnedCursor entryReturned eventIndex childVolume + completedAxes) *
        growthConstant * 4 ^ denominatorAdvance) :=
      Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right _ prefixBound)
    _ = 4 * CompactComplexScalarPathGuard.budget baselinePrecision growthConstant dependencyLevels
        frameVolume (returnedCursor entryReturned eventIndex childVolume) (completedAxes + denominatorAdvance) := by
      rw [budgetEquation]
    _ < 4 * 2 ^ CompactComplexScalarPathGuard.power shape baselinePrecision growthConstant
        (completedAxes + denominatorAdvance) := Nat.mul_lt_mul_of_pos_left growthPower (by decide)
    _ = 2 ^ (CompactComplexScalarPathGuard.power shape baselinePrecision growthConstant
        (completedAxes + denominatorAdvance) + 2) := by rw [pow_add]; ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) storedPowerFits

section Parent
variable {extraTapes : ℕ} {shape : Shape} {stage : ActivePrefixStageParameters.Stage shape}
    {nodeLeft nodeExponent dependencyLevels frameVolume entryReturned eventIndex childVolume : ℕ}
    {parentRows polynomialExponent metadataPrecision baselinePrecision growthConstant completedAxes
      baselineLive scalarPrefix parentLive : ℕ}
    {pcStack : Fin extraTapes} {origin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
    {parentBank : Tapes (nodeTapes extraTapes roles) 2}
    (parentReached : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent
      baselinePrecision growthConstant completedAxes baselineLive dependencyLevels frameVolume
      (returnedCursor entryReturned eventIndex childVolume) scalarPrefix parentLive pcStack origin savedCalls parentBank)

/-- The literal pre-oriented leaf and post-orientation install the exact grid
required by parent return, with the true one-volume denominator advance. -/
theorem installed_grid {childLeft childExponent : ℕ}
    (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft nodeExponent
      dependencyLevels frameVolume entryReturned)
    (call : Networks.ComplexRecursiveCallSchema.Call) (phaseCoordinate : Fin shape.chunk)
    (childVisit : Visit shape.active childLeft (childExponent + 1))
    (childFitsNode : childVolume ≤ arity ^ nodeExponent)
    (activePositive : 0 < shape.active)
    (precisionReserve : baselinePrecision + 2 * shape.bits ≤ metadataPrecision)
    (axesFit : completedAxes + arity ^ (childExponent + 1) ≤ shape.bits)
    (growthReserve : CompactFramedScalarGrid.growthConstant ≤ growthConstant)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant +
      Nat.clog 2 (growthConstant + 1) + CompactComplexScalarIntegerRows.guardBits ≤ shape.chunk) :
    Grid shape (parentRows / roles) polynomialExponent (metadataPrecision - 2 * shape.bits)
      (parentLive + arity ^ (childExponent + 1))
      (CompactFramedScalarGrid.bound scalarPrefix
        (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels
          (frameVolume + 2 * (returnedCursor entryReturned eventIndex childVolume +
            arity ^ (childExponent + 1)) + completedAxes)))
      (CompactComplexCorrectedStoppedChildGridSemantics.installed call (parentRows / roles)
        polynomialExponent (metadataPrecision - 2 * shape.bits) phaseCoordinate childVisit
        (CompactComplexSourceReadyOrientationInvariants.oriented call
          (roleData parentReached (CompactComplexRolePhaseSite.role call.site)))) := by
  let precision := metadataPrecision - 2 * shape.bits
  let advance := arity ^ (childExponent + 1)
  let numeratorBound := CompactFramedScalarGrid.bound scalarPrefix
    (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels
      (frameVolume + 2 * returnedCursor entryReturned eventIndex childVolume + completedAxes))
  let originalArray := roleData parentReached (CompactComplexRolePhaseSite.role call.site)
  let orientedArray := CompactComplexSourceReadyOrientationInvariants.oriented call originalArray
  let leafArray := CompactSpectatorLeafGuardOriginal.result .forward shape (parentRows / roles)
    polynomialExponent precision phaseCoordinate childVisit orientedArray
  have metadataFits : 2 * shape.bits ≤ metadataPrecision := by omega
  have originalWidth := CompactComplexSourceReadyReachedReturnInvariant.role_width parentReached metadataFits
    (CompactComplexRolePhaseSite.role call.site)
  have originalGrid := CompactComplexSourceReadyReachedReturnInvariant.role_grid parentReached metadataFits
    (CompactComplexRolePhaseSite.role call.site)
  have signedGuard := stopped_guard entryPath eventIndex childVolume scalarPrefix baselinePrecision growthConstant
    completedAxes advance metadataPrecision childFitsNode activePositive precisionReserve axesFit growthReserve chunkRoom
  change 4 * (numeratorBound * 4 ^ advance) < 2 ^ half shape precision at signedGuard
  have boundFits : numeratorBound ≤ numeratorBound * 4 ^ advance :=
    Nat.le_mul_of_pos_right numeratorBound (pow_pos (by decide) advance)
  have inputGrid := CompactComplexSourceReadyOrientedStoppedReturnPrefix.orientation_grid call shape
    (parentRows / roles) polynomialExponent precision parentLive numeratorBound originalArray
    originalWidth originalGrid (by omega)
  have inputWidth := CompactComplexSourceReadyOrientationInvariants.oriented_width call shape
    (parentRows / roles) polynomialExponent precision originalArray originalWidth
  have leafGrid : Grid shape (parentRows / roles) polynomialExponent precision
      (parentLive + advance) (numeratorBound * 4 ^ advance) leafArray :=
    CompactSpectatorInheritedGrid.forward_grid shape (parentRows / roles) polynomialExponent precision
      phaseCoordinate childVisit advance parentLive numeratorBound le_rfl orientedArray inputWidth inputGrid.1 signedGuard
  have leafWidth := CompactSpectatorLeafLoop.width_run shape (parentRows / roles) polynomialExponent
    (ButterflyIndependentGuardHeaders.reservation shape.bits precision) phaseCoordinate childVisit advance orientedArray inputWidth
  have outputGrid := CompactComplexSourceReadyOrientedStoppedReturnPrefix.orientation_grid call shape
    (parentRows / roles) polynomialExponent precision (parentLive + advance) (numeratorBound * 4 ^ advance)
    leafArray leafWidth leafGrid (by omega)
  intro coefficient
  exact Networks.GaussianPrecision.bound_mono
    (CompactComplexStoppedEventProgress.prefix_return_bound scalarPrefix baselinePrecision growthConstant
      dependencyLevels frameVolume (returnedCursor entryReturned eventIndex childVolume) completedAxes advance)
    (outputGrid.1 coefficient)

end Parent
end
end IntegerMultBounds.Machine.CompactComplexSourceReadySiblingStoppedGrid
