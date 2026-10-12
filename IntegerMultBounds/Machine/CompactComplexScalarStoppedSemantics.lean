module

public import IntegerMultBounds.Machine.CompactComplexScalarPrefixRows
public import IntegerMultBounds.Machine.CompactComplexScalarSequenceGrid
public import IntegerMultBounds.Machine.CompactComplexCorrectedStoppedChildGridSemantics

/-! Complete mathematical composition of the actual scalar-prefix rows with
an oriented stopped tensor and literal spectator promotion. Original dependency
geometry derives signed guards; no post-prefix grid or semantic oracle is used.
Spectator equality compares with the completed scalar output. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexScalarStoppedSemantics
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Width Grid decoded half)
open CompactComplexScalarRowBlock (wireCount)
open CompactComplexScalarIntegerRows (wireIndex guardBits)
open CompactComplexScalarPrefixRows (prefixRows)
open CompactComplexScalarPolynomialSequence (execute)
open CompactComplexScalarSequenceSemantics (Bound values circuit)
open CompactComplexSourceReadyOrientationInvariants (oriented)
open CompactComplexCorrectedStoppedChildGridSemantics (installed)
open CompactComplexStoppedLeafTensorSemantics (rowSlice)
open Networks.ComplexRecursiveCallSchema (Call)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexFramedExecution.rows
  CompactFramedScalarGrid.rows prefixRows CompactComplexScalarIntegerRows.gates

variable {shape : Shape} {rowCount polynomialExponent leftBoundary childExponent : ℕ}

/-- Every original scalar group preceding the selected prefix is executed. -/
def scalarOutput (scalarPrefix : ℕ) (input : Fin wireCount → Array shape rowCount polynomialExponent) :=
  execute (prefixRows scalarPrefix) input

/-- The selected original role gets its pre/post-oriented leaf result, while
all other roles shift their actual signed numerators by the child volume. -/
def stoppedOutput (scalarPrefix : ℕ) (call : Call) (storagePrecision : ℕ)
    (rowCoordinate : Fin shape.chunk) (visit : Visit shape.active leftBoundary (childExponent+1))
    (input : Fin wireCount → Array shape rowCount polynomialExponent) :=
  CompactComplexNormalizedSpectatorHandoff.aligned shape rowCount polynomialExponent
    (arity^(childExponent+1)) (wireIndex call.role) (scalarOutput scalarPrefix input)
    (installed call rowCount polynomialExponent storagePrecision rowCoordinate visit
      (oriented call (scalarOutput scalarPrefix input (wireIndex call.role))))

private theorem growth_constant_ge_one : 1≤CompactFramedScalarGrid.growthConstant := by
  unfold CompactFramedScalarGrid.growthConstant
  exact Networks.GaussianPrecision.scalarBound_ge _ _ _ _

private theorem base_budget_le (baselinePrecision growthConstant dependencyLevels frameVolume returned axes : ℕ)
    (growthPositive : 1≤growthConstant) :
    CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*returned+axes)≤
      CompactComplexScalarPathGuard.budget baselinePrecision growthConstant dependencyLevels frameVolume returned axes := by
  have budgetEquation : CompactComplexScalarPathGuard.budget baselinePrecision growthConstant dependencyLevels frameVolume returned axes=
      CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*returned+axes)*growthConstant := by
    unfold CompactComplexScalarPathGuard.budget CompactRecursiveGridBudget.bound
    rw [pow_succ]
    ring
  rw [budgetEquation]
  exact Nat.le_mul_of_pos_right _ (lt_of_lt_of_le (by decide : 0<1) growthPositive)

/-- A whole arbitrary original scalar prefix, the corrected stopped tensor,
and every spectator have exact values on the derived returned grid and ledger.
This is a mathematical endpoint theorem; it does not assert a tape execution. -/
theorem stopped_call_values
    (scalarPrefix storagePrecision baselinePrecision growthConstant axes initialLive baselineLive : ℕ)
    {dependencyLevels frameVolume returned : ℕ}
    (entryPath : CompactRecursiveDependencyBudget.Path shape.active leftBoundary (childExponent+1)
      dependencyLevels frameVolume returned)
    (rowCoordinate : Fin shape.chunk) (call : Call)
    (childStopped : Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=true)
    (input : Fin wireCount → Array shape rowCount polynomialExponent)
    (inputWidth : ∀ role,Width shape rowCount polynomialExponent storagePrecision (input role))
    (inputGrid : ∀ role,Grid shape rowCount polynomialExponent storagePrecision initialLive
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*returned+axes)) (input role))
    (activePositive : 0<shape.active) (baselineFits : baselinePrecision≤storagePrecision)
    (axesFit : axes+arity^(childExponent+1)≤shape.bits)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (scalarChunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      (prefixRows scalarPrefix).length*guardBits≤shape.chunk)
    (leafChunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+guardBits≤shape.chunk)
    (initialLedger : initialLive≤CompactComplexDenominatorCapacity.ledger CompactComplexDenominatorCapacity.scalarRows
      baselineLive dependencyLevels frameVolume returned 0) :
    (∀ coefficient,values (half shape storagePrecision) (initialLive+(prefixRows scalarPrefix).length)
      (scalarOutput scalarPrefix input) coefficient=
      Networks.Circuit.run (circuit (prefixRows scalarPrefix)) (values (half shape storagePrecision) initialLive input coefficient)) ∧
    (∀ role,Width shape rowCount polynomialExponent storagePrecision (scalarOutput scalarPrefix input role) ∧
      Grid shape rowCount polynomialExponent storagePrecision (initialLive+(prefixRows scalarPrefix).length)
        (CompactFramedScalarGrid.bound scalarPrefix
          (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*returned+axes)))
        (scalarOutput scalarPrefix input role)) ∧
    (∀ role,Grid shape rowCount polynomialExponent storagePrecision
      (initialLive+(prefixRows scalarPrefix).length+arity^(childExponent+1))
      (CompactFramedScalarGrid.bound scalarPrefix
        (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels
          (frameVolume+2*(returned+arity^(childExponent+1))+axes)))
      (stoppedOutput scalarPrefix call storagePrecision rowCoordinate entryPath.visit input role)) ∧
    (∀ (row : Fin rowCount) (polynomialIndex : Fin (2^polynomialExponent)) (anchor : Networks.BinaryWalsh.Address shape.bits),
      rowSlice rowCount polynomialExponent storagePrecision (initialLive+(prefixRows scalarPrefix).length+arity^(childExponent+1))
        rowCoordinate entryPath.visit row polynomialIndex anchor
        (stoppedOutput scalarPrefix call storagePrecision rowCoordinate entryPath.visit input (wireIndex call.role))=
      if call.inverse then (Networks.ComplexEndpoints.fullFrame (arity^childExponent)).symm
        (rowSlice rowCount polynomialExponent storagePrecision (initialLive+(prefixRows scalarPrefix).length)
          rowCoordinate entryPath.visit row polynomialIndex anchor (scalarOutput scalarPrefix input (wireIndex call.role)))
      else Networks.ComplexEndpoints.fullFrame (arity^childExponent)
        (rowSlice rowCount polynomialExponent storagePrecision (initialLive+(prefixRows scalarPrefix).length)
          rowCoordinate entryPath.visit row polynomialIndex anchor (scalarOutput scalarPrefix input (wireIndex call.role)))) ∧
    (∀ role,role≠wireIndex call.role → decoded shape rowCount polynomialExponent storagePrecision
      (initialLive+(prefixRows scalarPrefix).length+arity^(childExponent+1))
      (stoppedOutput scalarPrefix call storagePrecision rowCoordinate entryPath.visit input role)=
      decoded shape rowCount polynomialExponent storagePrecision (initialLive+(prefixRows scalarPrefix).length)
        (scalarOutput scalarPrefix input role)) ∧
    initialLive+(prefixRows scalarPrefix).length+arity^(childExponent+1)≤
      CompactComplexDenominatorCapacity.ledger CompactComplexDenominatorCapacity.scalarRows baselineLive dependencyLevels
        frameVolume (returned+arity^(childExponent+1)) (CompactFramedScalarGrid.rows scalarPrefix).length := by
  let baseBound := CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*returned+axes)
  let prefixBound := CompactFramedScalarGrid.bound scalarPrefix baseBound
  let scalarLive := initialLive+(prefixRows scalarPrefix).length
  let childVolume := arity^(childExponent+1)
  have growthPositive : 1≤growthConstant := growth_constant_ge_one.trans growthReserve
  have budgetFits := base_budget_le baselinePrecision growthConstant dependencyLevels frameVolume returned axes growthPositive
  have signedBudget := CompactComplexScalarPathGuard.growth_power entryPath baselinePrecision growthConstant axes
  have inputWordWidth : ∀ role coefficient,(input role coefficient).1.length=half shape storagePrecision+1 ∧
      (input role coefficient).2.length=half shape storagePrecision+1 := by
    intro role coefficient
    simpa only [Width,ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using inputWidth role coefficient
  have inputBound : Bound (half shape storagePrecision) (CompactComplexScalarPathGuard.power shape baselinePrecision growthConstant axes) input := by
    intro role coefficient
    have represented := ButterflyGuard.represented_bound _ _ initialLive baseBound (inputGrid role coefficient)
    have numeratorReserve := Int.ofNat_le.mpr (budgetFits.trans signedBudget.le)
    exact ⟨represented.1.trans numeratorReserve,represented.2.trans numeratorReserve⟩
  have metadataReserve : baselinePrecision+2*shape.bits≤ButterflyIndependentGuardHeaders.reservation shape.bits storagePrecision := by
    unfold ButterflyIndependentGuardHeaders.reservation
    omega
  have scalarReserve := CompactComplexScalarRoleSemantics.stored_reserve shape baselinePrecision growthConstant axes
    (ButterflyIndependentGuardHeaders.reservation shape.bits storagePrecision) (prefixRows scalarPrefix).length
    activePositive metadataReserve (by omega) scalarChunkRoom
  rw [ButterflyIndependentGuardSemantics.half_eq] at scalarReserve
  have exactScalar := CompactComplexScalarSequenceSemantics.sequence_values (prefixRows scalarPrefix) input
    (half shape storagePrecision) (CompactComplexScalarPathGuard.power shape baselinePrecision growthConstant axes)
    initialLive inputWordWidth inputBound scalarReserve
  have scalarWordWidth := RawLinearCombinationComplexRowSequence.execute_width CompactComplexScalarRowBlock.wires_pos
    CompactComplexScalarPolynomialSequence.rows (prefixRows scalarPrefix) input (half shape storagePrecision+1) inputWordWidth
  have scalarWidth : ∀ role,Width shape rowCount polynomialExponent storagePrecision (scalarOutput scalarPrefix input role) := by
    intro role coefficient
    simpa only [scalarOutput,execute,Width,ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq]
      using scalarWordWidth role coefficient
  have scalarGrid : ∀ role,Grid shape rowCount polynomialExponent storagePrecision scalarLive prefixBound
      (scalarOutput scalarPrefix input role) := by
    intro role coefficient
    have numericalGrid := CompactComplexScalarSequenceGrid.sequence_grid (prefixRows scalarPrefix) input
      (half shape storagePrecision) (CompactComplexScalarPathGuard.power shape baselinePrecision growthConstant axes)
      initialLive baseBound inputWordWidth inputBound scalarReserve
      (fun wire position => inputGrid (wireIndex wire) position) coefficient (wireIndex.symm role)
    rw [CompactComplexScalarPrefixRows.prefix_circuit] at numericalGrid
    simpa only [scalarOutput,scalarLive,prefixBound,CompactFramedScalarGrid.bound,values,decoded,
      ButterflyStreamSemantics.decode,Equiv.apply_symm_apply] using numericalGrid
  have leafGuard := CompactComplexStoppedEventProgress.prefix_guard_from_path entryPath scalarPrefix baselinePrecision
    growthConstant axes childVolume (ButterflyIndependentGuardHeaders.reservation shape.bits storagePrecision)
    activePositive metadataReserve axesFit growthReserve leafChunkRoom
  simp only [ButterflyIndependentGuardHeaders.reservation,Nat.add_sub_cancel] at leafGuard
  change 4*(prefixBound*4^childVolume)<2^(half shape storagePrecision) at leafGuard
  have boundIncrease : prefixBound≤prefixBound*4^childVolume :=
    Nat.le_mul_of_pos_right _ (pow_pos (by decide) _)
  have orientedGrid := CompactComplexSourceReadyOrientedStoppedReturnPrefix.orientation_grid call shape rowCount polynomialExponent
    storagePrecision scalarLive prefixBound (scalarOutput scalarPrefix input (wireIndex call.role))
    (scalarWidth _) (scalarGrid _) (by omega)
  have orientedWidth := CompactComplexSourceReadyOrientationInvariants.oriented_width call shape rowCount polynomialExponent
    storagePrecision (scalarOutput scalarPrefix input (wireIndex call.role)) (scalarWidth _)
  have leafGrid := CompactSpectatorInheritedGrid.forward_grid shape rowCount polynomialExponent storagePrecision rowCoordinate
    entryPath.visit childVolume scalarLive prefixBound le_rfl _ orientedWidth orientedGrid.1 leafGuard
  have leafWidth := CompactSpectatorLeafLoop.width_run shape rowCount polynomialExponent
    (ButterflyIndependentGuardHeaders.reservation shape.bits storagePrecision) rowCoordinate entryPath.visit childVolume _ orientedWidth
  have installedGrid := CompactComplexSourceReadyOrientedStoppedReturnPrefix.orientation_grid call shape rowCount polynomialExponent
    storagePrecision (scalarLive+childVolume) (prefixBound*4^childVolume)
    (CompactSpectatorLeafGuardOriginal.result .forward shape rowCount polynomialExponent storagePrecision rowCoordinate entryPath.visit
      (oriented call (scalarOutput scalarPrefix input (wireIndex call.role)))) leafWidth leafGrid (by omega)
  have capacity : childVolume≤half shape storagePrecision+1 := by
    unfold childVolume half ButterflyGuard.halfWidth
    omega
  have promotionGuard : prefixBound*2^childVolume<2^(half shape storagePrecision) := by
    have powerFits := Nat.pow_le_pow_left (by decide : 2≤4) childVolume
    have promotedFits := Nat.mul_le_mul_left prefixBound powerFits
    omega
  have sharedGrid := CompactComplexChildGridAlignment.shared_grid shape rowCount polynomialExponent storagePrecision scalarLive
    prefixBound childVolume (wireIndex call.role) (scalarOutput scalarPrefix input)
    (stoppedOutput scalarPrefix call storagePrecision rowCoordinate entryPath.visit input) scalarGrid
    (by simpa only [stoppedOutput,CompactComplexNormalizedSpectatorHandoff.aligned,ite_true,installed] using installedGrid.1)
    (by
      intro role roleDistinct coefficient
      simp only [stoppedOutput,CompactComplexNormalizedSpectatorHandoff.aligned,ite_eq_right roleDistinct]
      exact CompactComplexChildGridPromoted.promotes shape rowCount polynomialExponent storagePrecision scalarLive prefixBound
        childVolume (scalarOutput scalarPrefix input role) (scalarWidth role) (scalarGrid role) capacity promotionGuard coefficient)
  have scalarLedger := CompactComplexRecursiveLiveProgress.scalar_segment_bound baselineLive dependencyLevels frameVolume
    returned 0 initialLive (prefixRows scalarPrefix) initialLedger
  have returnedLedger := CompactComplexDenominatorCapacity.returned_advance CompactComplexDenominatorCapacity.scalarRows
    baselineLive dependencyLevels frameVolume returned (prefixRows scalarPrefix).length scalarLive (scalarLive+childVolume)
    childVolume (by simpa only [scalarLive,Nat.zero_add] using scalarLedger) (by omega)
  refine ⟨exactScalar,fun role => ⟨scalarWidth role,scalarGrid role⟩,?_,?_,sharedGrid.2,?_⟩
  · intro role coefficient
    exact Networks.GaussianPrecision.bound_mono
      (CompactComplexStoppedEventProgress.prefix_return_bound scalarPrefix baselinePrecision growthConstant dependencyLevels
        frameVolume returned axes childVolume) (sharedGrid.1 role coefficient)
  · intro row polynomialIndex anchor
    have targetTensor := CompactComplexStoppedLeafTensorSemantics.stopped_leaf_tensor_guarded call rowCount polynomialExponent
      storagePrecision scalarLive prefixBound rowCoordinate entryPath.visit
      (scalarOutput scalarPrefix input (wireIndex call.role)) (scalarWidth _) (scalarGrid _) leafGuard row polynomialIndex anchor
    simpa only [stoppedOutput,CompactComplexNormalizedSpectatorHandoff.aligned,ite_true,installed] using targetTensor.2
  · simpa only [scalarLive,childVolume,CompactComplexScalarPrefixRows.prefix_length] using returnedLedger

end
end IntegerMultBounds.Machine.CompactComplexScalarStoppedSemantics
