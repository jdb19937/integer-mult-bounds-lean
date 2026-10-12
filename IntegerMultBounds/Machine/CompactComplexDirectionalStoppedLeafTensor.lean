module

public import IntegerMultBounds.Machine.CompactComplexStoppedLeafTensorSemantics

/-! Exact tensor semantics of the literal directional stopped-leaf arrays.
The inverse machine is identified through its actual negated kernel list;
its physical endpoint is kept, rather than replaced by a conjugated array. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexDirectionalStoppedLeafTensor
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactSpectatorLeafGuardOriginal (Direction)
open CompactSpectatorInheritedGrid (Width Grid half)
open CompactComplexStoppedLeafTensorSemantics (slice rowSlice forward_kernel_tensor)
variable {shape : Shape} {nodeLeft childExponent : ℕ}
attribute [local irreducible] arity Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites

private theorem slice_conjugate (phaseCoordinate : Fin shape.chunk)
    (childVisit : Visit shape.active nodeLeft (childExponent+1))
    (anchor : BinaryWalsh.Address shape.bits) (values : BinaryWalsh.Arrays shape.bits) :
    slice phaseCoordinate childVisit anchor (BinaryWalshComplexConjugation.conjugate values)=
      BinaryColumnConjugation.conjugate (slice phaseCoordinate childVisit anchor values) := rfl

/-- The literal inverse leaf kernels induce the inverse child tensor on
all anchored slices, retaining the same surrounding physical coordinates. -/
private theorem inverse_kernel_tensor (phaseCoordinate : Fin shape.chunk)
    (childVisit : Visit shape.active nodeLeft (childExponent+1))
    (anchor : BinaryWalsh.Address shape.bits) (values : BinaryWalsh.Arrays shape.bits) :
    slice phaseCoordinate childVisit anchor (BinaryWalsh.kernelRun
      (BinaryWalsh.negateKernels (CompactSpectatorLeafSemantics.directions shape phaseCoordinate childVisit
        (arity^(childExponent+1)) le_rfl)) values)=
      (ComplexEndpoints.fullFrame (arity^childExponent)).symm (slice phaseCoordinate childVisit anchor values) := by
  rw [BinaryWalshComplexConjugation.inverse_phase_run,slice_conjugate,forward_kernel_tensor,slice_conjugate]
  have inverseFrame := BinaryColumnConjugation.frame_conjugate BinaryPhase.weightPhase
    (BinaryColumnConjugation.conjugate (slice phaseCoordinate childVisit anchor values))
  simpa only [ComplexEndpoints.fullFrame,BinaryColumnConjugation.conjugate_twice] using inverseFrame

/-- Both actual directional endpoints have the exact child tensor action,
with their true one-volume live advance and inherited guarded output grid. -/
theorem directional_result_guarded (direction : Direction)
    (rows polynomialExponent precision initialLive numeratorBound : ℕ) (phaseCoordinate : Fin shape.chunk)
    (childVisit : Visit shape.active nodeLeft (childExponent+1))
    (inputArray : CompactSpectatorVisitGeometry.Array shape rows polynomialExponent)
    (inputWidth : Width shape rows polynomialExponent precision inputArray)
    (inputGrid : Grid shape rows polynomialExponent precision initialLive numeratorBound inputArray)
    (signedGuard : 4*(numeratorBound*4^(arity^(childExponent+1)))<2^(half shape precision))
    (row : Fin rows) (polynomialIndex : Fin (2^polynomialExponent)) (anchor : BinaryWalsh.Address shape.bits) :
    let result := CompactSpectatorLeafGuardOriginal.result direction shape rows polynomialExponent precision
      phaseCoordinate childVisit inputArray
    Grid shape rows polynomialExponent precision (initialLive+arity^(childExponent+1))
      (numeratorBound*4^(arity^(childExponent+1))) result ∧
    rowSlice rows polynomialExponent precision (initialLive+arity^(childExponent+1)) phaseCoordinate childVisit
      row polynomialIndex anchor result=
      if direction=.inverse then (ComplexEndpoints.fullFrame (arity^childExponent)).symm
        (rowSlice rows polynomialExponent precision initialLive phaseCoordinate childVisit row polynomialIndex anchor inputArray)
      else ComplexEndpoints.fullFrame (arity^childExponent)
        (rowSlice rows polynomialExponent precision initialLive phaseCoordinate childVisit row polynomialIndex anchor inputArray) := by
  dsimp only
  cases direction with
  | forward =>
    rw [if_neg (by decide : Direction.forward≠Direction.inverse)]
    exact CompactComplexStoppedLeafTensorSemantics.forward_result_guarded rows polynomialExponent precision
      initialLive numeratorBound phaseCoordinate childVisit inputArray inputWidth inputGrid signedGuard row polynomialIndex anchor
  | inverse =>
    rw [if_pos rfl]
    have directional := CompactSpectatorInheritedGrid.directional_semantics shape rows polynomialExponent precision
      phaseCoordinate childVisit .inverse initialLive numeratorBound inputArray inputWidth inputGrid signedGuard row polynomialIndex
    refine ⟨directional.1,?_⟩
    have restricted := congrArg (slice phaseCoordinate childVisit anchor) directional.2
    change rowSlice rows polynomialExponent precision (initialLive+arity^(childExponent+1)) phaseCoordinate childVisit
      row polynomialIndex anchor (CompactSpectatorLeafGuardOriginal.result .inverse shape rows polynomialExponent precision
        phaseCoordinate childVisit inputArray)=
      slice phaseCoordinate childVisit anchor (BinaryWalsh.kernelRun
        (BinaryWalsh.negateKernels (CompactSpectatorLeafSemantics.directions shape phaseCoordinate childVisit
          (arity^(childExponent+1)) le_rfl))
        (fun address => CompactSpectatorInheritedGrid.decoded shape rows polynomialExponent precision initialLive inputArray
          (RecursiveInterchangeRows.pack row (FlatCoordinateLayout.index address polynomialIndex)))) at restricted
    rw [inverse_kernel_tensor] at restricted
    exact restricted

/-- The real child dependency Path supplies the signed guard for the same
literal directional machine, without a tensor execution or equality premise. -/
theorem directional_result_from_path (direction : Direction)
    (rows polynomialExponent precision initialLive baselinePrecision growthConstant : ℕ)
    (phaseCoordinate : Fin shape.chunk) {dependencyLevels frameVolume returnedVolume : ℕ}
    (childPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+1)
      dependencyLevels frameVolume returnedVolume)
    (baselineFits : baselinePrecision≤precision)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant≤shape.chunk)
    (inputArray : CompactSpectatorVisitGeometry.Array shape rows polynomialExponent)
    (inputWidth : Width shape rows polynomialExponent precision inputArray)
    (inputGrid : Grid shape rows polynomialExponent precision initialLive
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*returnedVolume)) inputArray)
    (row : Fin rows) (polynomialIndex : Fin (2^polynomialExponent)) (anchor : BinaryWalsh.Address shape.bits) :
    let result := CompactSpectatorLeafGuardOriginal.result direction shape rows polynomialExponent precision
      phaseCoordinate childPath.visit inputArray
    Grid shape rows polynomialExponent precision (initialLive+arity^(childExponent+1))
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*returnedVolume)*
        4^(arity^(childExponent+1))) result ∧
    rowSlice rows polynomialExponent precision (initialLive+arity^(childExponent+1)) phaseCoordinate childPath.visit
      row polynomialIndex anchor result=
      if direction=.inverse then (ComplexEndpoints.fullFrame (arity^childExponent)).symm
        (rowSlice rows polynomialExponent precision initialLive phaseCoordinate childPath.visit row polynomialIndex anchor inputArray)
      else ComplexEndpoints.fullFrame (arity^childExponent)
        (rowSlice rows polynomialExponent precision initialLive phaseCoordinate childPath.visit row polynomialIndex anchor inputArray) := by
  have signedGuard := CompactSpectatorInheritedGrid.guard_from_path shape precision childPath baselinePrecision growthConstant
    (arity^(childExponent+1)) baselineFits chunkRoom (CompactSpectatorLeafSemantics.count_le_bits shape phaseCoordinate childPath.visit)
  exact directional_result_guarded direction rows polynomialExponent precision initialLive _ phaseCoordinate childPath.visit
    inputArray inputWidth inputGrid signedGuard row polynomialIndex anchor

end
end IntegerMultBounds.Machine.CompactComplexDirectionalStoppedLeafTensor
