module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyChildEventSemantics
public import IntegerMultBounds.Machine.CompactComplexCorrectedStoppedChildGridSemantics

/-! A stopped child's literal installed array discharges the tensor premise
of the original child-event semantics. The result is computed by the actual
forward leaf and both call orientations, rather than supplied by an oracle. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedChildTensor
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Width Grid half)
open CompactComplexActualBasisPullback (nativeField)
open CompactComplexStoppedLeafTensorSemantics (slice)
open CompactComplexNonleafChildAddress (address)
open CompactComplexSourceReadyOrientationInvariants (oriented)
open CompactComplexCorrectedStoppedChildGridSemantics (installed)
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites

/-- The actual oriented stopped leaf computes the genuine forward or inverse
child tensor at every global address, with all outer spectators retained. -/
theorem installed_native_tensor {shape : Shape} {childLeft childExponent : ℕ}
    (call : ComplexRecursiveCallSchema.Call) (rows polynomialExponent precision live numeratorBound : ℕ)
    (phaseCoordinate : Fin shape.chunk) (childVisit : Visit shape.active childLeft (childExponent + 1))
    (inputArray : Array shape rows polynomialExponent)
    (inputWidth : Width shape rows polynomialExponent precision inputArray)
    (inputGrid : Grid shape rows polynomialExponent precision live numeratorBound inputArray)
    (signedGuard : 4 * (numeratorBound * 4 ^ (arity ^ (childExponent + 1))) < 2 ^ half shape precision)
    (row : Fin rows) (polynomialIndex : Fin (2 ^ polynomialExponent))
    (globalAddress : BinaryWalsh.Address shape.bits) :
    nativeField precision (live + arity ^ (childExponent + 1))
      (installed call rows polynomialExponent precision phaseCoordinate childVisit (oriented call inputArray))
      row polynomialIndex globalAddress =
      if call.inverse then (ComplexEndpoints.fullFrame (arity ^ childExponent)).symm
        (slice phaseCoordinate childVisit globalAddress (nativeField precision live inputArray row polynomialIndex))
        (address phaseCoordinate childVisit globalAddress)
      else ComplexEndpoints.fullFrame (arity ^ childExponent)
        (slice phaseCoordinate childVisit globalAddress (nativeField precision live inputArray row polynomialIndex))
        (address phaseCoordinate childVisit globalAddress) := by
  have sliceTensor := (CompactComplexStoppedLeafTensorSemantics.stopped_leaf_tensor_guarded
    call rows polynomialExponent precision live numeratorBound phaseCoordinate childVisit inputArray
    inputWidth inputGrid signedGuard row polynomialIndex globalAddress).2
  have pointTensor := congrFun sliceTensor (address phaseCoordinate childVisit globalAddress)
  have inputField : nativeField precision live inputArray row polynomialIndex =
      (fun globalIndex => CompactSpectatorInheritedGrid.decoded shape rows polynomialExponent precision live inputArray
        (RecursiveInterchangeRows.pack row (FlatCoordinateLayout.index globalIndex polynomialIndex))) := rfl
  rw [inputField]
  simpa only [CompactComplexStoppedLeafTensorSemantics.rowSlice,
    CompactComplexStoppedLeafTensorSemantics.slice, nativeField,
    CompactComplexNonleafChildAddress.insert_address, installed, ite_apply] using pointTensor

/-- On the actual forward basis array, stopped execution supplies ChildTensor
unconditionally from its inherited width/grid and signed guard. This is the
base case needed to remove recursive tensor premises from event induction. -/
theorem child_tensor {shape : Shape} {nodeLeft childExponent : ℕ}
    (phaseCoordinate : Fin shape.chunk) (parentVisit : Visit shape.active nodeLeft (childExponent + 2))
    (activeFits : shape.active ≤ shape.axes) (pair : BinaryRowProgram.Op (Fin arity))
    (rows polynomialExponent metadataPrecision : ℕ)
    (guardPositive : 1 ≤ shape.guard) (guardFitsChunk : shape.guard + 1 ≤ shape.chunk)
    (rowsPositive : 0 < rows) (call : ComplexRecursiveCallSchema.Call)
    (precision live numeratorBound : ℕ)
    (data : Fin CompactComplexScalarRowBlock.wireCount → Array shape rows polynomialExponent)
    (forwardWidth : Width shape rows polynomialExponent precision
      (CompactComplexSourceReadyReachedBasisInvariant.basisArray
        (CompactBinaryBasisSchedule.stage (CompactComplexRecursiveGeometry.node phaseCoordinate parentVisit activeFits) pair)
        rows polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive
        (CompactComplexActualBasisSlice.native_slots phaseCoordinate parentVisit activeFits pair
          rows polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive)
        (CompactComplexRolePhaseSite.pc call.site) false (data (CompactComplexScalarIntegerRows.wireIndex call.role))))
    (forwardGrid : Grid shape rows polynomialExponent precision live numeratorBound
      (CompactComplexSourceReadyReachedBasisInvariant.basisArray
        (CompactBinaryBasisSchedule.stage (CompactComplexRecursiveGeometry.node phaseCoordinate parentVisit activeFits) pair)
        rows polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive
        (CompactComplexActualBasisSlice.native_slots phaseCoordinate parentVisit activeFits pair
          rows polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive)
        (CompactComplexRolePhaseSite.pc call.site) false (data (CompactComplexScalarIntegerRows.wireIndex call.role))))
    (signedGuard : 4 * (numeratorBound * 4 ^ (arity ^ (childExponent + 1))) < 2 ^ half shape precision) :
    let forwardArray := CompactComplexSourceReadyReachedBasisInvariant.basisArray
      (CompactBinaryBasisSchedule.stage (CompactComplexRecursiveGeometry.node phaseCoordinate parentVisit activeFits) pair)
      rows polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive
      (CompactComplexActualBasisSlice.native_slots phaseCoordinate parentVisit activeFits pair
        rows polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive)
      (CompactComplexRolePhaseSite.pc call.site) false (data (CompactComplexScalarIntegerRows.wireIndex call.role))
    CompactComplexSourceReadyChildEventSemantics.ChildTensor phaseCoordinate parentVisit activeFits pair
      rows polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive call precision live
      (arity ^ (childExponent + 1)) data
      (installed call rows polynomialExponent precision phaseCoordinate
        (CompactComplexNonleafChildAddress.childVisit parentVisit call) (oriented call forwardArray)) := by
  dsimp only [CompactComplexSourceReadyChildEventSemantics.ChildTensor]
  intro row polynomialIndex globalAddress
  exact installed_native_tensor call rows polynomialExponent precision live numeratorBound phaseCoordinate
    (CompactComplexNonleafChildAddress.childVisit parentVisit call) _ forwardWidth forwardGrid signedGuard
    row polynomialIndex globalAddress

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedChildTensor
