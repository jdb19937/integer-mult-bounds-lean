module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedRoleRejoin
public import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafOrientedSemantics
public import IntegerMultBounds.Machine.CompactComplexSourceReadyChildEventSemantics

/-! The normalized recursive node theorem computes the forward tensor on the
literal preoriented child input. Post-orientation changes this to the original
call's forward or inverse tensor, with the raw row and spectator addresses
unchanged. The only tensor premise is the recursive normalized-node identity. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafChildTensor
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Width Grid decoded)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactComplexSourceReadyOrientationInvariants (oriented)
open CompactComplexSourceReadyReachedStoppedNodeNormalizedValues (normalized)
open CompactComplexActualBasisPullback (nativeField)
open CompactComplexStoppedLeafTensorSemantics (slice)
open CompactComplexNonleafChildAddress (insert address)
open RecursiveInterchangeRows (pack)
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites
  CompactComplexRolePhaseSite.roleCount CompactComplexRolePhaseSite.roleEncoding
  CompactComplexScalarIntegerRows.wireIndex CompactComplexScalarRolePorts.roleIndex

/-- Reuse the recursive normalized-node formula at its actual raw row layout.
Input and output signed safety follow from the original dependency Path/Grid;
there is no wire-enumeration identification or new execution premise. -/
theorem normalized_native_tensor {shape : Shape} {childLeft tensorExponent levels frames returned : ℕ}
    (call : ComplexRecursiveCallSchema.Call) (rows polynomialExponent precision initialLive finalLive : ℕ)
    (phaseCoordinate : Fin shape.chunk) (childVisit : Visit shape.active childLeft (tensorExponent + 1))
    (dependencyPath : CompactRecursiveDependencyBudget.Path shape.active childLeft (tensorExponent + 1)
      levels frames returned)
    (baselinePrecision growthConstant : ℕ) (baselineFits : baselinePrecision ≤ precision)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant ≤ shape.chunk)
    (inputArray : Array shape rows polynomialExponent)
    (inputWidth : Width shape rows polynomialExponent precision inputArray)
    (inputGrid : Grid shape rows polynomialExponent precision initialLive
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant levels (frames + 2 * returned)) inputArray)
    (rolesDivide : roles ∣ rows)
    (sink : Fin CompactComplexScalarRowBlock.wireCount → Array shape (rows / roles) polynomialExponent)
    (normalizedWidth : Width shape rows polynomialExponent precision
      (normalized rows polynomialExponent finalLive
        (CompactComplexDenominatorPolicy.networkTarget initialLive tensorExponent) rolesDivide sink))
    (normalizedGrid : Grid shape rows polynomialExponent precision
      (CompactComplexDenominatorPolicy.networkTarget initialLive tensorExponent)
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant levels (frames + 2 * returned) *
        4 ^ (2 * arity ^ (tensorExponent + 1)))
      (normalized rows polynomialExponent finalLive
        (CompactComplexDenominatorPolicy.networkTarget initialLive tensorExponent) rolesDivide sink))
    (recursiveNormalizedTensor : ∀ (rawRow : Fin rows) (polynomialIndex : Fin (2 ^ polynomialExponent))
        (globalAnchor : BinaryWalsh.Address shape.bits),
      decoded shape rows polynomialExponent precision
        (CompactComplexDenominatorPolicy.networkTarget initialLive tensorExponent)
        (normalized rows polynomialExponent finalLive
          (CompactComplexDenominatorPolicy.networkTarget initialLive tensorExponent) rolesDivide sink)
        (pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex)) =
      ComplexEndpoints.fullFrame (arity ^ tensorExponent)
        (fun tensorAddress => decoded shape rows polynomialExponent precision initialLive (oriented call inputArray)
          (pack rawRow (FlatCoordinateLayout.index
            (insert phaseCoordinate childVisit globalAnchor tensorAddress) polynomialIndex)))
        (address phaseCoordinate childVisit globalAnchor))
    (row : Fin rows) (polynomialIndex : Fin (2 ^ polynomialExponent))
    (globalAnchor : BinaryWalsh.Address shape.bits) :
    nativeField precision (CompactComplexDenominatorPolicy.networkTarget initialLive tensorExponent)
      (oriented call (normalized rows polynomialExponent finalLive
        (CompactComplexDenominatorPolicy.networkTarget initialLive tensorExponent) rolesDivide sink))
      row polynomialIndex globalAnchor =
      if call.inverse then (ComplexEndpoints.fullFrame (arity ^ tensorExponent)).symm
        (slice phaseCoordinate childVisit globalAnchor (nativeField precision initialLive inputArray row polynomialIndex))
        (address phaseCoordinate childVisit globalAnchor)
      else ComplexEndpoints.fullFrame (arity ^ tensorExponent)
        (slice phaseCoordinate childVisit globalAnchor (nativeField precision initialLive inputArray row polynomialIndex))
        (address phaseCoordinate childVisit globalAnchor) := by
  have inputDecoded := CompactComplexSourceReadyOrientationInvariants.oriented_decoded call dependencyPath
    baselinePrecision growthConstant initialLive baselineFits chunkRoom inputArray inputWidth inputGrid
  obtain ⟨outputGrid, outputWidth, outputDecoded⟩ :=
    CompactComplexSourceReadyNonleafOrientedSemantics.post_grid call dependencyPath baselinePrecision growthConstant
      (CompactComplexDenominatorPolicy.networkTarget initialLive tensorExponent) baselineFits chunkRoom
      (normalized rows polynomialExponent finalLive
        (CompactComplexDenominatorPolicy.networkTarget initialLive tensorExponent) rolesDivide sink)
      normalizedWidth normalizedGrid
  let inputSlice := slice phaseCoordinate childVisit globalAnchor
    (nativeField precision initialLive inputArray row polynomialIndex)
  have orientedSlice :
      (fun tensorAddress => decoded shape rows polynomialExponent precision initialLive (oriented call inputArray)
        (pack row (FlatCoordinateLayout.index
          (insert phaseCoordinate childVisit globalAnchor tensorAddress) polynomialIndex))) =
      if call.inverse then (fun tensorAddress => star (inputSlice tensorAddress)) else inputSlice := by
    funext tensorAddress
    rw [congrFun inputDecoded (pack row (FlatCoordinateLayout.index
      (insert phaseCoordinate childVisit globalAnchor tensorAddress) polynomialIndex))]
    unfold inputSlice slice nativeField
    split_ifs <;> rfl
  change decoded shape rows polynomialExponent precision
    (CompactComplexDenominatorPolicy.networkTarget initialLive tensorExponent)
    (oriented call (normalized rows polynomialExponent finalLive
      (CompactComplexDenominatorPolicy.networkTarget initialLive tensorExponent) rolesDivide sink))
    (pack row (FlatCoordinateLayout.index globalAnchor polynomialIndex)) = _
  rw [congrFun outputDecoded (pack row (FlatCoordinateLayout.index globalAnchor polynomialIndex)),
    recursiveNormalizedTensor row polynomialIndex globalAnchor, orientedSlice]
  split_ifs with inverseOrientation
  · exact CompactComplexSourceReadyNonleafOrientedSemantics.inverse_full_tensor tensorExponent
      (fun _ => inputSlice) call.role (address phaseCoordinate childVisit globalAnchor)
  · rfl

/-- The literal selected forward basis array; its role is selected through
wireIndex, while normalized recombination keeps its actual role-port adapter. -/
def selectedForward {shape : Shape} {nodeLeft childExponent : ℕ}
    (phaseCoordinate : Fin shape.chunk) (parentVisit : Visit shape.active nodeLeft (childExponent + 2))
    (activeFits : shape.active ≤ shape.axes) (pair : BinaryRowProgram.Op (Fin arity))
    (rows polynomialExponent metadataPrecision : ℕ)
    (guardPositive : 1 ≤ shape.guard) (guardFitsChunk : shape.guard + 1 ≤ shape.chunk)
    (rowsPositive : 0 < rows) (call : ComplexRecursiveCallSchema.Call)
    (data : Fin CompactComplexScalarRowBlock.wireCount → Array shape rows polynomialExponent) :=
  CompactComplexSourceReadyReachedBasisInvariant.basisArray
    (CompactBinaryBasisSchedule.stage (CompactComplexRecursiveGeometry.node phaseCoordinate parentVisit activeFits) pair)
    rows polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive
    (CompactComplexActualBasisSlice.native_slots phaseCoordinate parentVisit activeFits pair
      rows polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive)
    (CompactComplexRolePhaseSite.pc call.site) false (data (CompactComplexScalarIntegerRows.wireIndex call.role))

/-- The recursive normalized-node identity specializes to the exact ChildTensor
assertion consumed by sibling-event semantics, on the selected forward basis. -/
theorem child_tensor {shape : Shape} {nodeLeft childExponent levels frames returned : ℕ}
    (phaseCoordinate : Fin shape.chunk) (parentVisit : Visit shape.active nodeLeft (childExponent + 2))
    (activeFits : shape.active ≤ shape.axes) (pair : BinaryRowProgram.Op (Fin arity))
    (rows polynomialExponent metadataPrecision : ℕ)
    (guardPositive : 1 ≤ shape.guard) (guardFitsChunk : shape.guard + 1 ≤ shape.chunk)
    (rowsPositive : 0 < rows) (call : ComplexRecursiveCallSchema.Call)
    (precision initialLive finalLive baselinePrecision growthConstant : ℕ)
    (dependencyPath : CompactRecursiveDependencyBudget.Path shape.active
      (nodeLeft + call.slot.val * arity ^ (childExponent + 1)) (childExponent + 1) levels frames returned)
    (baselineFits : baselinePrecision ≤ precision)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant ≤ shape.chunk)
    (data : Fin CompactComplexScalarRowBlock.wireCount → Array shape rows polynomialExponent)
    (rolesDivide : roles ∣ rows)
    (sink : Fin CompactComplexScalarRowBlock.wireCount → Array shape (rows / roles) polynomialExponent)
    (forwardWidth : Width shape rows polynomialExponent precision
      (selectedForward phaseCoordinate parentVisit activeFits pair rows polynomialExponent metadataPrecision
        guardPositive guardFitsChunk rowsPositive call data))
    (forwardGrid : Grid shape rows polynomialExponent precision initialLive
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant levels (frames + 2 * returned))
      (selectedForward phaseCoordinate parentVisit activeFits pair rows polynomialExponent metadataPrecision
        guardPositive guardFitsChunk rowsPositive call data))
    (normalizedWidth : Width shape rows polynomialExponent precision
      (normalized rows polynomialExponent finalLive
        (CompactComplexDenominatorPolicy.networkTarget initialLive childExponent) rolesDivide sink))
    (normalizedGrid : Grid shape rows polynomialExponent precision
      (CompactComplexDenominatorPolicy.networkTarget initialLive childExponent)
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant levels (frames + 2 * returned) *
        4 ^ (2 * arity ^ (childExponent + 1)))
      (normalized rows polynomialExponent finalLive
        (CompactComplexDenominatorPolicy.networkTarget initialLive childExponent) rolesDivide sink))
    (recursiveNormalizedTensor : ∀ (rawRow : Fin rows) (polynomialIndex : Fin (2 ^ polynomialExponent))
        (globalAnchor : BinaryWalsh.Address shape.bits),
      decoded shape rows polynomialExponent precision
        (CompactComplexDenominatorPolicy.networkTarget initialLive childExponent)
        (normalized rows polynomialExponent finalLive
          (CompactComplexDenominatorPolicy.networkTarget initialLive childExponent) rolesDivide sink)
        (pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex)) =
      ComplexEndpoints.fullFrame (arity ^ childExponent)
        (fun tensorAddress => decoded shape rows polynomialExponent precision initialLive
          (oriented call (selectedForward phaseCoordinate parentVisit activeFits pair rows polynomialExponent metadataPrecision
            guardPositive guardFitsChunk rowsPositive call data))
          (pack rawRow (FlatCoordinateLayout.index
            (insert phaseCoordinate (CompactComplexNonleafChildAddress.childVisit parentVisit call)
              globalAnchor tensorAddress) polynomialIndex)))
        (address phaseCoordinate (CompactComplexNonleafChildAddress.childVisit parentVisit call) globalAnchor)) :
    CompactComplexSourceReadyChildEventSemantics.ChildTensor phaseCoordinate parentVisit activeFits pair
      rows polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive call precision initialLive
      (2 * arity ^ (childExponent + 1)) data
      (oriented call (normalized rows polynomialExponent finalLive
        (CompactComplexDenominatorPolicy.networkTarget initialLive childExponent) rolesDivide sink)) := by
  intro row polynomialIndex globalAnchor
  have tensor := normalized_native_tensor call rows polynomialExponent precision initialLive finalLive phaseCoordinate
    (CompactComplexNonleafChildAddress.childVisit parentVisit call) dependencyPath baselinePrecision growthConstant
    baselineFits chunkRoom
    (selectedForward phaseCoordinate parentVisit activeFits pair rows polynomialExponent metadataPrecision
      guardPositive guardFitsChunk rowsPositive call data) forwardWidth forwardGrid rolesDivide sink
    normalizedWidth normalizedGrid recursiveNormalizedTensor row polynomialIndex globalAnchor
  simpa only [CompactComplexDenominatorPolicy.networkTarget, selectedForward] using tensor

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafChildTensor
