module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafChildTensor
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedChildInvariant
public import IntegerMultBounds.Machine.CompactComplexSourceReadySiblingReturnInvariant
public import IntegerMultBounds.Machine.CompactComplexCorrectedChildGridSemantics

/-! A recursive child's actual tensor identity gives a fresh parent return
bound from the selected forward input. Internal child scalar levels and frame
budgets are not carried into the parent. Every coefficient uses the literal
raw-row, polynomial and global-address layout of the computed child result. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafChildReturnGrid
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Grid)
open CompactComplexActualBasisPullback (nativeField)
open CompactComplexStoppedLeafTensorSemantics (slice)
open CompactComplexNonleafChildAddress (address)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached)
open CompactComplexSourceReadyReachedChildInvariant (selectedArray)
open CompactComplexSourceReadySiblingGuards (returnedCursor)
open RecursiveInterchangeRows (pack)
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites
  CompactComplexRolePhaseSite.roleCount CompactComplexCompletedLiveLower.schedule
  CompactComplexScalarIntegerRows.wireIndex CompactComplexScalarRolePorts.roleIndex

/-- Pointwise tensor semantics on actual raw rows covers every stored
coefficient and supplies the exact two-volume return numerator bound. -/
theorem native_tensor_grid {shape : Shape} {childLeft childExponent : ℕ}
    (call : ComplexRecursiveCallSchema.Call) (rows polynomialExponent precision parentLive numeratorBound : ℕ)
    (phaseCoordinate : Fin shape.chunk) (childVisit : Visit shape.active childLeft (childExponent + 1))
    (inputArray resultArray : Array shape rows polynomialExponent)
    (inputGrid : Grid shape rows polynomialExponent precision parentLive numeratorBound inputArray)
    (actualChildTensor : ∀ (rawRow : Fin rows) (polynomialIndex : Fin (2 ^ polynomialExponent))
        (globalAnchor : BinaryWalsh.Address shape.bits),
      nativeField precision (parentLive + 2 * arity ^ (childExponent + 1)) resultArray
        rawRow polynomialIndex globalAnchor =
      if call.inverse then (ComplexEndpoints.fullFrame (arity ^ childExponent)).symm
        (slice phaseCoordinate childVisit globalAnchor (nativeField precision parentLive inputArray rawRow polynomialIndex))
        (address phaseCoordinate childVisit globalAnchor)
      else ComplexEndpoints.fullFrame (arity ^ childExponent)
        (slice phaseCoordinate childVisit globalAnchor (nativeField precision parentLive inputArray rawRow polynomialIndex))
        (address phaseCoordinate childVisit globalAnchor)) :
    Grid shape rows polynomialExponent precision (parentLive + 2 * arity ^ (childExponent + 1))
      (numeratorBound * 4 ^ (2 * arity ^ (childExponent + 1))) resultArray := by
  let layout : (Fin rows × (BinaryWalsh.Address shape.bits × Fin (2 ^ polynomialExponent))) ≃
      Fin (ButterflySpectatorGeometry.Size rows shape.bits (2 ^ polynomialExponent)) :=
    (Equiv.prodCongr (Equiv.refl _) FlatCoordinateLayout.arrayEquiv).trans finProdFinEquiv
  intro coefficient
  obtain ⟨⟨rawRow,globalAnchor,polynomialIndex⟩,indexEquation⟩ := layout.surjective coefficient
  have rawIndex : coefficient = pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex) :=
    indexEquation.symm
  rw [rawIndex]
  change GaussianPrecision.BoundedGrid _ _
    (nativeField precision (parentLive + 2 * arity ^ (childExponent + 1)) resultArray
      rawRow polynomialIndex globalAnchor)
  rw [actualChildTensor rawRow polynomialIndex globalAnchor]
  exact CompactComplexCorrectedChildGridSemantics.tensor_grid call parentLive childExponent numeratorBound
    (fun _ => slice phaseCoordinate childVisit globalAnchor
      (nativeField precision parentLive inputArray rawRow polynomialIndex))
    (fun _ tensorAddress => inputGrid
      (pack rawRow (FlatCoordinateLayout.index
        (CompactComplexNonleafChildAddress.insert phaseCoordinate childVisit globalAnchor tensorAddress) polynomialIndex)))
    call.role (address phaseCoordinate childVisit globalAnchor)

section Parent
variable {extraTapes : ℕ} {shape : Shape} {stage : ActivePrefixStageParameters.Stage shape}
    {parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive
      dependencyLevels frameVolume currentReturned scalarPrefix parentLive : ℕ}
    {pcStack : Fin extraTapes} {origin : ℤ} {calls : List ComplexRecursiveCallSchema.Call}
    {parentBank : Tapes (nodeTapes extraTapes roles) 2}
    (parentReached : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision
      growthConstant completedAxes baselineLive dependencyLevels frameVolume currentReturned scalarPrefix parentLive
      pcStack origin calls parentBank)

/-- The actual forward parent's selected-role grid and the computed child
tensor discharge the inherited grid expected by physical sibling return. -/
theorem selected_return_grid {childLeft childExponent : ℕ}
    (call : ComplexRecursiveCallSchema.Call) (phaseCoordinate : Fin shape.chunk)
    (childVisit : Visit shape.active childLeft (childExponent + 1))
    (metadataFits : 2 * shape.bits ≤ metadataPrecision)
    (resultArray : Array shape (parentRows / roles) polynomialExponent)
    (actualChildTensor : ∀ (rawRow : Fin (parentRows / roles)) (polynomialIndex : Fin (2 ^ polynomialExponent))
        (globalAnchor : BinaryWalsh.Address shape.bits),
      nativeField (metadataPrecision - 2 * shape.bits) (parentLive + 2 * arity ^ (childExponent + 1))
        resultArray rawRow polynomialIndex globalAnchor =
      if call.inverse then (ComplexEndpoints.fullFrame (arity ^ childExponent)).symm
        (slice phaseCoordinate childVisit globalAnchor
          (nativeField (metadataPrecision - 2 * shape.bits) parentLive (selectedArray parentReached call)
            rawRow polynomialIndex))
        (address phaseCoordinate childVisit globalAnchor)
      else ComplexEndpoints.fullFrame (arity ^ childExponent)
        (slice phaseCoordinate childVisit globalAnchor
          (nativeField (metadataPrecision - 2 * shape.bits) parentLive (selectedArray parentReached call)
            rawRow polynomialIndex))
        (address phaseCoordinate childVisit globalAnchor)) :
    Grid shape (parentRows / roles) polynomialExponent (metadataPrecision - 2 * shape.bits)
      (parentLive + 2 * arity ^ (childExponent + 1))
      (CompactFramedScalarGrid.bound scalarPrefix
        (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels
          (frameVolume + 2 * (currentReturned + arity ^ (childExponent + 1)) + completedAxes))) resultArray := by
  have tightGrid := native_tensor_grid call (parentRows / roles) polynomialExponent (metadataPrecision - 2 * shape.bits)
    parentLive
    (CompactFramedScalarGrid.bound scalarPrefix
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels
        (frameVolume + 2 * currentReturned + completedAxes)))
    phaseCoordinate childVisit (selectedArray parentReached call) resultArray
    (CompactComplexSourceReadyReachedChildInvariant.selected_grid parentReached call metadataFits) actualChildTensor
  rw [CompactComplexNonleafEventProgress.prefix_bound] at tightGrid
  exact tightGrid

/-- A genuine basis replacement identifies the selected child input without
changing the adapters between scalar wire enumeration and physical role ports. -/
theorem selected_of_replacement
    (call : ComplexRecursiveCallSchema.Call)
    (forwardArray : Array shape (parentRows / roles) polynomialExponent)
    {forwardBank : Tapes (nodeTapes extraTapes roles) 2}
    (forwardReached : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision
      growthConstant completedAxes baselineLive dependencyLevels frameVolume currentReturned scalarPrefix parentLive
      pcStack origin calls forwardBank)
    (forwardDataEquation : forwardReached.data =
      CompactComplexSourceReadyReachedBasisInvariant.replacementData parentReached
        (CompactComplexRolePhaseSite.role call.site) forwardArray) :
    selectedArray forwardReached call = forwardArray := by
  unfold selectedArray
  rw [forwardDataEquation]
  simp only [CompactComplexSourceReadyChildEntryPath.selected,
    CompactComplexSourceReadyReachedBasisInvariant.replacementData, Function.update_self]

/-- Actual child tensor values on the selected forward Reached array give
ChildTensor for the original parent basis input via its real data equation. -/
theorem child_tensor_of_forward {nodeLeft childExponent : ℕ}
    (phaseCoordinate : Fin shape.chunk) (parentVisit : Visit shape.active nodeLeft (childExponent + 2))
    (activeFits : shape.active ≤ shape.axes) (pair : BinaryRowProgram.Op (Fin arity))
    (guardPositive : 1 ≤ shape.guard) (guardFitsChunk : shape.guard + 1 ≤ shape.chunk)
    (rowsPositive : 0 < parentRows / roles) (call : ComplexRecursiveCallSchema.Call)
    {forwardBank : Tapes (nodeTapes extraTapes roles) 2}
    (forwardReached : Reached stage parentRows polynomialExponent metadataPrecision nodeExponent baselinePrecision
      growthConstant completedAxes baselineLive dependencyLevels frameVolume currentReturned scalarPrefix parentLive
      pcStack origin calls forwardBank)
    (forwardDataEquation : forwardReached.data =
      CompactComplexSourceReadyReachedBasisInvariant.replacementData parentReached
        (CompactComplexRolePhaseSite.role call.site)
        (CompactComplexSourceReadyNonleafChildTensor.selectedForward phaseCoordinate parentVisit activeFits pair
          (parentRows / roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive call parentReached.data))
    (resultArray : Array shape (parentRows / roles) polynomialExponent)
    (actualChildTensor : ∀ (rawRow : Fin (parentRows / roles)) (polynomialIndex : Fin (2 ^ polynomialExponent))
        (globalAnchor : BinaryWalsh.Address shape.bits),
      nativeField (metadataPrecision - 2 * shape.bits) (parentLive + 2 * arity ^ (childExponent + 1))
        resultArray rawRow polynomialIndex globalAnchor =
      if call.inverse then (ComplexEndpoints.fullFrame (arity ^ childExponent)).symm
        (slice phaseCoordinate (CompactComplexNonleafChildAddress.childVisit parentVisit call) globalAnchor
          (nativeField (metadataPrecision - 2 * shape.bits) parentLive (selectedArray forwardReached call)
            rawRow polynomialIndex))
        (address phaseCoordinate (CompactComplexNonleafChildAddress.childVisit parentVisit call) globalAnchor)
      else ComplexEndpoints.fullFrame (arity ^ childExponent)
        (slice phaseCoordinate (CompactComplexNonleafChildAddress.childVisit parentVisit call) globalAnchor
          (nativeField (metadataPrecision - 2 * shape.bits) parentLive (selectedArray forwardReached call)
            rawRow polynomialIndex))
        (address phaseCoordinate (CompactComplexNonleafChildAddress.childVisit parentVisit call) globalAnchor)) :
    CompactComplexSourceReadyChildEventSemantics.ChildTensor phaseCoordinate parentVisit activeFits pair
      (parentRows / roles) polynomialExponent metadataPrecision guardPositive guardFitsChunk rowsPositive call
      (metadataPrecision - 2 * shape.bits) parentLive (2 * arity ^ (childExponent + 1)) parentReached.data resultArray := by
  have selectedInput := selected_of_replacement parentReached call _ forwardReached forwardDataEquation
  rw [selectedInput] at actualChildTensor
  simpa only [CompactComplexSourceReadyChildEventSemantics.ChildTensor,
    CompactComplexSourceReadyNonleafChildTensor.selectedForward] using actualChildTensor

end Parent
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafChildReturnGrid
