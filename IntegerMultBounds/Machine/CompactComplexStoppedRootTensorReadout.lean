module

public import IntegerMultBounds.Machine.CompactComplexStoppedLeafTensorSemantics
public import IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedInstalledResult

/-! Exact readout of the actual forward stopped-root result. Original
retained widths and a genuine dependency grid derive all signed guards;
no child semantics, output correctness or execution is assumed. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexStoppedRootTensorReadout
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactRecursiveDependencyBudget (Path)
open CompactSpectatorInheritedGrid (Width Grid decoded)
open CompactComplexStoppedLeafTensorSemantics (rowSlice slice)
open CompactComplexNonleafChildAddress (insert address)
open RecursiveInterchangeRows (pack)

/-- The same emitted positive stopped-root array has retained widths, its true
leaf-target grid and the exact corrected tensor value at every original
row, polynomial and spectator address. All guards come from the input Path. -/
theorem positive_readout (shape : Shape) (rows ell metadataPrecision baseline growthConstant initialLive : ℕ)
    (rowsPositive : 0<rows) (phaseCoordinate : Fin shape.chunk) {left childExponent levels frames returned : ℕ}
    (dependency : Path shape.active left (childExponent+1) levels frames returned)
    (metadataFits : 2*shape.bits≤metadataPrecision) (baselineFits : baseline≤metadataPrecision-2*shape.bits)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant≤shape.chunk)
    (inputArray : CompactSpectatorVisitGeometry.Array (NativePolynomialStageShape.shape shape ell metadataPrecision) rows ell)
    (inputWidth : ∀ index,(inputArray index).1.length=CompactNativeRoleHeaders.recordWidth shape metadataPrecision ∧
      (inputArray index).2.length=CompactNativeRoleHeaders.recordWidth shape metadataPrecision)
    (inputGrid : Grid shape rows ell (metadataPrecision-2*shape.bits) initialLive
      (CompactRecursiveGridBudget.bound baseline growthConstant levels (frames+2*returned)) inputArray) :
    let outputArray := CompactSpectatorLeafGuardOriginal.result .forward shape rows ell
      (metadataPrecision-2*shape.bits) phaseCoordinate dependency.visit inputArray
    (∀ index,(outputArray index).1.length=CompactNativeRoleHeaders.recordWidth shape metadataPrecision ∧
      (outputArray index).2.length=CompactNativeRoleHeaders.recordWidth shape metadataPrecision) ∧
    Grid shape rows ell (metadataPrecision-2*shape.bits)
      (CompactComplexDenominatorPolicy.leafTarget initialLive (childExponent+1))
      (CompactRecursiveGridBudget.bound baseline growthConstant levels (frames+2*returned)*4^(arity^(childExponent+1))) outputArray ∧
    ∀ (rawRow : Fin rows) (polynomialIndex : Fin (2^ell)) (globalAnchor : BinaryWalsh.Address shape.bits),
      decoded shape rows ell (metadataPrecision-2*shape.bits)
        (CompactComplexDenominatorPolicy.leafTarget initialLive (childExponent+1)) outputArray
        (pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex))=
      ComplexEndpoints.fullFrame (arity^childExponent)
        (fun tensorAddress => decoded shape rows ell (metadataPrecision-2*shape.bits) initialLive inputArray
          (pack rawRow (FlatCoordinateLayout.index
            (insert phaseCoordinate dependency.visit globalAnchor tensorAddress) polynomialIndex)))
        (address phaseCoordinate dependency.visit globalAnchor) := by
  dsimp only
  have widths := CompactComplexSourceReadyLeafSemantics.result_width .forward rows ell metadataPrecision
    phaseCoordinate dependency.visit metadataFits inputArray inputWidth
  have resultEquation := CompactComplexSourceReadyStoppedInstalledResult.polynomial_leaf_result
    shape rows ell metadataPrecision phaseCoordinate dependency.visit inputArray
  rw [resultEquation] at widths
  have retainedWidth := CompactSpectatorInheritedGrid.width_from_retained_role shape rows ell metadataPrecision
    metadataFits inputArray inputWidth
  have semantics := CompactComplexStoppedLeafTensorSemantics.forward_result_from_path
    rows ell (metadataPrecision-2*shape.bits) initialLive baseline growthConstant phaseCoordinate dependency
    baselineFits chunkRoom inputArray retainedWidth inputGrid
  have outputGrid := (semantics (⟨0,rowsPositive⟩ : Fin rows) (0 : Fin (2^ell)) (0 : BinaryWalsh.Address shape.bits)).1
  refine ⟨widths,?_,?_⟩
  · exact outputGrid
  · intro rawRow polynomialIndex globalAnchor
    have rowSemantics := (semantics rawRow polynomialIndex globalAnchor).2
    have inputSliceEquation : rowSlice rows ell (metadataPrecision-2*shape.bits) initialLive
        phaseCoordinate dependency.visit rawRow polynomialIndex globalAnchor inputArray=
        (fun tensorAddress => decoded shape rows ell (metadataPrecision-2*shape.bits) initialLive inputArray
          (pack rawRow (FlatCoordinateLayout.index
            (insert phaseCoordinate dependency.visit globalAnchor tensorAddress) polynomialIndex))) := rfl
    rw [inputSliceEquation] at rowSemantics
    have atAddress := congrFun rowSemantics (address phaseCoordinate dependency.visit globalAnchor)
    simpa only [rowSlice,CompactComplexStoppedLeafTensorSemantics.slice,CompactComplexDenominatorPolicy.leafTarget,
      CompactComplexNonleafChildAddress.insert_address] using atAddress

/-- Exponent zero has its actual single-coordinate forward kernel, retained
width and genuine leaf-target grid. This covers the finite scalar branch
without pretending it is a positive-width complex motif. -/
theorem scalar_readout (shape : Shape) (rows ell metadataPrecision baseline growthConstant initialLive : ℕ)
    (rowsPositive : 0<rows) (phaseCoordinate : Fin shape.chunk) {left levels frames returned : ℕ}
    (dependency : Path shape.active left 0 levels frames returned)
    (metadataFits : 2*shape.bits≤metadataPrecision) (baselineFits : baseline≤metadataPrecision-2*shape.bits)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant≤shape.chunk)
    (inputArray : CompactSpectatorVisitGeometry.Array (NativePolynomialStageShape.shape shape ell metadataPrecision) rows ell)
    (inputWidth : ∀ index,(inputArray index).1.length=CompactNativeRoleHeaders.recordWidth shape metadataPrecision ∧
      (inputArray index).2.length=CompactNativeRoleHeaders.recordWidth shape metadataPrecision)
    (inputGrid : Grid shape rows ell (metadataPrecision-2*shape.bits) initialLive
      (CompactRecursiveGridBudget.bound baseline growthConstant levels (frames+2*returned)) inputArray) :
    let outputArray := CompactSpectatorLeafGuardOriginal.result .forward shape rows ell
      (metadataPrecision-2*shape.bits) phaseCoordinate dependency.visit inputArray
    (∀ index,(outputArray index).1.length=CompactNativeRoleHeaders.recordWidth shape metadataPrecision ∧
      (outputArray index).2.length=CompactNativeRoleHeaders.recordWidth shape metadataPrecision) ∧
    Grid shape rows ell (metadataPrecision-2*shape.bits) (CompactComplexDenominatorPolicy.leafTarget initialLive 0)
      (CompactRecursiveGridBudget.bound baseline growthConstant levels (frames+2*returned)*4^(arity^0)) outputArray ∧
    ∀ (rawRow : Fin rows) (polynomialIndex : Fin (2^ell)),
      (fun globalAnchor => decoded shape rows ell (metadataPrecision-2*shape.bits)
        (CompactComplexDenominatorPolicy.leafTarget initialLive 0) outputArray
        (pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex)))=
      BinaryWalsh.kernelRun (CompactSpectatorInheritedGrid.kernelList shape phaseCoordinate dependency.visit .forward (arity^0) le_rfl)
        (fun globalAnchor => decoded shape rows ell (metadataPrecision-2*shape.bits) initialLive inputArray
          (pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex))) := by
  dsimp only
  have widths := CompactComplexSourceReadyLeafSemantics.result_width .forward rows ell metadataPrecision
    phaseCoordinate dependency.visit metadataFits inputArray inputWidth
  have resultEquation := CompactComplexSourceReadyStoppedInstalledResult.polynomial_leaf_result
    shape rows ell metadataPrecision phaseCoordinate dependency.visit inputArray
  rw [resultEquation] at widths
  have retainedWidth := CompactSpectatorInheritedGrid.width_from_retained_role shape rows ell metadataPrecision
    metadataFits inputArray inputWidth
  have signedGuard := CompactSpectatorInheritedGrid.guard_from_path shape (metadataPrecision-2*shape.bits)
    dependency baseline growthConstant (arity^0) baselineFits chunkRoom
    (CompactSpectatorLeafSemantics.count_le_bits shape phaseCoordinate dependency.visit)
  have semantics := CompactSpectatorInheritedGrid.directional_semantics shape rows ell (metadataPrecision-2*shape.bits)
    phaseCoordinate dependency.visit .forward initialLive _ inputArray retainedWidth inputGrid signedGuard
  have outputGrid := (semantics (⟨0,rowsPositive⟩ : Fin rows) (0 : Fin (2^ell))).1
  refine ⟨widths,?_,?_⟩
  · exact outputGrid
  · intro rawRow polynomialIndex
    exact (semantics rawRow polynomialIndex).2

end
end IntegerMultBounds.Machine.CompactComplexStoppedRootTensorReadout
