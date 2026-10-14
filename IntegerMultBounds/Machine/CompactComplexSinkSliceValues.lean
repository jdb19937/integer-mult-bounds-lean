module

public import IntegerMultBounds.Machine.CompactComplexSinkCorrectOutput
public import IntegerMultBounds.Machine.CompactComplexCorrectedEntrySliceCoordinates
public import IntegerMultBounds.Machine.CompactComplexSourceReadyChildEventSemantics

/-! The literal corrected-final family has correctOutput values on each actual
anchored node slice. Its input relation is proved at the one coefficient selected
by that slice, without a global input-decoding oracle or invented dependency Path. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSinkSliceValues
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit node)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Width Grid decoded half)
open CompactComplexEndpointRoleExchange (Wire)
open CompactComplexRolePhaseSite (roleEncoding)
open CompactComplexScalarIntegerRows (wireIndex)
open CompactComplexScalarRolePorts (roleIndex)
open CompactComplexScalarRowBlock (wireCount)
open CompactComplexActualBasisPullback (nativeField)
open CompactComplexStoppedLeafTensorSemantics (slice)
open CompactComplexNonleafChildAddress (insert)
open CompactComplexCorrectedEntryGridReadiness (coordinates)
open RecursiveInterchangeRows (pack)
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites
  CompactComplexRolePhaseSite.roleCount roleEncoding wireIndex

variable {shape : Shape} {rowCount polynomialExponent : ℕ}

/-- The real named corrected-final arrays, read in original wire order. -/
def outputRoles (stage : ActivePrefixStageParameters.Stage shape) (stageSlots : stage.slots=arity)
    (metadataPrecision : ℕ) (before : Wire → Array shape rowCount polynomialExponent) :=
  fun wire => CompactComplexSourceReadyCorrectedFinal.family stage stageSlots polynomialExponent metadataPrecision before
    (roleEncoding wire)

/-- Direct original row/polynomial/global-address projection of named arrays. -/
def sliceStored {leftBoundary childExponent : ℕ}
    (phaseCoordinate : Fin shape.chunk) (visit : Visit shape.active leftBoundary (childExponent+1))
    (storagePrecision live : ℕ) (roleArrays : Wire → Array shape rowCount polynomialExponent)
    (outerRow : Fin rowCount) (polynomialIndex : Fin (2^polynomialExponent)) (anchor : BinaryWalsh.Address shape.bits) :
    Wire → BinaryColumns.Arrays arity (arity^childExponent) :=
  fun wire => slice phaseCoordinate visit anchor (nativeField storagePrecision live (roleArrays wire) outerRow polynomialIndex)

/-- At every actual anchored node slice, the computed final family has the
original sink signs, column phase, negation and exchange of correctOutput. -/
theorem slice_values_guarded {leftBoundary childExponent : ℕ}
    (phaseCoordinate : Fin shape.chunk) (visit : Visit shape.active leftBoundary (childExponent+1))
    (activeFits : shape.active≤shape.axes) (pair : BinaryRowProgram.Op (Fin arity))
    (stageSlots : (CompactBinaryBasisSchedule.stage (node phaseCoordinate visit activeFits) pair).slots=arity)
    (metadataPrecision storagePrecision live numeratorBound : ℕ)
    (before : Wire → Array shape rowCount polynomialExponent)
    (inputWidth : ∀ wire,Width shape rowCount polynomialExponent storagePrecision (before wire))
    (inputGrid : ∀ wire,Grid shape rowCount polynomialExponent storagePrecision live numeratorBound (before wire))
    (signedReserve : numeratorBound<2^(half shape storagePrecision))
    (outerRow : Fin rowCount) (polynomialIndex : Fin (2^polynomialExponent)) (anchor : BinaryWalsh.Address shape.bits) :
    sliceStored phaseCoordinate visit storagePrecision live
      (outputRoles (CompactBinaryBasisSchedule.stage (node phaseCoordinate visit activeFits) pair) stageSlots metadataPrecision before)
      outerRow polynomialIndex anchor=
    ComplexEndpoints.correctOutput (arity^childExponent)
      (sliceStored phaseCoordinate visit storagePrecision live before outerRow polynomialIndex anchor) := by
  let stage := CompactBinaryBasisSchedule.stage (node phaseCoordinate visit activeFits) pair
  let inputNetwork := sliceStored phaseCoordinate visit storagePrecision live before outerRow polynomialIndex anchor
  funext wire tensorAddress
  let coefficient := pack outerRow (FlatCoordinateLayout.index (insert phaseCoordinate visit anchor tensorAddress) polynomialIndex)
  have coordinateAt : coordinates stage stageSlots rowCount polynomialExponent metadataPrecision coefficient=tensorAddress :=
    CompactComplexCorrectedEntrySliceCoordinates.anchored_insert_coordinates phaseCoordinate visit activeFits pair
      rowCount polynomialExponent metadataPrecision stageSlots outerRow anchor polynomialIndex tensorAddress
  have inputAt : ∀ inputWire,decoded shape rowCount polynomialExponent storagePrecision live
      (before inputWire) coefficient=inputNetwork inputWire
        (coordinates stage stageSlots rowCount polynomialExponent metadataPrecision coefficient) := by
    intro inputWire
    rw [coordinateAt]
    rfl
  have corrected := CompactComplexSinkCorrectOutput.decoded_correctOutput_at_guarded stage stageSlots metadataPrecision live
    numeratorBound before inputWidth inputGrid signedReserve coefficient inputNetwork inputAt wire
  rw [coordinateAt] at corrected
  change decoded shape rowCount polynomialExponent storagePrecision live
    (CompactComplexSourceReadySinkCorrections.data stage stageSlots polynomialExponent metadataPrecision before wire)
    coefficient=ComplexEndpoints.correctOutput (arity^childExponent)
      (sliceStored phaseCoordinate visit storagePrecision live before outerRow polynomialIndex anchor) wire tensorAddress at corrected
  change decoded shape rowCount polynomialExponent storagePrecision live
    (outputRoles stage stageSlots metadataPrecision before wire) coefficient=_
  simpa only [outputRoles,CompactComplexSourceReadyCorrectedFinal.family,Equiv.symm_apply_apply] using corrected

private theorem equiv_encoding {Original Scalar Port : Type*}
    (scalarEncoding : Original ≃ Scalar) (portEncoding : Original ≃ Port) (original : Original) :
    (scalarEncoding.symm.trans portEncoding) (scalarEncoding original)=portEncoding original := by
  simp only [Equiv.trans_apply,Equiv.symm_apply_apply]

private theorem role_index_encoding (wire : Wire) : roleIndex (wireIndex wire)=roleEncoding wire := by
  unfold roleIndex
  exact equiv_encoding wireIndex roleEncoding wire

/-- The same literal corrected-final family, in the scalar bank's role order. -/
def scalarOutputRoles (stage : ActivePrefixStageParameters.Stage shape) (stageSlots : stage.slots=arity)
    (metadataPrecision : ℕ) (before : Fin wireCount → Array shape rowCount polynomialExponent) :=
  fun scalarRole => CompactComplexSourceReadyCorrectedFinal.family stage stageSlots polynomialExponent metadataPrecision
    (fun wire => before (wireIndex wire)) (roleIndex scalarRole)

private theorem scalar_output_encoding (stage : ActivePrefixStageParameters.Stage shape) (stageSlots : stage.slots=arity)
    (metadataPrecision : ℕ) (before : Fin wireCount → Array shape rowCount polynomialExponent) (wire : Wire) :
    scalarOutputRoles stage stageSlots metadataPrecision before (wireIndex wire)=
      outputRoles stage stageSlots metadataPrecision (fun namedWire => before (wireIndex namedWire)) wire := by
  unfold scalarOutputRoles outputRoles
  rw [role_index_encoding]

/-- Direct compatibility with the actual reached nonleaf stored-slice API,
using literal scalar-order before arrays and the actual corrected-final family. -/
theorem stored_values_guarded {leftBoundary childExponent : ℕ}
    (phaseCoordinate : Fin shape.chunk) (visit : Visit shape.active leftBoundary (childExponent+2))
    (activeFits : shape.active≤shape.axes) (pair : BinaryRowProgram.Op (Fin arity))
    (stageSlots : (CompactBinaryBasisSchedule.stage (node phaseCoordinate visit activeFits) pair).slots=arity)
    (metadataPrecision storagePrecision live numeratorBound : ℕ)
    (before : Fin wireCount → Array shape rowCount polynomialExponent)
    (inputWidth : ∀ role,Width shape rowCount polynomialExponent storagePrecision (before role))
    (inputGrid : ∀ role,Grid shape rowCount polynomialExponent storagePrecision live numeratorBound (before role))
    (signedReserve : numeratorBound<2^(half shape storagePrecision))
    (outerRow : Fin rowCount) (polynomialIndex : Fin (2^polynomialExponent)) (anchor : BinaryWalsh.Address shape.bits) :
    CompactComplexSourceReadyChildEventSemantics.stored phaseCoordinate visit rowCount polynomialExponent storagePrecision live
      (scalarOutputRoles (CompactBinaryBasisSchedule.stage (node phaseCoordinate visit activeFits) pair) stageSlots metadataPrecision before)
      outerRow polynomialIndex anchor=
    ComplexEndpoints.correctOutput (arity^(childExponent+1))
      (CompactComplexSourceReadyChildEventSemantics.stored phaseCoordinate visit rowCount polynomialExponent storagePrecision live
        before outerRow polynomialIndex anchor) := by
  let stage := CompactBinaryBasisSchedule.stage (node phaseCoordinate visit activeFits) pair
  have corrected := slice_values_guarded phaseCoordinate visit activeFits pair stageSlots metadataPrecision storagePrecision live
    numeratorBound (fun wire => before (wireIndex wire)) (fun wire => inputWidth (wireIndex wire))
    (fun wire => inputGrid (wireIndex wire)) signedReserve outerRow polynomialIndex anchor
  have outputSlice : CompactComplexSourceReadyChildEventSemantics.stored phaseCoordinate visit rowCount polynomialExponent
      storagePrecision live (scalarOutputRoles stage stageSlots metadataPrecision before) outerRow polynomialIndex anchor=
      sliceStored phaseCoordinate visit storagePrecision live
        (outputRoles stage stageSlots metadataPrecision (fun wire => before (wireIndex wire))) outerRow polynomialIndex anchor := by
    funext wire tensorAddress
    change nativeField storagePrecision live (scalarOutputRoles stage stageSlots metadataPrecision before (wireIndex wire))
      outerRow polynomialIndex (insert phaseCoordinate visit anchor tensorAddress)=
      nativeField storagePrecision live (outputRoles stage stageSlots metadataPrecision (fun namedWire => before (wireIndex namedWire)) wire)
        outerRow polynomialIndex (insert phaseCoordinate visit anchor tensorAddress)
    rw [scalar_output_encoding]
  rw [outputSlice]
  exact corrected

end
end IntegerMultBounds.Machine.CompactComplexSinkSliceValues
