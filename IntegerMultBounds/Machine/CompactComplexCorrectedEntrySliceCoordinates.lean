module

public import IntegerMultBounds.Machine.CompactComplexCorrectedEntryGridReadiness
public import IntegerMultBounds.Machine.CompactComplexEndpointCoordinates

/-! The corrected source codec reads the original global binary address of
each coefficient, independently of its outer row and polynomial index. Its
node readout is the actual tensor slice address, including inserted addresses.
No coordinate compatibility equality is supplied. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexCorrectedEntrySliceCoordinates
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit node)
open CompactComplexEndpointCoordinates (rowCoordinates)
open CompactComplexCorrectedEntryGridReadiness (codecIndex coordinates)
open CompactComplexNonleafChildAddress (address insert)
open RecursiveInterchangeRows (pack)
open Networks

private theorem row_polynomial_quotient (outerRow addressWidth addressOrdinal polynomialWidth polynomialOrdinal : ℕ)
    (polynomialWidthPositive : 0<polynomialWidth) (polynomialBound : polynomialOrdinal<polynomialWidth) :
    (outerRow*(addressWidth*polynomialWidth)+(addressOrdinal*polynomialWidth+polynomialOrdinal))/polynomialWidth=
      outerRow*addressWidth+addressOrdinal := by
  have numeratorEquation : outerRow*(addressWidth*polynomialWidth)+(addressOrdinal*polynomialWidth+polynomialOrdinal)=
      polynomialWidth*(outerRow*addressWidth+addressOrdinal)+polynomialOrdinal := by ring
  rw [numeratorEquation,Nat.mul_add_div polynomialWidthPositive,Nat.div_eq_of_lt polynomialBound,Nat.add_zero]

variable {shape : Shape}

/-- The codec's payload block starts at the same global address, retaining
the original outer row and polynomial coefficient without a supplied reshape. -/
theorem codec_row_coordinates (rowCount polynomialExponent metadataPrecision : ℕ)
    (outerRow : Fin rowCount) (globalAddress : BinaryWalsh.Address shape.bits)
    (polynomialIndex : Fin (2^polynomialExponent)) :
    rowCoordinates (NativePolynomialStageShape.shape shape polynomialExponent metadataPrecision)
      (codecIndex rowCount polynomialExponent metadataPrecision
        (pack outerRow (FlatCoordinateLayout.index globalAddress polynomialIndex)))=globalAddress := by
  have payloadPositive : 0<NativePolynomialStageShape.payload shape polynomialExponent metadataPrecision :=
    lt_of_lt_of_le (by omega : 0<shape.bits+1)
      (NativePolynomialStageShape.payload_fits shape polynomialExponent metadataPrecision)
  have coefficientQuotient :
      (pack outerRow (FlatCoordinateLayout.index globalAddress polynomialIndex)).val/2^polynomialExponent=
        outerRow.val*2^shape.bits+(FlatCoordinateLayout.rank globalAddress).val := by
    rw [RecursiveInterchangeRows.pack_val,FlatCoordinateLayout.index_val]
    exact row_polynomial_quotient outerRow.val (2^shape.bits) (FlatCoordinateLayout.rank globalAddress).val
      (2^polynomialExponent) polynomialIndex.val (pow_pos (by decide) _) polynomialIndex.isLt
  have addressRemainder :
      (pack outerRow (FlatCoordinateLayout.index globalAddress polynomialIndex)).val/2^polynomialExponent%2^shape.bits=
        (FlatCoordinateLayout.rank globalAddress).val := by
    rw [coefficientQuotient,Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,
      Nat.mod_eq_of_lt (FlatCoordinateLayout.rank globalAddress).isLt,
      Nat.mod_eq_of_lt (FlatCoordinateLayout.rank globalAddress).isLt]
  unfold rowCoordinates
  change FlatCoordinateLayout.coordinates
    (⟨((pack outerRow (FlatCoordinateLayout.index globalAddress polynomialIndex)).val/2^polynomialExponent*
        NativePolynomialStageShape.payload shape polynomialExponent metadataPrecision)/
        NativePolynomialStageShape.payload shape polynomialExponent metadataPrecision%2^shape.bits,
      Nat.mod_lt _ (pow_pos (by decide) _)⟩ : Fin (2^shape.bits))=globalAddress
  rw [Nat.mul_div_cancel _ payloadPositive]
  have addressIndex :
      (⟨(pack outerRow (FlatCoordinateLayout.index globalAddress polynomialIndex)).val/2^polynomialExponent%2^shape.bits,
        Nat.mod_lt _ (pow_pos (by decide) _)⟩ : Fin (2^shape.bits))=FlatCoordinateLayout.rank globalAddress :=
    Fin.ext addressRemainder
  rw [addressIndex,FlatCoordinateLayout.coordinates_rank]

/-- The exact corrected entry readout is the actual enclosing node tensor
address at every outer row, polynomial index and original global address. -/
theorem node_coordinates {leftBoundary childExponent : ℕ}
    (phaseCoordinate : Fin shape.chunk) (visit : Visit shape.active leftBoundary (childExponent+1))
    (activeFits : shape.active≤shape.axes) (pair : BinaryRowProgram.Op (Fin arity))
    (rowCount polynomialExponent metadataPrecision : ℕ)
    (stageSlots : (CompactBinaryBasisSchedule.stage (node phaseCoordinate visit activeFits) pair).slots=arity)
    (outerRow : Fin rowCount) (globalAddress : BinaryWalsh.Address shape.bits)
    (polynomialIndex : Fin (2^polynomialExponent)) :
    coordinates (CompactBinaryBasisSchedule.stage (node phaseCoordinate visit activeFits) pair)
      stageSlots rowCount polynomialExponent metadataPrecision
      (pack outerRow (FlatCoordinateLayout.index globalAddress polynomialIndex))=
      address phaseCoordinate visit globalAddress := by
  funext column slot
  change BinaryRowColumns.scalar (ActivePrefixStageRuntimeOrdinal.highCoordinates
      (NativePolynomialStageShape.stage (CompactBinaryBasisSchedule.stage (node phaseCoordinate visit activeFits) pair)
        polynomialExponent metadataPrecision)
      (codecIndex rowCount polynomialExponent metadataPrecision
        (pack outerRow (FlatCoordinateLayout.index globalAddress polynomialIndex)))
      column (finCongr stageSlots.symm slot))=_
  have readout := CompactComplexEndpointCoordinates.high_coordinate
    (NativePolynomialStageShape.stage (CompactBinaryBasisSchedule.stage (node phaseCoordinate visit activeFits) pair)
      polynomialExponent metadataPrecision)
    (codecIndex rowCount polynomialExponent metadataPrecision
      (pack outerRow (FlatCoordinateLayout.index globalAddress polynomialIndex))) column (finCongr stageSlots.symm slot)
  rw [codec_row_coordinates] at readout
  refine readout.trans ?_
  apply congrArg globalAddress
  apply congrArg Fin.rev
  apply Fin.ext
  change shape.H+shape.B+ActivePrefixStageRuntimeOrdinal.originalPosition
    (CompactBinaryBasisSchedule.stage (node phaseCoordinate visit activeFits) pair) (finCongr stageSlots.symm slot) column=
    CompactSpectatorVisitGeometry.selected shape phaseCoordinate.val leftBoundary
      (CompactComplexNonleafChildAddress.axisIndex slot column).val
  have slotIdentity : finCongr stageSlots.symm slot=slot := Fin.ext rfl
  rw [slotIdentity]
  exact CompactComplexEndpointCoordinates.node_position phaseCoordinate visit activeFits pair slot column

/-- Inserting the chosen tensor address leaves the outer row and polynomial
index intact, and the actual codec readout recovers precisely that address. -/
theorem anchored_insert_coordinates {leftBoundary childExponent : ℕ}
    (phaseCoordinate : Fin shape.chunk) (visit : Visit shape.active leftBoundary (childExponent+1))
    (activeFits : shape.active≤shape.axes) (pair : BinaryRowProgram.Op (Fin arity))
    (rowCount polynomialExponent metadataPrecision : ℕ)
    (stageSlots : (CompactBinaryBasisSchedule.stage (node phaseCoordinate visit activeFits) pair).slots=arity)
    (outerRow : Fin rowCount) (anchor : BinaryWalsh.Address shape.bits)
    (polynomialIndex : Fin (2^polynomialExponent))
    (tensorAddress : BinaryColumns.Address arity (arity^childExponent)) :
    coordinates (CompactBinaryBasisSchedule.stage (node phaseCoordinate visit activeFits) pair)
      stageSlots rowCount polynomialExponent metadataPrecision
      (pack outerRow (FlatCoordinateLayout.index (insert phaseCoordinate visit anchor tensorAddress) polynomialIndex))=
      tensorAddress := by
  rw [node_coordinates,CompactComplexNonleafChildAddress.address_insert]

end
end IntegerMultBounds.Machine.CompactComplexCorrectedEntrySliceCoordinates
