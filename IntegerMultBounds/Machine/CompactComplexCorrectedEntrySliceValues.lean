module

public import IntegerMultBounds.Machine.CompactComplexCorrectedEntrySliceCoordinates
public import IntegerMultBounds.Machine.CompactComplexSourceReadyChildEventSemantics

/-! Literal cyclic input roles and actual corrected-entry output roles satisfy
correctInput on every anchored original node slice. Only the one coefficient
selected by that slice is used to connect physical phase readout with values;
no global input-coordinate or network equality is assumed. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexCorrectedEntrySliceValues
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit node)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Width Grid decoded)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactComplexScalarRowBlock (wireCount)
open CompactComplexScalarIntegerRows (wireIndex)
open CompactComplexScalarRolePorts (roleIndex)
open CompactComplexRolePhaseSite (roleEncoding)
open CompactComplexCorrectedEntryGridReadiness (coordinates parentIndex)
open CompactComplexCorrectedEntryGeometryReadiness (data)
open CompactComplexStoppedLeafTensorSemantics (slice)
open CompactComplexActualBasisPullback (nativeField)
open CompactComplexNonleafChildAddress (insert)
open RecursiveInterchangeRows (pack)
open Networks
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites
  CompactComplexRolePhaseSite.roleCount roleEncoding wireIndex

private theorem equiv_encoding {Original Scalar Port : Type*}
    (scalarEncoding : Original ≃ Scalar) (portEncoding : Original ≃ Port) (original : Original) :
    (scalarEncoding.symm.trans portEncoding) (scalarEncoding original)=portEncoding original := by
  simp only [Equiv.trans_apply,Equiv.symm_apply_apply]

private theorem role_index_encoding (wire : ComplexFramedExecution.Wire) :
    roleIndex (wireIndex wire)=roleEncoding wire := by
  unfold roleIndex
  exact equiv_encoding wireIndex roleEncoding wire

private theorem cast_roundtrip {firstCount lastCount : ℕ} (countEqual : firstCount=lastCount)
    (index : Fin lastCount) : Fin.cast countEqual (Fin.cast countEqual.symm index)=index := by
  cases countEqual
  rfl

variable {shape : Shape}

/-- The input is the literal original cyclic role split, in scalar wire order. -/
def inputRoles (rowCount polynomialExponent : ℕ) (rolesDivide : roles∣rowCount)
    (original : Array shape rowCount polynomialExponent) :
    Fin wireCount → Array shape (rowCount/roles) polynomialExponent :=
  fun scalarRole => CompactNativeRoleReservedBridge.role shape rowCount roles polynomialExponent rolesDivide original
    (roleIndex scalarRole)

/-- The output is the literal reached corrected-entry role array. -/
def outputRoles (stage : ActivePrefixStageParameters.Stage shape) (stageSlots : stage.slots=arity)
    (rowCount polynomialExponent metadataPrecision : ℕ) (rolesDivide : roles∣rowCount)
    (original : Array shape rowCount polynomialExponent) :
    Fin wireCount → Array shape (rowCount/roles) polynomialExponent :=
  fun scalarRole => CompactComplexCorrectedEntryGeometryReadiness.array stage stageSlots rowCount polynomialExponent
    metadataPrecision rolesDivide original (roleIndex scalarRole)

/-- The generic slice projection also covers node exponent one. -/
def sliceStored {leftBoundary childExponent : ℕ}
    (phaseCoordinate : Fin shape.chunk) (visit : Visit shape.active leftBoundary (childExponent+1))
    (rowCount polynomialExponent storagePrecision live : ℕ)
    (roleArrays : Fin wireCount → Array shape rowCount polynomialExponent)
    (outerRow : Fin rowCount) (polynomialIndex : Fin (2^polynomialExponent)) (anchor : BinaryWalsh.Address shape.bits) :
    ComplexFramedExecution.Wire → BinaryColumns.Arrays arity (arity^childExponent) :=
  fun wire => slice phaseCoordinate visit anchor (nativeField storagePrecision live (roleArrays (wireIndex wire)) outerRow polynomialIndex)

private theorem input_role_coefficient (rowCount polynomialExponent : ℕ) (rolesDivide : roles∣rowCount)
    (original : Array shape rowCount polynomialExponent) (wire : ComplexFramedExecution.Wire)
    (coefficient : Fin (rowCount/roles*(2^shape.bits*2^polynomialExponent))) :
    NativeEndpointCharacterEntryRoles.data rowCount polynomialExponent rolesDivide original wire
      (Fin.cast (NativeEndpointCharacterEntryRoles.cardinality shape rowCount polynomialExponent).symm coefficient)=
      inputRoles rowCount polynomialExponent rolesDivide original (wireIndex wire) coefficient := by
  unfold NativeEndpointCharacterEntryRoles.data inputRoles
  rw [cast_roundtrip,role_index_encoding]

private theorem input_role_decoded (rowCount polynomialExponent storagePrecision live : ℕ)
    (rolesDivide : roles∣rowCount) (original : Array shape rowCount polynomialExponent) (wire : ComplexFramedExecution.Wire)
    (coefficient : Fin (rowCount/roles*(2^shape.bits*2^polynomialExponent))) :
    decoded shape (rowCount/CompactComplexScalarCountLifecycle.roleDivisor) polynomialExponent storagePrecision live
      (NativeEndpointCharacterEntryRoles.data rowCount polynomialExponent rolesDivide original wire)
      (Fin.cast (NativeEndpointCharacterEntryRoles.cardinality shape rowCount polynomialExponent).symm coefficient)=
      decoded shape (rowCount/roles) polynomialExponent storagePrecision live
        (inputRoles rowCount polynomialExponent rolesDivide original (wireIndex wire)) coefficient := by
  unfold decoded
  rw [input_role_coefficient]

private theorem output_role_decoded (stage : ActivePrefixStageParameters.Stage shape) (stageSlots : stage.slots=arity)
    (rowCount polynomialExponent metadataPrecision storagePrecision live : ℕ) (rolesDivide : roles∣rowCount)
    (original : Array shape rowCount polynomialExponent) (wire : ComplexFramedExecution.Wire)
    (coefficient : Fin (rowCount/roles*(2^shape.bits*2^polynomialExponent))) :
    decoded shape (rowCount/roles) polynomialExponent storagePrecision live
      (outputRoles stage stageSlots rowCount polynomialExponent metadataPrecision rolesDivide original (wireIndex wire)) coefficient=
    decoded shape (rowCount/CompactComplexScalarCountLifecycle.roleDivisor) polynomialExponent storagePrecision live
      (data stage stageSlots rowCount polynomialExponent metadataPrecision rolesDivide original wire)
      (Fin.cast (NativeEndpointCharacterEntryRoles.cardinality shape rowCount polynomialExponent).symm coefficient) := by
  unfold decoded outputRoles CompactComplexCorrectedEntryGeometryReadiness.array
  rw [role_index_encoding,Equiv.symm_apply_apply]

private theorem coordinates_row_cast (stage : ActivePrefixStageParameters.Stage shape) (stageSlots : stage.slots=arity)
    (firstRows lastRows polynomialExponent metadataPrecision : ℕ) (rowEquality : firstRows=lastRows)
    (coefficient : Fin (lastRows*(2^shape.bits*2^polynomialExponent))) :
    coordinates stage stageSlots firstRows polynomialExponent metadataPrecision
      (Fin.cast (congrArg (fun rows => rows*(2^shape.bits*2^polynomialExponent)) rowEquality).symm coefficient)=
      coordinates stage stageSlots lastRows polynomialExponent metadataPrecision coefficient := by
  cases rowEquality
  rfl

/-- Adapt the source proof at one coefficient only. The two local equalities
are discharged by literal role splitting and actual codec coordinates below. -/
private theorem decoded_correctInput_at {leftBoundary nodeExponent dependencyLevels frameVolume returned : ℕ}
    (stage : ActivePrefixStageParameters.Stage shape) (stageSlots : stage.slots=arity)
    (rowCount polynomialExponent metadataPrecision storagePrecision : ℕ) (rolesDivide : roles∣rowCount)
    (original : Array shape rowCount polynomialExponent)
    (entryPath : CompactRecursiveDependencyBudget.Path shape.active leftBoundary nodeExponent dependencyLevels frameVolume returned)
    (baselinePrecision growthConstant live : ℕ) (baselineFits : baselinePrecision≤storagePrecision)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant≤shape.chunk)
    (originalWidth : Width shape rowCount polynomialExponent storagePrecision original)
    (originalGrid : Grid shape rowCount polynomialExponent storagePrecision live
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*returned)) original)
    (network : ComplexFramedExecution.Wire → BinaryColumns.Arrays arity stage.f)
    (networkAddress : BinaryColumns.Address arity stage.f)
    (coefficient : Fin (rowCount/CompactComplexScalarCountLifecycle.roleDivisor*(2^shape.bits*2^polynomialExponent)))
    (coordinateAt : coordinates stage stageSlots (rowCount/CompactComplexScalarCountLifecycle.roleDivisor)
      polynomialExponent metadataPrecision coefficient=networkAddress)
    (inputAt : ∀ wire,decoded shape rowCount polynomialExponent storagePrecision live original
      (parentIndex rowCount polynomialExponent rolesDivide wire coefficient)=network wire networkAddress) :
    ∀ wire,decoded shape (rowCount/CompactComplexScalarCountLifecycle.roleDivisor) polynomialExponent storagePrecision live
      (data stage stageSlots rowCount polynomialExponent metadataPrecision rolesDivide original wire) coefficient=
      ComplexEndpoints.correctInput stage.f network wire networkAddress := by
  have source := CompactComplexCorrectedEntryGridReadiness.decoded_source stage stageSlots rowCount polynomialExponent
    metadataPrecision storagePrecision rolesDivide original entryPath baselinePrecision growthConstant live baselineFits chunkRoom
    originalWidth originalGrid
  intro wire
  rw [congrFun (congrFun source wire) coefficient]
  rcases wire with inputWire | otherWire
  · change BinaryPhase.phase ((NativeEndpointCharacterPath.phase false stage stageSlots polynomialExponent metadataPrecision
        inputWire coefficient.val).val : ZMod 4)*_=_
    dsimp only
    rw [CompactComplexCorrectedEntryGridReadiness.phase_character,
      CompactComplexCorrectedEntryGridReadiness.input_decoded,inputAt,coordinateAt]
    exact (ComplexEndpoints.signColumns_apply _ _ _ _).symm
  · exact (CompactComplexCorrectedEntryGridReadiness.input_decoded rowCount polynomialExponent storagePrecision live
      rolesDivide original _ _).trans (inputAt _)

/-- Every actual corrected-entry source slice has the original corrected
network input values, with no supplied coordinate or network-input relation. -/
theorem slice_values {leftBoundary childExponent dependencyLevels frameVolume returned : ℕ}
    (phaseCoordinate : Fin shape.chunk) (visit : Visit shape.active leftBoundary (childExponent+1))
    (activeFits : shape.active≤shape.axes) (pair : BinaryRowProgram.Op (Fin arity))
    (rowCount polynomialExponent metadataPrecision storagePrecision live : ℕ)
    (stageSlots : (CompactBinaryBasisSchedule.stage (node phaseCoordinate visit activeFits) pair).slots=arity)
    (rolesDivide : roles∣rowCount) (original : Array shape rowCount polynomialExponent)
    (entryPath : CompactRecursiveDependencyBudget.Path shape.active leftBoundary (childExponent+1) dependencyLevels frameVolume returned)
    (baselinePrecision growthConstant : ℕ) (baselineFits : baselinePrecision≤storagePrecision)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant≤shape.chunk)
    (originalWidth : Width shape rowCount polynomialExponent storagePrecision original)
    (originalGrid : Grid shape rowCount polynomialExponent storagePrecision live
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*returned)) original)
    (outerRow : Fin (rowCount/roles)) (polynomialIndex : Fin (2^polynomialExponent)) (anchor : BinaryWalsh.Address shape.bits) :
    sliceStored phaseCoordinate visit (rowCount/roles) polynomialExponent storagePrecision live
      (outputRoles (CompactBinaryBasisSchedule.stage (node phaseCoordinate visit activeFits) pair) stageSlots
        rowCount polynomialExponent metadataPrecision rolesDivide original) outerRow polynomialIndex anchor=
    ComplexEndpoints.correctInput (arity^childExponent)
      (sliceStored phaseCoordinate visit (rowCount/roles) polynomialExponent storagePrecision live
        (inputRoles rowCount polynomialExponent rolesDivide original) outerRow polynomialIndex anchor) := by
  let stage := CompactBinaryBasisSchedule.stage (node phaseCoordinate visit activeFits) pair
  let inputNetwork := sliceStored phaseCoordinate visit (rowCount/roles) polynomialExponent storagePrecision live
    (inputRoles rowCount polynomialExponent rolesDivide original) outerRow polynomialIndex anchor
  funext wire tensorAddress
  let coefficient := pack outerRow (FlatCoordinateLayout.index (insert phaseCoordinate visit anchor tensorAddress) polynomialIndex)
  let namedCoefficient := Fin.cast (NativeEndpointCharacterEntryRoles.cardinality shape rowCount polynomialExponent).symm coefficient
  have coordinateAt : coordinates stage stageSlots (rowCount/CompactComplexScalarCountLifecycle.roleDivisor)
      polynomialExponent metadataPrecision namedCoefficient=tensorAddress := by
    exact (coordinates_row_cast stage stageSlots _ _ polynomialExponent metadataPrecision
      (NativeEndpointCharacterEntryRoles.quotient rowCount) coefficient).trans
      (CompactComplexCorrectedEntrySliceCoordinates.anchored_insert_coordinates phaseCoordinate visit activeFits pair
        (rowCount/roles) polynomialExponent metadataPrecision stageSlots outerRow anchor polynomialIndex tensorAddress)
  have inputAt : ∀ inputWire,decoded shape rowCount polynomialExponent storagePrecision live original
      (parentIndex rowCount polynomialExponent rolesDivide inputWire namedCoefficient)=inputNetwork inputWire tensorAddress := by
    intro inputWire
    have selectedInput := CompactComplexCorrectedEntryGridReadiness.input_decoded rowCount polynomialExponent storagePrecision live
      rolesDivide original inputWire namedCoefficient
    exact selectedInput.symm.trans
      (input_role_decoded rowCount polynomialExponent storagePrecision live rolesDivide original inputWire coefficient)
  have sourceValue := decoded_correctInput_at stage stageSlots rowCount polynomialExponent metadataPrecision storagePrecision
    rolesDivide original entryPath baselinePrecision growthConstant live baselineFits chunkRoom originalWidth originalGrid
    inputNetwork tensorAddress namedCoefficient coordinateAt inputAt wire
  exact (output_role_decoded stage stageSlots rowCount polynomialExponent metadataPrecision storagePrecision live
    rolesDivide original wire coefficient).trans sourceValue

/-- Specialization to the existing actual nonleaf stored-slice API. -/
theorem stored_values {leftBoundary childExponent dependencyLevels frameVolume returned : ℕ}
    (phaseCoordinate : Fin shape.chunk) (visit : Visit shape.active leftBoundary (childExponent+2))
    (activeFits : shape.active≤shape.axes) (pair : BinaryRowProgram.Op (Fin arity))
    (rowCount polynomialExponent metadataPrecision storagePrecision live : ℕ)
    (stageSlots : (CompactBinaryBasisSchedule.stage (node phaseCoordinate visit activeFits) pair).slots=arity)
    (rolesDivide : roles∣rowCount) (original : Array shape rowCount polynomialExponent)
    (entryPath : CompactRecursiveDependencyBudget.Path shape.active leftBoundary (childExponent+2) dependencyLevels frameVolume returned)
    (baselinePrecision growthConstant : ℕ) (baselineFits : baselinePrecision≤storagePrecision)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant≤shape.chunk)
    (originalWidth : Width shape rowCount polynomialExponent storagePrecision original)
    (originalGrid : Grid shape rowCount polynomialExponent storagePrecision live
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*returned)) original)
    (outerRow : Fin (rowCount/roles)) (polynomialIndex : Fin (2^polynomialExponent)) (anchor : BinaryWalsh.Address shape.bits) :
    CompactComplexSourceReadyChildEventSemantics.stored phaseCoordinate visit (rowCount/roles) polynomialExponent storagePrecision live
      (outputRoles (CompactBinaryBasisSchedule.stage (node phaseCoordinate visit activeFits) pair) stageSlots
        rowCount polynomialExponent metadataPrecision rolesDivide original) outerRow polynomialIndex anchor=
    ComplexEndpoints.correctInput (arity^(childExponent+1))
      (CompactComplexSourceReadyChildEventSemantics.stored phaseCoordinate visit (rowCount/roles) polynomialExponent storagePrecision live
        (inputRoles rowCount polynomialExponent rolesDivide original) outerRow polynomialIndex anchor) :=
  slice_values phaseCoordinate visit activeFits pair rowCount polynomialExponent metadataPrecision storagePrecision live stageSlots
    rolesDivide original entryPath baselinePrecision growthConstant baselineFits chunkRoom originalWidth originalGrid
    outerRow polynomialIndex anchor

end
end IntegerMultBounds.Machine.CompactComplexCorrectedEntrySliceValues
