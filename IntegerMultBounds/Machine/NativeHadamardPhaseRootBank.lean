module

public import IntegerMultBounds.Machine.NativeHadamardPhaseFixed
public import IntegerMultBounds.Machine.NativeEndpointNamedPorts
public import IntegerMultBounds.Machine.NativeEndpointSourceReadyPlacement
public import IntegerMultBounds.Machine.CompactComplexAlignedReachedNodeEntryPath
public import IntegerMultBounds.Machine.CompactComplexCorrectedEntrySliceCoordinates

/-! The fixed Hadamard phase correction runs on the literal original root bank.
Raw headers, source words and private placement are derived from that same bank;
no phase-input readiness, bank replacement or execution callback is assumed. -/

@[expose] public section
namespace IntegerMultBounds.Machine.NativeHadamardPhaseRootBank
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactComplexNativeCodecFrame (permanentTapes)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexAlignedReachedNodeEntryPath (originalBank)
variable {stackCount : ℕ} {shape : Shape} {rows ell : ℕ}
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount
  NativeHadamardPhaseFixed.program
  NativeHadamardPhaseOriginal.fixedWeights
  NativeHadamardPhaseReadout.weights NativeEndpointSourceReadyPlacement.program
  CompactComplexSourceReadyAlignedActualTable.liftPair

def source : Fin (NativeEndpointSourceReadyPlacement.callerTapes stackCount roles) :=
  Fin.castAdd 9 (CompactComplexSpectatorTargetBank.numericSlot (s:=10+stackCount) (c:=roles) 65)

def focus := NativeEndpointNamedPorts.focus (s:=10+stackCount) (u:=9)

theorem leaf_capacity : 67≤CompactComplexSourceReadyWorkspace.leafTapes := by
  norm_num [CompactComplexSourceReadyWorkspace.leafTapes,CompactSpectatorLeafOriginal.tapes,
    CompactSpectatorLeafOriginal.localCount,ButterflySpectatorPorts.count]

def binaryProgram := NativeEndpointSourceReadyPlacement.program (s:=stackCount) (c:=roles)
  (w:=CompactComplexSourceReadyScalarWorkspace.scratch) leaf_capacity
  (NativeHadamardPhaseFixed.program focus source)

/-- The unchanged alphabet lifting appends the existing basis workspace only. -/
def program := CompactComplexSourceReadyAlignedActualTable.liftPair ⟨_,binaryProgram (stackCount:=stackCount)⟩

def permanent (stage : Stage shape) (metadataPrecision : ℕ) (input : Array shape rows ell)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+stackCount) 2) :=
  CompactComplexNativeCodecFrame.bank control queue scalar (CompactComplexNativeCodec.raw stage rows ell metadataPrecision)
    tail storage (CompactNativeRoleReservedBridge.sourcePayload shape rows ell input roles)

private theorem source_replacement (stage : Stage shape) (metadataPrecision : ℕ)
    (input output : Array shape rows ell)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+stackCount) 2) (frame : Tapes 9 2) :
    SharedPlacementAlphabet.setTape ((permanent stage metadataPrecision input control queue scalar tail storage).append frame)
      source (NativeZeroPadding.word (NativeZeroPaddingArray.word output)) 0 =
      (permanent stage metadataPrecision output control queue scalar tail storage).append frame := by
  unfold source
  rw [SharedPlacementAlphabet.setTape_append_left]
  apply congrArg (fun bank : Tapes (permanentTapes (10+stackCount) roles) 2 => bank.append frame)
  unfold permanent CompactComplexNativeCodecFrame.bank CompactComplexNativeRoleBridge.bank
    CompactComplexSpectatorTargetBank.numericSlot CompactComplexControllerNativeFrame.nativeSlot
  rw [SharedPlacementAlphabet.setTape_append_left]
  unfold CompactComplexControllerNativeFrame.bank
  rw [SharedPlacementAlphabet.setTape_append_right,SharedPlacementAlphabet.setTape_append_right,
    SharedPlacementAlphabet.setTape_append_left]
  unfold CompactComplexNativeRoleBridge.native
  have sourceSplit : (65 : Fin 66)=Fin.natAdd 43 (Fin.natAdd 22 (0 : Fin 1)) := rfl
  rw [sourceSplit,SharedPlacementAlphabet.setTape_append_right,SharedPlacementAlphabet.setTape_append_right]
  have singleOutput : SharedPlacementAlphabet.setTape
      (CompactComplexNativeRoleBridge.single (CompactNativeRoleReservedBridge.sourcePayload shape rows ell input roles))
      0 (NativeZeroPadding.word (NativeZeroPaddingArray.word output)) 0 =
        CompactComplexNativeRoleBridge.single (CompactNativeRoleReservedBridge.sourcePayload shape rows ell output roles) := by
    apply congrArg₂ Tapes.mk <;> funext index <;> fin_cases index <;> rfl
  rw [singleOutput]
  have roleOutput : CompactNativeRoleSourcePorts.roles
      (CompactNativeRoleReservedBridge.sourcePayload shape rows ell input roles) =
        CompactNativeRoleSourcePorts.roles (CompactNativeRoleReservedBridge.sourcePayload shape rows ell output roles) := by
    apply congrArg₂ Tapes.mk <;> funext role
    all_goals have roleSplit : (⟨role.val+1,by omega⟩ : Fin (1+roles))=Fin.natAdd 1 role := Fin.ext (by change role.val+1=1+role.val; omega)
    all_goals simp only [roleSplit,
      CompactNativeRoleReservedBridge.sourcePayload,CyclicRowCopy.payload,Tapes.append,Fin.addCases_right]
  rw [roleOutput]

/-- Physical phase correction from the actual original source-ready bank.
All raw-header/source prerequisites derive from the canonical constructor;
the frame, storage, leaf remainder and scalar suffix are retained literally. -/
theorem binary_runs (stage : Stage shape) (metadataPrecision : ℕ) (stageSlots : stage.slots=arity)
    (rowsPositive : 0<rows) (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes)
    (guardFits : shape.guard+1≤shape.chunk) (unitPayload : shape.payload=1)
    (input : Array shape rows ell)
    (inputWidth : ∀ index, (input index).1.length=NativePolynomialStageShape.width shape metadataPrecision ∧
      (input index).2.length=NativePolynomialStageShape.width shape metadataPrecision)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+stackCount) 2) (frame : Tapes 9 2)
    (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (leafBlank : ∀ index : Fin 67,leaf.head ⟨index.val,lt_of_lt_of_le index.isLt leaf_capacity⟩=0 ∧
      leaf.tape ⟨index.val,lt_of_lt_of_le index.isLt leaf_capacity⟩=(fun _ => blank)) :
    HoareTime (binaryProgram (stackCount:=stackCount))
      (fun bank => bank=(CompactComplexSourceReadyNonleafContraction.ready
        (permanent stage metadataPrecision input control queue scalar tail storage) frame leaf).append scratch)
      (fun bank => bank=(CompactComplexSourceReadyNonleafContraction.ready
        (permanent stage metadataPrecision (NativeHadamardPhaseOriginal.result stage metadataPrecision input)
          control queue scalar tail storage) frame leaf).append scratch)
      (NativeHadamardPhaseOriginal.constant*CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision) := by
  have phaseRun := NativeHadamardPhaseFixed.runs focus source
    ((permanent stage metadataPrecision input control queue scalar tail storage).append frame)
    stage metadataPrecision stageSlots rowsPositive guardPositive axesPositive guardFits unitPayload input inputWidth
    (by
      intro header
      exact (NativeEndpointNamedPorts.focus_bank control queue scalar
        (CompactComplexNativeCodec.raw stage rows ell metadataPrecision) tail storage
        (CompactNativeRoleReservedBridge.sourcePayload shape rows ell input roles) frame header).2.trans
          (by fin_cases header <;> rfl))
    (by
      intro header
      exact (NativeEndpointNamedPorts.focus_bank control queue scalar
        (CompactComplexNativeCodec.raw stage rows ell metadataPrecision) tail storage
        (CompactNativeRoleReservedBridge.sourcePayload shape rows ell input roles) frame header).1.trans
          (by fin_cases header <;> rfl))
    (by
      have sourceSplit : (65 : Fin 66)=Fin.natAdd 43 (Fin.natAdd 22 (0 : Fin 1)) := rfl
      simp only [source,permanent,CompactComplexNativeCodecFrame.bank,CompactComplexNativeRoleBridge.bank,
        CompactComplexSpectatorTargetBank.numericSlot,CompactComplexControllerNativeFrame.nativeSlot,
        CompactComplexControllerNativeFrame.bank,CompactComplexNativeRoleBridge.native,sourceSplit,
        Tapes.append,Fin.addCases_left,Fin.addCases_right,CompactComplexNativeRoleBridge.single,
        CompactNativeRoleReservedBridge.sourcePayload,CyclicRowCopy.payload]
      rfl)
    (by
      have sourceSplit : (65 : Fin 66)=Fin.natAdd 43 (Fin.natAdd 22 (0 : Fin 1)) := rfl
      simp only [source,permanent,CompactComplexNativeCodecFrame.bank,CompactComplexNativeRoleBridge.bank,
        CompactComplexSpectatorTargetBank.numericSlot,CompactComplexControllerNativeFrame.nativeSlot,
        CompactComplexControllerNativeFrame.bank,CompactComplexNativeRoleBridge.native,sourceSplit,
        Tapes.append,Fin.addCases_left,Fin.addCases_right,CompactComplexNativeRoleBridge.single,
        CompactNativeRoleReservedBridge.sourcePayload,CyclicRowCopy.payload]
      rfl)
  have outputBank : NativeHadamardPhaseOriginal.resultCaller
      ((permanent stage metadataPrecision input control queue scalar tail storage).append frame)
      source stage metadataPrecision input =
        (permanent stage metadataPrecision (NativeHadamardPhaseOriginal.result stage metadataPrecision input)
          control queue scalar tail storage).append frame :=
    source_replacement stage metadataPrecision input _ control queue scalar tail storage frame
  have exactPhaseRun := phaseRun.consequence (fun bank equality => equality)
    (fun bank equality => equality.trans (congrArg
      (fun caller : Tapes (NativeEndpointSourceReadyPlacement.callerTapes stackCount roles) 2 =>
        caller.append (FixedHeaderBankCopy.empty 67)) outputBank)) le_rfl
  unfold binaryProgram
  have placed := NativeEndpointSourceReadyPlacement.runs (s:=stackCount) (c:=roles)
    (w:=CompactComplexSourceReadyScalarWorkspace.scratch)
    (M:=NativeHadamardPhaseFixed.program (focus (stackCount:=stackCount)) source)
    leaf_capacity _ _ frame leaf scratch leafBlank exactPhaseRun
  exact placed

/-- The same physical correction executes on precisely originalBank used by
the checked fixed-program root contracts, preserving all appended basis tapes. -/
theorem runs (stage : Stage shape) (metadataPrecision : ℕ) (stageSlots : stage.slots=arity)
    (rowsPositive : 0<rows) (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes)
    (guardFits : shape.guard+1≤shape.chunk) (unitPayload : shape.payload=1)
    (input : Array shape rows ell)
    (inputWidth : ∀ index, (input index).1.length=NativePolynomialStageShape.width shape metadataPrecision ∧
      (input index).2.length=NativePolynomialStageShape.width shape metadataPrecision)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+stackCount) 2) (auxiliary : Tapes 2 2) :
    HoareTime (program (stackCount:=stackCount)).2
      (fun bank => bank=originalBank stage rows ell metadataPrecision input control queue scalar tail storage auxiliary)
      (fun bank => bank=originalBank stage rows ell metadataPrecision
        (NativeHadamardPhaseOriginal.result stage metadataPrecision input) control queue scalar tail storage auxiliary)
      (NativeHadamardPhaseOriginal.constant*CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision) := by
  have phaseRun := binary_runs stage metadataPrecision stageSlots rowsPositive guardPositive axesPositive guardFits
    unitPayload input inputWidth control queue scalar tail storage (auxiliary.append (SharedBank.empty 7 2))
    (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2)
    (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2) (by intro index; constructor <;> rfl)
  have lifted := CompactComplexSourceReadyAlignedActualTable.lift_runs (s:=stackCount)
    (binaryProgram (stackCount:=stackCount)) _ _
    (SharedBank.empty (CompactComplexActualCallFullAlignment.localTapes roles) Networks.Shared50ModularControl.prime)
    phaseRun
  unfold program
  exact lifted

/-- The literal phase coefficient on the actual root word is the required
tensor correction at its own original row, polynomial and spectator address. -/
theorem phase_at_node {left exponent : ℕ} (phaseCoordinate : Fin shape.chunk)
    (visit : CompactComplexRecursiveGeometry.Visit shape.active left (exponent+1))
    (activeFits : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (metadataPrecision : ℕ) (rawRow : Fin rows) (polynomialIndex : Fin (2^ell))
    (globalAnchor : Networks.BinaryWalsh.Address shape.bits) :
    Networks.BinaryPhase.phase ((AllAxisPolynomialLiteralEndpoint.phase
      (NativePolynomialStageShape.stage (CompactBinaryBasisSchedule.stage (CompactComplexRecursiveGeometry.node phaseCoordinate visit activeFits) pair)
        ell metadataPrecision) arity NativeHadamardPhaseOriginal.fixedWeights
      ((RecursiveInterchangeRows.pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex)).val/2^ell)).val : ZMod 4) =
      ∏ column : Fin (arity^exponent), Networks.BinaryPhase.phase (Networks.BinaryPhase.weightPhase
        (CompactComplexNonleafChildAddress.address phaseCoordinate visit globalAnchor column)) := by
  rw [NativeHadamardPhaseOriginal.phase_readout _ _ rfl]
  have codecIndex : NativeHadamardPhaseOriginal.recordIndex metadataPrecision
      (RecursiveInterchangeRows.pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex)) =
      CompactComplexCorrectedEntryGridReadiness.codecIndex rows ell metadataPrecision
        (RecursiveInterchangeRows.pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex)) := Fin.ext rfl
  rw [codecIndex]
  have nodeCoordinates := CompactComplexCorrectedEntrySliceCoordinates.node_coordinates
    phaseCoordinate visit activeFits pair rows ell metadataPrecision rfl rawRow globalAnchor polynomialIndex
  have coordinatesEquation : (fun column => NativeEndpointCharacterReadout.coordinates
      (NativePolynomialStageShape.stage
        (CompactBinaryBasisSchedule.stage (CompactComplexRecursiveGeometry.node phaseCoordinate visit activeFits) pair)
        ell metadataPrecision)
      (CompactComplexCorrectedEntryGridReadiness.codecIndex rows ell metadataPrecision
        (RecursiveInterchangeRows.pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex))) column) =
        CompactComplexNonleafChildAddress.address phaseCoordinate visit globalAnchor := by
    funext column slot
    have atSlot := congrFun (congrFun nodeCoordinates column) slot
    let stage := CompactBinaryBasisSchedule.stage (CompactComplexRecursiveGeometry.node phaseCoordinate visit activeFits) pair
    have stageSlots : stage.slots=arity := rfl
    change NativeEndpointCharacterReadout.coordinates (NativePolynomialStageShape.stage stage ell metadataPrecision)
      (CompactComplexCorrectedEntryGridReadiness.codecIndex rows ell metadataPrecision
        (RecursiveInterchangeRows.pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex)))
      column (finCongr stageSlots.symm slot) =
        CompactComplexNonleafChildAddress.address phaseCoordinate visit globalAnchor column slot at atSlot
    have slotIdentity : finCongr stageSlots.symm slot=slot := Fin.ext rfl
    exact (congrArg (fun selectedSlot => NativeEndpointCharacterReadout.coordinates
      (NativePolynomialStageShape.stage stage ell metadataPrecision)
      (CompactComplexCorrectedEntryGridReadiness.codecIndex rows ell metadataPrecision
        (RecursiveInterchangeRows.pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex)))
      column selectedSlot) slotIdentity).symm.trans atSlot
  exact congrArg (fun tensorAddress : Networks.BinaryColumns.Address arity (arity^exponent) =>
    ∏ column, Networks.BinaryPhase.phase (Networks.BinaryPhase.weightPhase (tensorAddress column))) coordinatesEquation

/-- Original dependency Paths justify the same physical phase readout on actual
root coefficients, without numerical guards or tensor compatibility premises. -/
theorem decoded_at_node {left exponent levels frames returned : ℕ} (phaseCoordinate : Fin shape.chunk)
    (path : CompactRecursiveDependencyBudget.Path shape.active left (exponent+1) levels frames returned)
    (activeFits : shape.active≤shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (precision baseline growthConstant denominator : ℕ) (baselineFits : baseline≤precision)
    (dependencyFits : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant≤shape.chunk)
    (input : Array shape rows ell) (inputWidth : CompactSpectatorInheritedGrid.Width shape rows ell precision input)
    (inputGrid : CompactSpectatorInheritedGrid.Grid shape rows ell precision denominator
      (CompactRecursiveGridBudget.bound baseline growthConstant levels (frames+2*returned)) input)
    (rawRow : Fin rows) (polynomialIndex : Fin (2^ell)) (globalAnchor : Networks.BinaryWalsh.Address shape.bits) :
    CompactSpectatorInheritedGrid.decoded shape rows ell precision denominator
      (NativeHadamardPhaseOriginal.result (CompactBinaryBasisSchedule.stage (CompactComplexRecursiveGeometry.node phaseCoordinate path.visit activeFits) pair)
        (ButterflyIndependentGuardHeaders.reservation shape.bits precision) input)
      (RecursiveInterchangeRows.pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex)) =
      (∏ column : Fin (arity^exponent), Networks.BinaryPhase.phase (Networks.BinaryPhase.weightPhase
        (CompactComplexNonleafChildAddress.address phaseCoordinate path.visit globalAnchor column))) *
      CompactSpectatorInheritedGrid.decoded shape rows ell precision denominator input
        (RecursiveInterchangeRows.pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex)) := by
  rw [CompactSpectatorInheritedGrid.decoded,NativeHadamardPhaseOriginal.signed_decoded]
  · rw [phase_at_node]
    rfl
  · intro index
    simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using inputWidth index
  · exact fun index => CompactSpectatorInheritedGrid.signed_guards_from_path shape rows ell precision
      path baseline growthConstant denominator baselineFits dependencyFits input inputGrid index

end
end IntegerMultBounds.Machine.NativeHadamardPhaseRootBank
