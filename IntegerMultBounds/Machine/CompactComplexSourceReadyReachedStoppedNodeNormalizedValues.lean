module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedStoppedNodeTensorValues
public import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafOrientedSemantics
public import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedRoleRejoin

/-! Literal signed contraction and cyclic recombination of the actual stopped
node's computed sink arrays, with a shared proof for arbitrary recursive
schedules. These are mathematical output arrays; physical
execution of the final contraction and merge is a separate theorem. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedStoppedNodeNormalizedValues
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Grid Width decoded half)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactComplexScalarRowBlock (wireCount)
open CompactComplexScalarIntegerRows (wireIndex)
open CompactComplexScalarRolePorts (roleIndex)
open CompactComplexSourceReadyChildEventSemantics (stored)
open CompactComplexControllerExactReturn (contracted)
open Networks
open RecursiveInterchangeRows (pack)
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites
  CompactComplexRolePhaseSite.roleCount CompactComplexRolePhaseSite.roleEncoding wireIndex

/-- The real physical cyclic wire order, including untouched spectators. -/
def physicalRowLayout (rowCount : ℕ) (rolesDivide : roles∣rowCount) :
    (Fin (rowCount/roles) × ComplexFramedExecution.Wire) ≃ Fin rowCount :=
  ((Equiv.prodCongr (Equiv.refl _) CompactComplexRolePhaseSite.roleEncoding).trans finProdFinEquiv).trans
    (finCongr (Nat.div_mul_cancel rolesDivide))

def physicalLayout (shape : Shape) (rowCount polynomialExponent : ℕ) (rolesDivide : roles∣rowCount) :
    ((Fin (rowCount/roles) × ComplexFramedExecution.Wire) ×
      (BinaryWalsh.Address shape.bits × Fin (2^polynomialExponent))) ≃
      Fin (ButterflySpectatorGeometry.Size rowCount shape.bits (2^polynomialExponent)) :=
  (Equiv.prodCongr (physicalRowLayout rowCount rolesDivide) FlatCoordinateLayout.arrayEquiv).trans finProdFinEquiv

private theorem physical_role_layout (shape : Shape) (rowCount polynomialExponent : ℕ)
    (rolesDivide : roles∣rowCount) (data : Array shape rowCount polynomialExponent)
    (row : Fin (rowCount/roles)) (wire : ComplexFramedExecution.Wire)
    (anchor : BinaryWalsh.Address shape.bits) (polynomialIndex : Fin (2^polynomialExponent)) :
    CompactNativeRoleReservedBridge.role shape rowCount roles polynomialExponent rolesDivide data
      (CompactComplexRolePhaseSite.roleEncoding wire) (pack row (FlatCoordinateLayout.index anchor polynomialIndex))=
      data (physicalLayout shape rowCount polynomialExponent rolesDivide ((row,wire),(anchor,polynomialIndex))) := by
  refine (CompactNativeRoleReservedBridge.global_index shape rowCount roles polynomialExponent rolesDivide data row
    (CompactComplexRolePhaseSite.roleEncoding wire) (FlatCoordinateLayout.index anchor polynomialIndex)).trans ?_
  apply congrArg data
  apply Fin.ext
  rfl

private theorem role_index_encoding (wire : ComplexFramedExecution.Wire) :
    roleIndex (wireIndex wire)=CompactComplexRolePhaseSite.roleEncoding wire := by
  unfold roleIndex
  simp only [Equiv.trans_apply,Equiv.symm_apply_apply]

private theorem normalized_tensor_layout {shape : Shape} {nodeLeft childExponent : ℕ}
    (phaseCoordinate : Fin shape.chunk) (visit : Visit shape.active nodeLeft (childExponent+2))
    (rowCount polynomialExponent storagePrecision initialLive finalLive : ℕ) (rolesDivide : roles∣rowCount)
    (original : Array shape rowCount polynomialExponent)
    (sink : Fin wireCount → Array shape (rowCount/roles) polynomialExponent)
    (contractionExact : ∀ scalarRole index,
      decoded shape (rowCount/roles) polynomialExponent storagePrecision
        (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1))
        (contracted (finalLive-CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1))
          (sink scalarRole)) index=
      decoded shape (rowCount/roles) polynomialExponent storagePrecision finalLive (sink scalarRole) index)
    (tensorValues : ∀ row polynomialIndex anchor,
      stored phaseCoordinate visit (rowCount/roles) polynomialExponent storagePrecision finalLive sink row polynomialIndex anchor=
      fun wire => ComplexEndpoints.fullFrame (arity^(childExponent+1))
        (stored phaseCoordinate visit (rowCount/roles) polynomialExponent storagePrecision initialLive
          (CompactComplexCorrectedEntrySliceValues.inputRoles rowCount polynomialExponent rolesDivide original)
          row polynomialIndex anchor wire))
    (row : Fin (rowCount/roles)) (wire : ComplexFramedExecution.Wire)
    (anchor : BinaryWalsh.Address shape.bits) (polynomialIndex : Fin (2^polynomialExponent)) :
    decoded shape rowCount polynomialExponent storagePrecision
      (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1))
      (normalized rowCount polynomialExponent finalLive
        (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivide sink)
      (physicalLayout shape rowCount polynomialExponent rolesDivide ((row,wire),(anchor,polynomialIndex)))=
    ComplexEndpoints.fullFrame (arity^(childExponent+1))
      (fun tensorAddress => decoded shape rowCount polynomialExponent storagePrecision initialLive original
        (physicalLayout shape rowCount polynomialExponent rolesDivide
          ((row,wire),(CompactComplexNonleafChildAddress.insert phaseCoordinate visit anchor tensorAddress,polynomialIndex))))
      (CompactComplexNonleafChildAddress.address phaseCoordinate visit anchor) := by
  have normalizedAt := physical_role_layout shape rowCount polynomialExponent rolesDivide
    (normalized rowCount polynomialExponent finalLive
      (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivide sink)
    row wire anchor polynomialIndex
  rw [←role_index_encoding,normalized_role] at normalizedAt
  have normalizedDecoded := congrArg
    (ButterflyStreamSemantics.decode (half shape storagePrecision)
      (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1))) normalizedAt
  change decoded shape (rowCount/roles) polynomialExponent storagePrecision
      (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1))
      (contracted (finalLive-CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1))
        (sink (wireIndex wire))) (pack row (FlatCoordinateLayout.index anchor polynomialIndex))=_ at normalizedDecoded
  rw [contractionExact] at normalizedDecoded
  have selectedValue := congrFun (congrFun (tensorValues row polynomialIndex anchor) wire)
    (CompactComplexNonleafChildAddress.address phaseCoordinate visit anchor)
  have sinkAt : stored phaseCoordinate visit (rowCount/roles) polynomialExponent storagePrecision finalLive sink
      row polynomialIndex anchor wire (CompactComplexNonleafChildAddress.address phaseCoordinate visit anchor)=
    decoded shape (rowCount/roles) polynomialExponent storagePrecision finalLive
      (sink (wireIndex wire)) (pack row (FlatCoordinateLayout.index anchor polynomialIndex)) := by
    simp only [stored,CompactComplexStoppedLeafTensorSemantics.slice,
      CompactComplexActualBasisPullback.nativeField,CompactComplexNonleafChildAddress.insert_address]
  rw [sinkAt] at selectedValue
  refine normalizedDecoded.symm.trans (selectedValue.trans ?_)
  apply congrArg (fun field => ComplexEndpoints.fullFrame (arity^(childExponent+1)) field
    (CompactComplexNonleafChildAddress.address phaseCoordinate visit anchor))
  funext tensorAddress
  unfold stored CompactComplexStoppedLeafTensorSemantics.slice CompactComplexActualBasisPullback.nativeField
    CompactComplexCorrectedEntrySliceValues.inputRoles decoded
  rw [role_index_encoding,physical_role_layout]

private theorem full_tensor_grid {shape : Shape} {nodeLeft childExponent rowCount polynomialExponent : ℕ}
    (phaseCoordinate : Fin shape.chunk) (visit : Visit shape.active nodeLeft (childExponent+2))
    (storagePrecision initialLive finalLive numeratorBound : ℕ)
    (before sink : Fin wireCount → Array shape rowCount polynomialExponent)
    (inputGrid : ∀ scalarRole,Grid shape rowCount polynomialExponent storagePrecision initialLive numeratorBound (before scalarRole))
    (tensorValues : ∀ row polynomialIndex anchor,
      stored phaseCoordinate visit rowCount polynomialExponent storagePrecision finalLive sink row polynomialIndex anchor=
      fun wire => ComplexEndpoints.fullFrame (arity^(childExponent+1))
        (stored phaseCoordinate visit rowCount polynomialExponent storagePrecision initialLive before row polynomialIndex anchor wire)) :
    ∀ scalarRole index,GaussianPrecision.BoundedGrid
      (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1))
      (numeratorBound*4^(2*arity^(childExponent+2)))
      (decoded shape rowCount polynomialExponent storagePrecision finalLive (sink scalarRole) index) := by
  intro scalarRole index
  let rowSuffix := finProdFinEquiv.symm index
  let anchorPolynomial := FlatCoordinateLayout.arrayEquiv.symm rowSuffix.2
  have indexCoordinates : pack rowSuffix.1
      (FlatCoordinateLayout.index anchorPolynomial.1 anchorPolynomial.2)=index := by
    change finProdFinEquiv (rowSuffix.1,FlatCoordinateLayout.arrayEquiv anchorPolynomial)=index
    rw [Equiv.apply_symm_apply]
    exact finProdFinEquiv.apply_symm_apply index
  let selectedAddress : BinaryColumns.Address (25^3) (arity^(childExponent+1)) :=
    CompactComplexNonleafChildAddress.address phaseCoordinate visit anchorPolynomial.1
  have selectedValue := congrFun (congrFun (tensorValues rowSuffix.1 anchorPolynomial.2 anchorPolynomial.1)
      (wireIndex.symm scalarRole)) selectedAddress
  have inputSlices : ∀ wire address,GaussianPrecision.BoundedGrid initialLive numeratorBound
      (stored phaseCoordinate visit rowCount polynomialExponent storagePrecision initialLive before
        rowSuffix.1 anchorPolynomial.2 anchorPolynomial.1 wire address) := by
    intro wire address
    exact inputGrid (wireIndex wire) _
  have targetGrid := CompactComplexSourceReadyNonleafOrientedSemantics.corrected_grid initialLive
    (childExponent+1) numeratorBound
    (stored phaseCoordinate visit rowCount polynomialExponent storagePrecision initialLive before
      rowSuffix.1 anchorPolynomial.2 anchorPolynomial.1) inputSlices (wireIndex.symm scalarRole) selectedAddress
  rw [ComplexEndpoints.corrected_network_run] at targetGrid
  have selectedGrid : GaussianPrecision.BoundedGrid
      (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1))
      (numeratorBound*4^(2*arity^(childExponent+2)))
      (stored phaseCoordinate visit rowCount polynomialExponent storagePrecision finalLive sink
        rowSuffix.1 anchorPolynomial.2 anchorPolynomial.1 (wireIndex.symm scalarRole) selectedAddress) :=
    selectedValue.symm ▸ targetGrid
  simpa only [stored,CompactComplexStoppedLeafTensorSemantics.slice,
    CompactComplexActualBasisPullback.nativeField,Equiv.apply_symm_apply,
    selectedAddress,CompactComplexNonleafChildAddress.insert_address,indexCoordinates,
    Nat.add_assoc] using selectedGrid

private theorem contract_and_rejoin {shape : Shape} (rowCount polynomialExponent storagePrecision current target numeratorBound : ℕ)
    (rolesDivide : roles∣rowCount)
    (sink : Fin wireCount → Array shape (rowCount/roles) polynomialExponent)
    (targetCoverage : target≤current) (currentCapacity : current≤half shape storagePrecision+1)
    (sinkWidth : ∀ scalarRole index,(sink scalarRole index).1.length=half shape storagePrecision+1 ∧
      (sink scalarRole index).2.length=half shape storagePrecision+1)
    (sinkGrid : ∀ scalarRole index,GaussianPrecision.BoundedGrid target numeratorBound
      (decoded shape (rowCount/roles) polynomialExponent storagePrecision current (sink scalarRole) index)) :
    (∀ scalarRole index,decoded shape (rowCount/roles) polynomialExponent storagePrecision target
      (contracted (current-target) (sink scalarRole)) index=
      decoded shape (rowCount/roles) polynomialExponent storagePrecision current (sink scalarRole) index) ∧
    (∀ index,(normalized rowCount polynomialExponent current target rolesDivide sink index).1.length=half shape storagePrecision+1 ∧
      (normalized rowCount polynomialExponent current target rolesDivide sink index).2.length=half shape storagePrecision+1) ∧
    Grid shape rowCount polynomialExponent storagePrecision target numeratorBound
      (normalized rowCount polynomialExponent current target rolesDivide sink) := by
  have contraction := fun scalarRole => CompactComplexControllerExactReturn.contracted_exact
    (sink scalarRole) (half shape storagePrecision) current target numeratorBound targetCoverage
    (by omega) (sinkWidth scalarRole) (sinkGrid scalarRole)
  have contractionExact : ∀ scalarRole index,
      decoded shape (rowCount/roles) polynomialExponent storagePrecision target
        (contracted (current-target) (sink scalarRole)) index=
      decoded shape (rowCount/roles) polynomialExponent storagePrecision current (sink scalarRole) index :=
    fun scalarRole => (contraction scalarRole).2
  refine ⟨contractionExact,?_,?_⟩
  · exact CompactNativeRoleRecombine.width shape rowCount roles polynomialExponent _ rolesDivide _
      (fun port => (contraction (roleIndex.symm port)).1)
  · apply CompactNativeRoleRecombine.grid
    intro port index
    rw [contractionExact]
    exact sinkGrid (roleIndex.symm port) index

open CompactComplexChildHeadersData (parent)
open CompactComplexScalarIntegerRows (GroupIndex gates guardBits)
open CompactComplexCompletedLiveLower (schedule)
open CompactComplexSourceReadyReachedEventTrace (State Execution)
open CompactComplexSourceReadyReachedEventFrameState (FrameState capture)
open CompactComplexSourceReadyReachedStoppedSchedule (totalBudget)
open Networks.Shared50ModularControl (prime)
attribute [local irreducible] schedule totalBudget

section Node
variable {stackCount basisStateCount : ℕ} {shape : Shape}
  {nodeLeft childExponent dependencyLevels frameVolume entryReturned : ℕ}
  {rowCount polynomialExponent inputPrecision baselinePrecision growthConstant baselineLive initialLive : ℕ}
  {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
  (phaseCoordinate : Fin shape.chunk)
  (entryPath : CompactRecursiveDependencyBudget.Path shape.active nodeLeft (childExponent+2)
    dependencyLevels frameVolume entryReturned)
  (activeFits : shape.active ≤ shape.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))

/-- Literal normalization of an arbitrary actually executed recursive node
schedule. Raw compiler values are corrected internally, terminal capacity and
target coverage follow from the actual reached frame and execution, and the
original cyclic layout is preserved. No stopping assumption is required. -/
theorem normalize_of_schedule
    (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime)
    (headerStack liveStack : Fin stackCount)
    (originalCoefficients : CompactSpectatorVisitGeometry.Array shape rowCount polynomialExponent)
    (inputWidth : CompactSpectatorInheritedGrid.Width shape rowCount polynomialExponent inputPrecision originalCoefficients)
    (inputGrid : CompactSpectatorInheritedGrid.Grid shape rowCount polynomialExponent inputPrecision initialLive
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*entryReturned)) originalCoefficients)
    (baselineFitsPrecision : baselinePrecision≤ inputPrecision)
    (parentSlots : (parent phaseCoordinate entryPath.visit activeFits pair).slots=25^3)
    (rolesDivideRows : roles∣rowCount)
    (initialState : State (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=savedCalls) 0 initialLive)
    (entryData : initialState.reached.data=(fun arrayIndex => CompactComplexCorrectedEntryGeometryReadiness.array
      (parent phaseCoordinate entryPath.visit activeFits pair) parentSlots rowCount polynomialExponent
      (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) rolesDivideRows originalCoefficients
      (CompactComplexScalarRolePorts.roleIndex arrayIndex)))
    (finalLive : ℕ) (finalBoundary : FrameState (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=(ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision))
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=savedCalls) (capture initialState headerStack liveStack)
      initialState.reached.targetValue schedule.length finalLive)
    (elapsedSteps : ℕ)
    (actualTrace : Execution basisProgram headerStack liveStack initialLive initialState finalBoundary.state elapsedSteps)
    (networkValues : ∀ (row : Fin (rowCount/roles)) (polynomialIndex : Fin (2^polynomialExponent))
        (globalAnchor : Networks.BinaryWalsh.Address shape.bits),
      stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent
        ((ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)-2*shape.bits)
        finalLive finalBoundary.state.reached.data row polynomialIndex globalAnchor=
      Networks.FramedCircuit.run (Networks.ComplexFramedExecution.network (arity^(childExponent+1)))
        (stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent
          ((ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)-2*shape.bits)
          initialLive initialState.reached.data row polynomialIndex globalAnchor))
    (activePositive : 0<shape.active)
    (precisionReserve : baselinePrecision+2*shape.bits≤ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (childChunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      CompactComplexScalarIntegerRows.guardBits≤shape.chunk)
    (baselineFits : baselineLive≤baselinePrecision)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤shape.chunk) :
    (∀ (row : Fin (rowCount/roles)) (polynomialIndex : Fin (2^polynomialExponent))
          (globalAnchor : Networks.BinaryWalsh.Address shape.bits),
          stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent inputPrecision finalLive
            (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair)
              parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
              finalBoundary.state.reached.data) row polynomialIndex globalAnchor=
            fun wire => Networks.ComplexEndpoints.fullFrame (arity^(childExponent+1))
              (stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent inputPrecision initialLive
                (CompactComplexCorrectedEntrySliceValues.inputRoles rowCount polynomialExponent rolesDivideRows originalCoefficients)
                row polynomialIndex globalAnchor wire)) ∧
        (∀ index,((normalized rowCount polynomialExponent finalLive (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivideRows (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair) parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) finalBoundary.state.reached.data)) index).1.length=half shape inputPrecision+1 ∧
          ((normalized rowCount polynomialExponent finalLive (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivideRows (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair) parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) finalBoundary.state.reached.data)) index).2.length=half shape inputPrecision+1) ∧
        Grid shape rowCount polynomialExponent inputPrecision (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) ((CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*entryReturned))*4^(2*arity^(childExponent+2))) (normalized rowCount polynomialExponent finalLive (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivideRows (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair) parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) finalBoundary.state.reached.data)) ∧
        (∀ scalarRole index,decoded shape (rowCount/roles) polynomialExponent inputPrecision (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1))
          (CompactNativeRoleReservedBridge.role shape rowCount roles polynomialExponent rolesDivideRows (normalized rowCount polynomialExponent finalLive (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivideRows (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair) parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) finalBoundary.state.reached.data))
            (roleIndex scalarRole)) index=
          decoded shape (rowCount/roles) polynomialExponent inputPrecision finalLive
            ((CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair) parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) finalBoundary.state.reached.data) scalarRole) index) ∧
        (∀ (rawRow : Fin rowCount) (polynomialIndex : Fin (2^polynomialExponent))
          (globalAnchor : BinaryWalsh.Address shape.bits),
          decoded shape rowCount polynomialExponent inputPrecision
            (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1))
            (normalized rowCount polynomialExponent finalLive
              (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivideRows
              (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair)
                parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
                finalBoundary.state.reached.data))
            (pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex))=
          ComplexEndpoints.fullFrame (arity^(childExponent+1))
            (fun tensorAddress => decoded shape rowCount polynomialExponent inputPrecision initialLive originalCoefficients
              (pack rawRow (FlatCoordinateLayout.index
                (CompactComplexNonleafChildAddress.insert phaseCoordinate entryPath.visit globalAnchor tensorAddress) polynomialIndex)))
            (CompactComplexNonleafChildAddress.address phaseCoordinate entryPath.visit globalAnchor)) := by
  have tensorValues := CompactComplexSourceReadyReachedStoppedNodeTensorValues.tensor_of_schedule
    phaseCoordinate entryPath activeFits pair originalCoefficients inputWidth inputGrid baselineFitsPrecision parentSlots
    rolesDivideRows initialState entryData finalLive finalBoundary.state networkValues activePositive precisionReserve growthReserve childChunkRoom
  have targetCoverage := (CompactComplexSourceReadyReachedEventTrace.execution_terminal_coverage actualTrace).2
  let stage := parent phaseCoordinate entryPath.visit activeFits pair
  let metadataPrecision := ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision
  let sink := CompactComplexSinkSliceValues.scalarOutputRoles stage parentSlots metadataPrecision finalBoundary.state.reached.data
  have metadataFits : 2*shape.bits≤metadataPrecision := by
    dsimp only [metadataPrecision,ButterflyIndependentGuardHeaders.reservation]
    omega
  have storagePrecision : metadataPrecision-2*shape.bits=inputPrecision := by
    dsimp only [metadataPrecision,ButterflyIndependentGuardHeaders.reservation]
    omega
  have halfEqual : half shape inputPrecision=ButterflyGuard.halfWidth metadataPrecision shape.bits := by
    rw [←storagePrecision]
    exact CompactComplexSourceReadyReachedReturnInvariant.inherited_half_eq metadataFits
  have currentCapacity : finalLive≤half shape inputPrecision+1 := by
    rw [halfEqual]
    exact CompactComplexSourceReadyReachedCursorGuards.current_capacity entryPath finalBoundary.state
      baselineFits precisionReserve denominatorRoom
  have terminalWidth : ∀ scalarRole index,(finalBoundary.state.reached.data scalarRole index).1.length=half shape inputPrecision+1 ∧
      (finalBoundary.state.reached.data scalarRole index).2.length=half shape inputPrecision+1 := by
    intro scalarRole index
    rw [halfEqual]
    exact finalBoundary.state.reached.width scalarRole index
  have sinkWidth : ∀ scalarRole index,(sink scalarRole index).1.length=half shape inputPrecision+1 ∧
      (sink scalarRole index).2.length=half shape inputPrecision+1 := by
    intro scalarRole index
    exact CompactComplexSourceReadyCorrectedFinal.family_width stage parentSlots polynomialExponent metadataPrecision
      (half shape inputPrecision+1) (fun wire => finalBoundary.state.reached.data (wireIndex wire))
      (fun wire => terminalWidth (wireIndex wire)) (roleIndex scalarRole) index
  have inputRolesGrid : ∀ scalarRole,Grid shape (rowCount/roles) polynomialExponent inputPrecision initialLive
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*entryReturned))
      (CompactComplexCorrectedEntrySliceValues.inputRoles rowCount polynomialExponent rolesDivideRows originalCoefficients scalarRole) := by
    intro scalarRole index
    exact inputGrid _
  have sinkGrid := full_tensor_grid phaseCoordinate entryPath.visit inputPrecision initialLive finalLive
    (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*entryReturned))
    (CompactComplexCorrectedEntrySliceValues.inputRoles rowCount polynomialExponent rolesDivideRows originalCoefficients)
    sink inputRolesGrid tensorValues
  have normalization := contract_and_rejoin rowCount polynomialExponent inputPrecision finalLive
    (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1))
    ((CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*entryReturned))*
      4^(2*arity^(childExponent+2))) rolesDivideRows sink targetCoverage currentCapacity sinkWidth sinkGrid
  refine ⟨tensorValues,normalization.2.1,normalization.2.2,?_,?_⟩
  · intro scalarRole index
    rw [normalized_role]
    exact normalization.1 scalarRole index
  · intro rawRow polynomialIndex globalAnchor
    let rowWire := (physicalRowLayout rowCount rolesDivideRows).symm rawRow
    have rowAt : physicalRowLayout rowCount rolesDivideRows rowWire=rawRow :=
      (physicalRowLayout rowCount rolesDivideRows).apply_symm_apply rawRow
    have layoutAt : ∀ anchor,physicalLayout shape rowCount polynomialExponent rolesDivideRows
        ((rowWire.1,rowWire.2),(anchor,polynomialIndex))=
      pack rawRow (FlatCoordinateLayout.index anchor polynomialIndex) := by
      intro anchor
      change pack (physicalRowLayout rowCount rolesDivideRows rowWire)
        (FlatCoordinateLayout.index anchor polynomialIndex)=_
      rw [rowAt]
    have values := normalized_tensor_layout phaseCoordinate entryPath.visit rowCount polynomialExponent inputPrecision
      initialLive finalLive rolesDivideRows originalCoefficients sink normalization.1 tensorValues
      rowWire.1 rowWire.2 globalAnchor polynomialIndex
    simpa only [layoutAt] using values


theorem exists_node_normalized_values
    (packingLimit : ℕ) (basisProgram : Program ActivePrefixStageNative.tapes basisStateCount prime) (basisConstant : ℝ)
    (basisRuns : CompactComplexAlignedChildEntryPath.BasisRuns packingLimit basisStateCount basisProgram basisConstant)
    (headerStack liveStack : Fin stackCount)
    (originalCoefficients : CompactSpectatorVisitGeometry.Array shape rowCount polynomialExponent)
    (inputWidth : CompactSpectatorInheritedGrid.Width shape rowCount polynomialExponent inputPrecision originalCoefficients)
    (inputGrid : CompactSpectatorInheritedGrid.Grid shape rowCount polynomialExponent inputPrecision initialLive
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*entryReturned)) originalCoefficients)
    (baselineFitsPrecision : baselinePrecision  ≤  inputPrecision)
    (controlBank : Tapes 43 2) (queueBank : Tapes 1 2) (scalarHeaders : ActiveRepairRankHeadersCommands.State)
    (tailBank : Tapes 22 2) (originalStorage : Tapes (10+stackCount) 2) (auxiliaryBank : Tapes 2 2)
    (countBlank : originalStorage.head ⟨0,by omega⟩=0 ∧ originalStorage.tape ⟨0,by omega⟩=(fun _ => blank))
    (currentReady : originalStorage.head ⟨7,by omega⟩=1 ∧ originalStorage.tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits initialLive))
    (clockBlank : auxiliaryBank.head 1=0 ∧ auxiliaryBank.tape 1=(fun _ => blank))
    (auxiliaryFree : CompactComplexSourceReadyPrefixReadiness.BlankAfter auxiliaryBank 0)
    (exponentReady : controlBank.head 1=1 ∧ controlBank.tape 1=
      BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits (childExponent+2)))
    (control28Blank : controlBank.head 28=0 ∧ controlBank.tape 28=(fun _ => blank))
    (control29Blank : controlBank.head 29=0 ∧ controlBank.tape 29=(fun _ => blank))
    (initialLedger : initialLive ≤ CompactComplexDenominatorCapacity.ledger CompactComplexDenominatorCapacity.scalarRows
      baselineLive dependencyLevels frameVolume entryReturned (CompactFramedScalarGrid.rows 0).length)
    (savedAssociated : CompactComplexSourceReadySavedCallHistory.Associated origin savedCalls
      (originalStorage.tape (Fin.natAdd 10 pcStack)) (originalStorage.head (Fin.natAdd 10 pcStack)))
    (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack) (headerLiveDistinct : headerStack≠liveStack)
    (originalProtectedTails : ∀ storagePort,CompactComplexSourceReadyReachedDormantFrameInvariant.protectedSlots
      headerStack liveStack pcStack storagePort → ∀ cell,originalStorage.head storagePort ≤ cell →
      originalStorage.tape storagePort cell=blank)
    (activePositive : 0 < shape.active)
    (childStopped : Networks.ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=true)
    (axesFit : 0+arity^(childExponent+1) ≤ shape.bits)
    (childChunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+Nat.clog 2 (growthConstant+1)+
      CompactComplexScalarIntegerRows.guardBits ≤ shape.chunk)
    (scalarChunkRoom : ∀ group : GroupIndex,CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+
      Nat.clog 2 (growthConstant+1)+(gates group).length*guardBits ≤ shape.chunk)
    (guardPositive : 1 ≤ shape.guard) (guardFitsChunk : shape.guard+1 ≤ shape.chunk)
    (rowsPositive : 0 < rowCount) (childRowsPositive : 0 < rowCount/roles) (rolesDivideRows : roles∣rowCount)
    (unitPayload : shape.payload=1)
    (parentSlots : (parent phaseCoordinate entryPath.visit activeFits pair).slots=25^3)
    (parentPacked : ∀ operation,1 < (parent phaseCoordinate entryPath.visit activeFits pair).f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair
        (CompactComplexSourceReadyReachedBasisInvariant.input (parent phaseCoordinate entryPath.visit activeFits pair)
          (rowCount/roles) polynomialExponent (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) guardPositive guardFitsChunk childRowsPositive) operation) packingLimit)
    (precisionReserve : baselinePrecision+2*shape.bits ≤ (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)) (baselineFits : baselineLive ≤ baselinePrecision)
    (growthReserve : CompactFramedScalarGrid.growthConstant ≤ growthConstant)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows ≤ shape.chunk)
    (axesPositive : 0 < shape.axes) (chunkPositive : 0 < shape.chunk) :
    ∃ initialState : State (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent)
      (metadataPrecision:=ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=savedCalls) 0 initialLive,
      initialState.bank=CompactComplexSourceReadyReachedEventInvariant.canonical
        (CompactComplexCorrectedEntryGeometryReadiness.permanent (parent phaseCoordinate entryPath.visit activeFits pair)
          parentSlots rowCount polynomialExponent (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
          initialLive (childExponent+1) rolesDivideRows originalCoefficients controlBank queueBank scalarHeaders tailBank originalStorage)
        auxiliaryBank ∧
      initialState.reached.data=(fun arrayIndex => CompactComplexCorrectedEntryGeometryReadiness.array
        (parent phaseCoordinate entryPath.visit activeFits pair) parentSlots rowCount polynomialExponent
        (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) rolesDivideRows originalCoefficients
        (CompactComplexScalarRolePorts.roleIndex arrayIndex)) ∧
    ∃ finalLive,∃ finalBoundary : FrameState (stage:=parent phaseCoordinate entryPath.visit activeFits pair) (rowCount:=rowCount)
      (polynomialExponent:=polynomialExponent) (metadataPrecision:=(ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision))
      (baselinePrecision:=baselinePrecision) (growthConstant:=growthConstant) (completedAxes:=0)
      (baselineLive:=baselineLive) (dependencyLevels:=dependencyLevels) (frameVolume:=frameVolume)
      (entryReturned:=entryReturned) (childExponent:=childExponent+1) (pcStack:=pcStack)
      (origin:=origin) (savedCalls:=savedCalls) (capture initialState headerStack liveStack)
      initialState.reached.targetValue schedule.length finalLive,
      ∃ elapsedSteps,Execution basisProgram headerStack liveStack initialLive initialState finalBoundary.state elapsedSteps ∧
        elapsedSteps ≤ totalBudget phaseCoordinate entryPath activeFits pair packingLimit guardPositive guardFitsChunk
          childRowsPositive parentSlots parentPacked ∧
        CompactComplexDenominatorPolicy.minimumCompletedExponent initialLive (childExponent+1) ≤ finalLive ∧
        CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1) ≤ finalLive ∧
        (∀ (row : Fin (rowCount/roles)) (polynomialIndex : Fin (2^polynomialExponent))
          (globalAnchor : Networks.BinaryWalsh.Address shape.bits),
          stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent ((ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)-2*shape.bits)
            finalLive finalBoundary.state.reached.data row polynomialIndex globalAnchor=
          Networks.FramedCircuit.run (Networks.ComplexFramedExecution.network (arity^(childExponent+1)))
            (stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent ((ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)-2*shape.bits)
              initialLive initialState.reached.data row polynomialIndex globalAnchor)) ∧
        (∀ (row : Fin (rowCount/roles)) (polynomialIndex : Fin (2^polynomialExponent))
          (globalAnchor : Networks.BinaryWalsh.Address shape.bits),
          stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent inputPrecision finalLive
            (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair)
              parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
              finalBoundary.state.reached.data) row polynomialIndex globalAnchor=
            fun wire => Networks.ComplexEndpoints.fullFrame (arity^(childExponent+1))
              (stored phaseCoordinate entryPath.visit (rowCount/roles) polynomialExponent inputPrecision initialLive
                (CompactComplexCorrectedEntrySliceValues.inputRoles rowCount polynomialExponent rolesDivideRows originalCoefficients)
                row polynomialIndex globalAnchor wire)) ∧
        (∀ index,((normalized rowCount polynomialExponent finalLive (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivideRows (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair) parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) finalBoundary.state.reached.data)) index).1.length=half shape inputPrecision+1 ∧
          ((normalized rowCount polynomialExponent finalLive (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivideRows (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair) parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) finalBoundary.state.reached.data)) index).2.length=half shape inputPrecision+1) ∧
        Grid shape rowCount polynomialExponent inputPrecision (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) ((CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*entryReturned))*4^(2*arity^(childExponent+2))) (normalized rowCount polynomialExponent finalLive (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivideRows (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair) parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) finalBoundary.state.reached.data)) ∧
        (∀ scalarRole index,decoded shape (rowCount/roles) polynomialExponent inputPrecision (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1))
          (CompactNativeRoleReservedBridge.role shape rowCount roles polynomialExponent rolesDivideRows (normalized rowCount polynomialExponent finalLive (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivideRows (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair) parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) finalBoundary.state.reached.data))
            (roleIndex scalarRole)) index=
          decoded shape (rowCount/roles) polynomialExponent inputPrecision finalLive
            ((CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair) parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision) finalBoundary.state.reached.data) scalarRole) index) ∧
        (∀ (rawRow : Fin rowCount) (polynomialIndex : Fin (2^polynomialExponent))
          (globalAnchor : BinaryWalsh.Address shape.bits),
          decoded shape rowCount polynomialExponent inputPrecision
            (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1))
            (normalized rowCount polynomialExponent finalLive
              (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) rolesDivideRows
              (CompactComplexSinkSliceValues.scalarOutputRoles (parent phaseCoordinate entryPath.visit activeFits pair)
                parentSlots (ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
                finalBoundary.state.reached.data))
            (pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex))=
          ComplexEndpoints.fullFrame (arity^(childExponent+1))
            (fun tensorAddress => decoded shape rowCount polynomialExponent inputPrecision initialLive originalCoefficients
              (pack rawRow (FlatCoordinateLayout.index
                (CompactComplexNonleafChildAddress.insert phaseCoordinate entryPath.visit globalAnchor tensorAddress) polynomialIndex)))
            (CompactComplexNonleafChildAddress.address phaseCoordinate entryPath.visit globalAnchor)) := by
  obtain ⟨initialState,entryBank,entryData,finalLive,finalBoundary,elapsedSteps,actualTrace,timeBound,
      minimumCoverage,targetCoverage,networkValues⟩ :=
    CompactComplexSourceReadyReachedStoppedNodeSchedule.exists_node_schedule phaseCoordinate entryPath activeFits pair
      packingLimit basisProgram basisConstant basisRuns headerStack liveStack originalCoefficients inputWidth inputGrid
      baselineFitsPrecision controlBank queueBank scalarHeaders tailBank originalStorage auxiliaryBank countBlank currentReady
      clockBlank auxiliaryFree exponentReady control28Blank control29Blank initialLedger savedAssociated pcHeaderDistinct
      pcLiveDistinct headerLiveDistinct originalProtectedTails activePositive childStopped axesFit childChunkRoom scalarChunkRoom
      guardPositive guardFitsChunk rowsPositive childRowsPositive rolesDivideRows unitPayload parentSlots parentPacked precisionReserve
      baselineFits growthReserve denominatorRoom axesPositive chunkPositive
  obtain ⟨tensorValues,normalizedWidth,normalizedGrid,contractionExact,normalizedTensor⟩ :=
    normalize_of_schedule phaseCoordinate entryPath activeFits pair basisProgram headerStack liveStack
      originalCoefficients inputWidth inputGrid baselineFitsPrecision parentSlots rolesDivideRows initialState entryData
      finalLive finalBoundary elapsedSteps actualTrace networkValues activePositive precisionReserve growthReserve childChunkRoom
      baselineFits denominatorRoom
  exact ⟨initialState,entryBank,entryData,finalLive,finalBoundary,elapsedSteps,actualTrace,timeBound,
    minimumCoverage,targetCoverage,networkValues,tensorValues,normalizedWidth,normalizedGrid,contractionExact,normalizedTensor⟩

end Node
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedStoppedNodeNormalizedValues
