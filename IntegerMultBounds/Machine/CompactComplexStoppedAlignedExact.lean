module

public import IntegerMultBounds.Machine.CompactComplexStoppedAlignedBudget
public import IntegerMultBounds.Machine.CompactComplexDirectionalStoppedLeafTensor

/-! The original permanent-bank stopped roundtrip has exact selected tensor
values in addition to its paid physical run, spectator values, grids and ledger.
The literal forward or inverse output bank is retained unchanged. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexStoppedAlignedBudget
noncomputable section
open CompactComplexRecursiveGeometry (arity Visit)
open CompactRecursiveDependencyBudget (Path)
open CompactSpectatorInheritedGrid (Grid decoded)
open ActiveRepairRankHeadersCommands (State)
open CompactComplexNativeCodecFrame (bank)
open CompactComplexStoppedAlignedCall
open CompactComplexRolePhaseSite (roleCount role)
open Networks.ComplexRecursiveCallSchema (Call)
open RecursiveChildQuotientsConstant (bits)
variable {s : ℕ}
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites

/-- Exact corrected stopped tensor values on the same permanent bank and the
same native-volume times stopped-axis-count bound as the actual roundtrip. -/
theorem actual_runs_tensor (interchangeBase globalAxes reservedAxes guardWidth chunkWidth polynomialExponent basePrecision rowLevel : ℕ) (interchangeBaseFits : 2 ≤ interchangeBase)
    (reservedAxesFit : reservedAxes ≤ globalAxes) (axesPositive : 0 < globalAxes) (guardPositive : 0 < guardWidth) (chunkPositive : 0 < chunkWidth) (reservationPositive : 0 < reservedAxes)
    (reservationFits : CompactGlobalReservation.reservedAxes roleCount interchangeBase globalAxes guardWidth chunkWidth ≤ reservedAxes)
    (rowLevelFits : rowLevel < CompactGlobalRowPadding.depth interchangeBase globalAxes)
    (rowCoordinate : Fin (CompactReservationNativeRows.shape roleCount interchangeBase globalAxes reservedAxes guardWidth chunkWidth).chunk)
    {leftBoundary childExponent dependencyLevels frameVolume returnedVolume : ℕ}
    (path : Path (CompactReservationNativeRows.shape roleCount interchangeBase globalAxes reservedAxes guardWidth chunkWidth).active
      leftBoundary (childExponent+2) dependencyLevels frameVolume returnedVolume)
    (childStopped : Networks.ComplexRecursiveCallSchema.stopped globalAxes (childExponent+1) = true)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (call : Call)
    (headerStack pcStack : Fin s) (stackPortsDistinct : pcStack ≠ headerStack)
    (controlState : State) (controlExponent : controlState 1 = some (childExponent+2)) (queue : Tapes 1 2) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (parentLive : ℕ)
    (liveWord : storage.tape ⟨7,by omega⟩ = RadixZeroFill.encodedBinary (bits parentLive) ∧ storage.head ⟨7,by omega⟩ = 1)
    (targetBlank : storage.tape ⟨8,by omega⟩ = (fun _ => blank) ∧ storage.head ⟨8,by omega⟩ = 0)
    (temporaryBlank : storage.tape ⟨0,by omega⟩ = (fun _ => blank) ∧ storage.head ⟨0,by omega⟩ = 0)
    (headerTailBlank : ∀ z,storage.head (Fin.natAdd 10 headerStack) ≤ z → storage.tape (Fin.natAdd 10 headerStack) z = blank)
    (pcTailBlank : ∀ j < CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length arity,
      storage.tape (Fin.natAdd 10 pcStack) (storage.head (Fin.natAdd 10 pcStack)+j) = blank)
    (liveTailBlank : ∀ z,storage.head ⟨9,by omega⟩ ≤ z →
      z < storage.head ⟨9,by omega⟩+1+(bits (CompactComplexDenominatorPolicy.leafTarget parentLive (childExponent+1))).length →
      storage.tape ⟨9,by omega⟩ z = blank)
    (inputData : CompactSpectatorVisitGeometry.Array (CompactReservationNativeRows.shape roleCount interchangeBase globalAxes reservedAxes guardWidth chunkWidth)
      (CompactGlobalRowPadding.rowsAt roleCount interchangeBase globalAxes chunkWidth rowLevel) polynomialExponent)
    (inputWidths : ∀ i,(inputData i).1.length = CompactNativeRoleHeaders.recordWidth
      (CompactReservationNativeRows.shape roleCount interchangeBase globalAxes reservedAxes guardWidth chunkWidth)
      (CompactNativeRoleReservedBridge.precision roleCount interchangeBase globalAxes reservedAxes chunkWidth basePrecision) ∧
      (inputData i).2.length = CompactNativeRoleHeaders.recordWidth
      (CompactReservationNativeRows.shape roleCount interchangeBase globalAxes reservedAxes guardWidth chunkWidth)
      (CompactNativeRoleReservedBridge.precision roleCount interchangeBase globalAxes reservedAxes chunkWidth basePrecision))
    (baselinePrecision growthConstant : ℕ) (growthPositive : 1 ≤ growthConstant) (baselineFitsPrecision : baselinePrecision ≤ basePrecision)
    (dependencyRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant ≤ chunkWidth)
    (inputGrid : Grid (CompactReservationNativeRows.shape CompactComplexRolePhaseSite.roleCount interchangeBase globalAxes reservedAxes guardWidth chunkWidth)
      (CompactGlobalRowPadding.rowsAt CompactComplexRolePhaseSite.roleCount interchangeBase globalAxes chunkWidth rowLevel) polynomialExponent
      (CompactNativeRoleReservedBridge.precision CompactComplexRolePhaseSite.roleCount interchangeBase globalAxes reservedAxes chunkWidth basePrecision-
        2*(CompactReservationNativeRows.shape CompactComplexRolePhaseSite.roleCount interchangeBase globalAxes reservedAxes guardWidth chunkWidth).bits) parentLive
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*returnedVolume)) inputData)
    (rowBound baselineLive usedRows : ℕ) (baselineLiveFits : baselineLive ≤ basePrecision) (usedRowsFit : usedRows ≤ rowBound)
    (denominatorRoom : CompactComplexDenominatorCapacity.room rowBound ≤ chunkWidth)
    (liveLedger : parentLive ≤ CompactComplexDenominatorCapacity.ledger rowBound baselineLive dependencyLevels frameVolume returnedVolume usedRows) :
    let shape := CompactReservationNativeRows.shape roleCount interchangeBase globalAxes reservedAxes guardWidth chunkWidth
    let rowCount := CompactGlobalRowPadding.rowsAt roleCount interchangeBase globalAxes chunkWidth rowLevel
    let metadataPrecision := CompactNativeRoleReservedBridge.precision roleCount interchangeBase globalAxes reservedAxes chunkWidth basePrecision
    let ha := CompactNativeRoleStoppedChildBudget.actual_active roleCount interchangeBase globalAxes reservedAxes guardWidth chunkWidth reservedAxesFit
    let scalar := CompactReservedHeaders.initial reservedAxes chunkWidth rowCoordinate.val polynomialExponent basePrecision globalAxes guardWidth
    let parent := CompactComplexChildHeadersData.parent rowCoordinate path.visit ha pair
    let targetN := CompactComplexDenominatorPolicy.leafTarget parentLive (childExponent+1)
    ∃ (hdiv : roleCount ∣ rowCount) (time : ℕ),
      let before := fun j => CompactNativeRoleReservedBridge.role shape rowCount roleCount polynomialExponent hdiv inputData j
      let after := CompactComplexChildGridPromoted.aligned shape (rowCount/roleCount) polynomialExponent (metadataPrecision-2*shape.bits)
        rowCoordinate (Visit.child path.visit call.slot) (CompactComplexStoppedCallSite.direction call) (role call.site) before
      HoareTime (program interchangeBase s headerStack pcStack call)
        (fun z => z = ready (bank (ActiveRepairRankHeadersCommands.bank controlState) queue scalar
          (ActivePrefixStageHeadersData.initial parent rowCount) tail storage
          (CompactNativeRoleReservedBridge.rolePayload shape rowCount roleCount polynomialExponent hdiv inputData)))
        (fun z => z = ready (bank (ActiveRepairRankHeadersCommands.bank controlState) queue scalar
          (ActivePrefixStageHeadersData.initial parent rowCount) tail (committed storage targetN)
          (CompactComplexStoppedGridHandoff.payload shape (rowCount/roleCount) polynomialExponent (fun _ => blank) 0 after))) time ∧
      time ≤ constant interchangeBase*CompactFallbackAxisRun.volume reservedAxes chunkWidth polynomialExponent basePrecision*(arity^(childExponent+1)) ∧
      (∀ j,Grid shape (rowCount/roleCount) polynomialExponent (metadataPrecision-2*shape.bits) targetN
        (CompactRecursiveGridBudget.bound baselinePrecision growthConstant (dependencyLevels+1)
          ((frameVolume+arity^(childExponent+2))+2*(returnedVolume+CompactRecursiveDependencyBudget.precedingCalls call*arity^(childExponent+1)+arity^(childExponent+1))))
        (after j)) ∧
      (∀ j,j ≠ role call.site → decoded shape (rowCount/roleCount) polynomialExponent (metadataPrecision-2*shape.bits) targetN (after j) = 
        decoded shape (rowCount/roleCount) polynomialExponent (metadataPrecision-2*shape.bits) parentLive (before j)) ∧
      (∀ (row : Fin (rowCount/roleCount)) (polynomialIndex : Fin (2^polynomialExponent))
        (globalAnchor : Networks.BinaryWalsh.Address shape.bits),
        CompactComplexStoppedLeafTensorSemantics.rowSlice (rowCount/roleCount) polynomialExponent (metadataPrecision-2*shape.bits) targetN
          rowCoordinate (Visit.child path.visit call.slot) row polynomialIndex globalAnchor (after (role call.site)) = 
        if call.inverse then (Networks.ComplexEndpoints.fullFrame (arity^childExponent)).symm
          (CompactComplexStoppedLeafTensorSemantics.rowSlice (rowCount/roleCount) polynomialExponent (metadataPrecision-2*shape.bits) parentLive
            rowCoordinate (Visit.child path.visit call.slot) row polynomialIndex globalAnchor (before (role call.site)))
        else Networks.ComplexEndpoints.fullFrame (arity^childExponent)
          (CompactComplexStoppedLeafTensorSemantics.rowSlice (rowCount/roleCount) polynomialExponent (metadataPrecision-2*shape.bits) parentLive
            rowCoordinate (Visit.child path.visit call.slot) row polynomialIndex globalAnchor (before (role call.site)))) ∧
      targetN ≤ CompactComplexDenominatorCapacity.ledger rowBound baselineLive dependencyLevels frameVolume (returnedVolume+arity^(childExponent+1)) usedRows := by
  dsimp only
  obtain ⟨rolesDivideRows,elapsedSteps,physicalRun,timeBound,returnedGrid,spectatorValues⟩ := 
    actual_runs_linear interchangeBase globalAxes reservedAxes guardWidth chunkWidth polynomialExponent basePrecision rowLevel interchangeBaseFits reservedAxesFit axesPositive guardPositive chunkPositive reservationPositive reservationFits rowLevelFits rowCoordinate path childStopped pair call
      headerStack pcStack stackPortsDistinct controlState controlExponent queue tail storage parentLive liveWord targetBlank temporaryBlank headerTailBlank pcTailBlank liveTailBlank inputData inputWidths baselinePrecision growthConstant growthPositive baselineFitsPrecision dependencyRoom inputGrid
      rowBound baselineLive usedRows baselineLiveFits usedRowsFit denominatorRoom liveLedger
  let shape := CompactReservationNativeRows.shape roleCount interchangeBase globalAxes reservedAxes guardWidth chunkWidth
  let rowCount := CompactGlobalRowPadding.rowsAt roleCount interchangeBase globalAxes chunkWidth rowLevel
  let metadataPrecision := CompactNativeRoleReservedBridge.precision roleCount interchangeBase globalAxes reservedAxes chunkWidth basePrecision
  have precisionFacts := CompactNativeRoleChildPrecision.actual_precision roleCount interchangeBase globalAxes reservedAxes guardWidth chunkWidth basePrecision chunkPositive reservationFits
  have baselineFits : baselinePrecision ≤ metadataPrecision-2*shape.bits := by
    dsimp only [metadataPrecision,shape]
    rw [precisionFacts.2]
    omega
  have childGrid : Grid shape rowCount polynomialExponent (metadataPrecision-2*shape.bits) parentLive
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant (dependencyLevels+1)
        ((frameVolume+arity^(childExponent+2))+2*(returnedVolume+CompactRecursiveDependencyBudget.precedingCalls call*arity^(childExponent+1)))) inputData := by
    intro arrayIndex
    exact Networks.GaussianPrecision.bound_mono
      (CompactComplexStoppedAlignedCall.child_budget path call baselinePrecision growthConstant growthPositive) (inputGrid arrayIndex)
  have roleWidths := CompactComplexStoppedAlignedCall.reserved_width shape rowCount polynomialExponent metadataPrecision
    rolesDivideRows precisionFacts.1 inputData inputWidths
  have roleGrids := CompactComplexStoppedGridHandoff.reserved_grid shape rowCount polynomialExponent (metadataPrecision-2*shape.bits) parentLive _
    rolesDivideRows inputData childGrid
  refine ⟨rolesDivideRows,elapsedSteps,physicalRun,timeBound,returnedGrid,spectatorValues,?_,?_⟩
  · intro row polynomialIndex globalAnchor
    have tensorValues := CompactComplexDirectionalStoppedLeafTensor.directional_result_from_path
      (CompactComplexStoppedCallSite.direction call) (rowCount/roleCount) polynomialExponent (metadataPrecision-2*shape.bits) parentLive baselinePrecision growthConstant
      rowCoordinate (Path.child path call) baselineFits dependencyRoom
      (CompactNativeRoleReservedBridge.role shape rowCount roleCount polynomialExponent rolesDivideRows inputData (role call.site))
      (roleWidths (role call.site)) (roleGrids (role call.site)) row polynomialIndex globalAnchor
    cases inverseEquation : call.inverse <;>
      simpa [CompactComplexChildGridPromoted.aligned,CompactComplexStoppedCallSite.direction,
        CompactComplexDenominatorPolicy.leafTarget,inverseEquation] using tensorValues.2
  · exact CompactComplexDenominatorCapacity.returned_advance rowBound baselineLive dependencyLevels frameVolume returnedVolume usedRows parentLive
      (CompactComplexDenominatorPolicy.leafTarget parentLive (childExponent+1)) (arity^(childExponent+1)) liveLedger (by
        unfold CompactComplexDenominatorPolicy.leafTarget
        omega)

end
end IntegerMultBounds.Machine.CompactComplexStoppedAlignedBudget
