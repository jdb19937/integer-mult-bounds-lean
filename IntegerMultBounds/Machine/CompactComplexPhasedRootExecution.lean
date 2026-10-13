module

public import IntegerMultBounds.Machine.CompactComplexInputPhasedRootExecution
public import IntegerMultBounds.Machine.NativeHadamardPhaseCompletedGrid

/-! Both physical Hadamard phase corrections execute around the complete actual
root trace on one fixed program. The final word has exact normalized Hadamard
readout with an explicit dyadic Gaussian factor; executing that normalization
and the public paper-format wrapper remain separate obligations. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexPhasedRootExecution
noncomputable section
open Networks
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexChildHeadersData (parent)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactComplexSourceReadyReachedDormantFrameInvariant (protectedSlots)
open CompactComplexSourceReadyCompletedNonleafChildOfStoppedChildren.RecursiveInduction (PackingFamily)
open CompactComplexScalarIntegerRows (GroupIndex gates guardBits)
open CompactComplexAlignedReachedNodeEntryPath (originalBank entryCost)
open CompactComplexAlignedReachedFinalReturn (rootEndpoint rootFinalCost)
open CompactComplexAlignedBoundaryPaths (alignedBank)
open CompactComplexSourceReadyCompletedChildBoundary (joined)
open CompactSpectatorInheritedGrid (half decoded Grid Width)
open CompactSpectatorVisitGeometry (Array)
open CompactGlobalRowPadding (rowsAt)
open CompactRecursiveDependencyBudget (Path)
open RecursiveInterchangeRows (pack)
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites
  ComplexRecursiveCallSchema.calls CompactComplexCompletedLiveLower.schedule CompactComplexRolePhaseSite.roleCount
  CompactComplexSourceReadyReachedRecursiveSchedule.totalBudget
  CompactComplexSourceReadyGuard.guardConstant
  CompactComplexSourceReadyNonleafTargetSplit.constant
  NativeEndpointCharacterCanonicalRoles.constant NativeUniformPolynomialRotationRoles.constant
  CompactComplexEndpointRoleExchange.constant CompactComplexSourceReadyNonleafFinalPath.constant

variable {stackCount : ℕ} {shape : Shape}
attribute [local irreducible] NativeHadamardPhaseRootBank.program CompactComplexPublicRootExecution.program
  CompactComplexInputPhasedRootExecution.program


/-- The same fixed output phase runs after the input-phase/root program. -/
def program (packingLimit : ℕ) (headerStack pcStack liveStack : Fin stackCount) :=
  (⟨_,seq (CompactComplexInputPhasedRootExecution.program packingLimit headerStack pcStack liveStack).2
    (NativeHadamardPhaseRootBank.program (stackCount:=stackCount)).2⟩ :
      Σ stateCount,Program (CompactComplexActualCallFullAlignment.tapes stackCount roles) stateCount prime)

def constant (packingLimit : ℕ) : ℝ :=
  CompactComplexInputPhasedRootExecution.constant packingLimit+(NativeHadamardPhaseOriginal.constant : ℝ)+1

theorem constant_positive (packingLimit : ℕ) : 0<constant packingLimit := by
  have rootPositive := CompactComplexInputPhasedRootExecution.constant_positive packingLimit
  have phaseNonnegative : (0 : ℝ)≤NativeHadamardPhaseOriginal.constant := Nat.cast_nonneg _
  unfold constant
  linarith

/-- The original input physically executes both phase corrections and the full
recursive root to the same final word, with derived post-root readiness and
signed guards. All transitions and both joins have a fixed uniform coefficient.
The normalization factor is explicit; no normalized-output or execution premise
is supplied, and this does not claim a physical public-format rounded layer. -/
theorem root_runs
    (phaseCoordinate : Fin shape.chunk) (activeFits : shape.active≤shape.axes)
    (pair : BinaryRowProgram.Op (Fin arity))
    (polynomialExponent inputPrecision baselinePrecision growthConstant baselineLive packingLimit : ℕ)
    (guardPositive : 1≤shape.guard) (guardFitsChunk : shape.guard+1≤shape.chunk)
    (headerStack pcStack liveStack : Fin stackCount)
    (largeAxes : arity^1000<shape.axes) (activePositive : 0<shape.active)
    (axesPositive : 0<shape.axes) (chunkPositive : 0<shape.chunk) (unitPayload : shape.payload=1)
    (packingFamily : PackingFamily phaseCoordinate activeFits pair polynomialExponent inputPrecision packingLimit
      guardPositive guardFitsChunk)
    (childChunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+
      Nat.clog 2 (growthConstant+1)+guardBits≤shape.chunk)
    (scalarChunkRoom : ∀ group : GroupIndex,CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant+
      Nat.clog 2 (growthConstant+1)+(gates group).length*guardBits≤shape.chunk)
    (precisionReserve : baselinePrecision+2*shape.bits≤ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision)
    (baselineFits : baselineLive≤baselinePrecision) (baselineFitsPrecision : baselinePrecision ≤ inputPrecision)
    (growthReserve : CompactFramedScalarGrid.growthConstant≤growthConstant)
    (denominatorRoom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤shape.chunk)
    (childExponent : ℕ)
    {nodeLeft dependencyLevels frameVolume entryReturned rowCount : ℕ}
    (entryPath : Path shape.active nodeLeft (childExponent+2) dependencyLevels frameVolume entryReturned)
    (rowsPadded : rowCount=rowsAt roles arity shape.axes shape.chunk dependencyLevels)
    (nodeNonstopped : ComplexRecursiveCallSchema.stopped shape.axes (childExponent+2)=false)
    (initialLive : ℕ) (originalCoefficients : Array shape rowCount polynomialExponent)
    (inputWidth : Width shape rowCount polynomialExponent inputPrecision originalCoefficients)
    (inputGrid : Grid shape rowCount polynomialExponent inputPrecision initialLive
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*entryReturned))
      originalCoefficients)
    (controlBank : Tapes 43 2) (queueBank : Tapes 1 2) (scalarHeaders : ActiveRepairRankHeadersCommands.State)
    (tailBank : Tapes 22 2) (originalStorage : Tapes (10+stackCount) 2) (auxiliaryBank : Tapes 2 2)
    (countBlank : originalStorage.head ⟨0,by omega⟩=0 ∧ originalStorage.tape ⟨0,by omega⟩=(fun _ => blank))
    (currentReady : originalStorage.head ⟨7,by omega⟩=1 ∧ originalStorage.tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits initialLive))
    (targetBlank : originalStorage.head ⟨8,by omega⟩=0 ∧ originalStorage.tape ⟨8,by omega⟩=(fun _ => blank))
    (clockBlank : auxiliaryBank.head 1=0 ∧ auxiliaryBank.tape 1=(fun _ => blank))
    (auxiliaryFree : CompactComplexSourceReadyPrefixReadiness.BlankAfter auxiliaryBank 0)
    (exponentReady : controlBank.head 1=1 ∧ controlBank.tape 1=
      BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits (childExponent+2)))
    (control28Blank : controlBank.head 28=0 ∧ controlBank.tape 28=(fun _ => blank))
    (control29Blank : controlBank.head 29=0 ∧ controlBank.tape 29=(fun _ => blank))
    (initialLedger : initialLive≤CompactComplexDenominatorCapacity.ledger CompactComplexDenominatorCapacity.scalarRows
      baselineLive dependencyLevels frameVolume entryReturned (CompactFramedScalarGrid.rows 0).length)
    (stackOrigin : ℤ)
    (savedAssociated : CompactComplexSourceReadySavedCallHistory.Associated stackOrigin []
      (originalStorage.tape (Fin.natAdd 10 pcStack)) (originalStorage.head (Fin.natAdd 10 pcStack)))
    (pcHeaderDistinct : pcStack≠headerStack) (pcLiveDistinct : pcStack≠liveStack) (headerLiveDistinct : headerStack≠liveStack)
    (originalProtectedTails : ∀ storagePort,protectedSlots headerStack liveStack pcStack storagePort →
      ∀ cell,originalStorage.head storagePort≤cell → originalStorage.tape storagePort cell=blank) :
    let metadataPrecision := ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision
    let stage := parent phaseCoordinate entryPath.visit activeFits pair
    ∃ elapsedSteps : ℕ,∃ outputBank : Tapes (CompactComplexSourceReadyWorkspace.tapes stackCount roles) 2,
    ∃ outputArray : Array shape rowCount polynomialExponent,
      CompactComplexRootWorkspaceClean.Clean outputBank ∧
      NativeHadamardPhaseRootHeaders.Ready stage rowCount polynomialExponent metadataPrecision outputBank ∧
      (elapsedSteps : ℝ)≤constant packingLimit*
        (CompactNativeRoleTransferBudget.volume rowCount shape polynomialExponent metadataPrecision : ℝ)*
        CompactComplexUniformRuntimeCoefficient.stageFactor shape (childExponent+1) ∧
      HoareTime (program packingLimit headerStack pcStack liveStack).2
        (fun bank => bank=originalBank stage rowCount polynomialExponent metadataPrecision originalCoefficients
          controlBank queueBank scalarHeaders tailBank originalStorage auxiliaryBank)
        (fun bank => bank=alignedBank (outputBank.append (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)))
        elapsedSteps ∧
      outputBank.tape CompactComplexSourceReadyOrientation.source=CompactSpectatorLeafAxis.word outputArray ∧
      outputBank.head CompactComplexSourceReadyOrientation.source=0 ∧
      (∀ index,(outputArray index).1.length=half shape inputPrecision+1 ∧ (outputArray index).2.length=half shape inputPrecision+1) ∧
      Grid shape rowCount polynomialExponent inputPrecision
        (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1))
        (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*entryReturned)*
          4^(2*arity^(childExponent+2))) outputArray ∧
      ∀ (rawRow : Fin rowCount) (polynomialIndex : Fin (2^polynomialExponent)) (globalAnchor : BinaryWalsh.Address shape.bits),
        Networks.GaussianHadamardBridge.normalization^(arity^(childExponent+2)) *
          decoded shape rowCount polynomialExponent inputPrecision
            (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) outputArray
            (pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex)) =
        BinaryColumns.tensorColumns (arity^(childExponent+1))
          (Networks.GaussianHadamardBridge.hadamardProduct (Networks.GaussianHadamardBridge.allCoordinates arity))
          (fun tensorAddress => decoded shape rowCount polynomialExponent inputPrecision initialLive originalCoefficients
            (pack rawRow (FlatCoordinateLayout.index
              (CompactComplexNonleafChildAddress.insert phaseCoordinate entryPath.visit globalAnchor tensorAddress) polynomialIndex)))
          (CompactComplexNonleafChildAddress.address phaseCoordinate entryPath.visit globalAnchor) := by
  let metadataPrecision := ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision
  let stage := parent phaseCoordinate entryPath.visit activeFits pair
  let completedDenominator := CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)
  obtain ⟨rootElapsed,beforeBank,beforeArray,beforeClean,beforeHeaders,rootRuntime,rootRun,beforeWord,beforeHead,
      beforeWidth,beforeGrid,beforeTensor⟩ :=
    CompactComplexInputPhasedRootExecution.root_runs phaseCoordinate activeFits pair polynomialExponent
      inputPrecision baselinePrecision growthConstant baselineLive packingLimit guardPositive guardFitsChunk
      headerStack pcStack liveStack largeAxes activePositive axesPositive chunkPositive unitPayload packingFamily
      childChunkRoom scalarChunkRoom precisionReserve baselineFits baselineFitsPrecision growthReserve denominatorRoom
      childExponent entryPath rowsPadded nodeNonstopped initialLive originalCoefficients inputWidth inputGrid
      controlBank queueBank scalarHeaders tailBank originalStorage auxiliaryBank countBlank currentReady targetBlank
      clockBlank auxiliaryFree exponentReady control28Blank control29Blank initialLedger stackOrigin savedAssociated
      pcHeaderDistinct pcLiveDistinct headerLiveDistinct originalProtectedTails
  have rowGuards := CompactComplexRecursivePathRows.recursive_row_guards entryPath activeFits roles shape.chunk
    (by unfold roles CompactComplexRolePhaseSite.roleCount; positivity) chunkPositive (by omega)
  have rowsPositive : 0<rowCount := by rw [rowsPadded]; exact rowGuards.2.1
  have beforeStorageWidth : Width shape rowCount polynomialExponent inputPrecision beforeArray := by
    intro index
    simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using beforeWidth index
  have beforeNativeWidth : ∀ index,(beforeArray index).1.length=NativePolynomialStageShape.width shape metadataPrecision ∧
      (beforeArray index).2.length=NativePolynomialStageShape.width shape metadataPrecision := by
    intro index
    simpa only [NativePolynomialStageShape.width,metadataPrecision,ButterflyGuard.width,
      ButterflyIndependentGuardSemantics.half_eq] using beforeWidth index
  have outputRun := NativeHadamardPhaseOutputBank.runs stage metadataPrecision rfl rowsPositive (by omega)
    axesPositive guardFitsChunk unitPayload beforeArray beforeNativeWidth beforeBank beforeClean beforeHeaders beforeWord beforeHead
  let finalArray := NativeHadamardPhaseOriginal.result stage metadataPrecision beforeArray
  let finalBank := NativeHadamardPhaseOutputBank.output stage metadataPrecision beforeArray beforeBank
  have finalClean := NativeHadamardPhaseOutputBank.output_clean stage metadataPrecision beforeArray beforeBank beforeClean
  have finalHeaders := NativeHadamardPhaseOutputBank.output_headers stage metadataPrecision beforeArray beforeBank beforeHeaders
  have dependencyRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant≤shape.chunk := by omega
  have pendingFits : 2*arity^(childExponent+2)≤shape.bits :=
    NativeHadamardPhaseCompletedGrid.double_visit_le_bits entryPath.visit (by omega)
  have finalGrid := NativeHadamardPhaseCompletedGrid.grid_from_growth stage inputPrecision baselinePrecision growthConstant
    completedDenominator (2*arity^(childExponent+2)) entryPath baselineFitsPrecision dependencyRoom pendingFits
    beforeArray beforeStorageWidth beforeGrid
  have finalWidth := NativeHadamardPhaseOriginal.result_width stage metadataPrecision (half shape inputPrecision+1)
    beforeArray beforeWidth
  let phaseBudget := NativeHadamardPhaseOriginal.constant*
    CompactNativeRoleTransferBudget.volume rowCount shape polynomialExponent metadataPrecision
  refine ⟨rootElapsed+phaseBudget+1,finalBank,finalArray,finalClean,finalHeaders,?_,?_,?_,?_,finalWidth,finalGrid,?_⟩
  · have factorBound := CompactComplexInputPhasedRootExecution.stage_factor_one_le (shape:=shape) axesPositive (childExponent+1)
    have volumePositive : 0<CompactNativeRoleTransferBudget.volume rowCount shape polynomialExponent metadataPrecision := by
      unfold CompactNativeRoleTransferBudget.volume
      exact Nat.mul_pos rowsPositive (CompactNativeRoleTransferBudget.symbols_pos shape polynomialExponent metadataPrecision)
    have volumeBound : (1 : ℝ)≤CompactNativeRoleTransferBudget.volume rowCount shape polynomialExponent metadataPrecision :=
      by exact_mod_cast volumePositive
    have joinBound := one_le_mul_of_one_le_of_one_le volumeBound factorBound
    have phaseBound := mul_le_mul_of_nonneg_left factorBound
      (mul_nonneg (Nat.cast_nonneg NativeHadamardPhaseOriginal.constant)
        (Nat.cast_nonneg (CompactNativeRoleTransferBudget.volume rowCount shape polynomialExponent metadataPrecision)))
    simp only [mul_one] at phaseBound
    dsimp only [phaseBudget]
    push_cast
    unfold constant
    dsimp only [metadataPrecision] at rootRuntime joinBound phaseBound ⊢
    nlinarith only [rootRuntime,joinBound,phaseBound]
  · exact (rootRun.seq outputRun).consequence (fun bank equality => equality) (fun bank equality => equality)
      (by dsimp only [phaseBudget]; omega)
  · dsimp only [finalBank,NativeHadamardPhaseOutputBank.output,SharedPlacementAlphabet.setTape]
    rw [Function.update_self]
    rfl
  · dsimp only [finalBank,NativeHadamardPhaseOutputBank.output,SharedPlacementAlphabet.setTape]
    rw [Function.update_self]
  · intro rawRow polynomialIndex globalAnchor
    have finalReadout := NativeHadamardPhaseCompletedGrid.decoded_at_node_from_growth phaseCoordinate entryPath activeFits pair
      inputPrecision baselinePrecision growthConstant completedDenominator (2*arity^(childExponent+2)) baselineFitsPrecision
      dependencyRoom pendingFits beforeArray beforeStorageWidth beforeGrid rawRow polynomialIndex globalAnchor
    have countEquation : arity*arity^(childExponent+1)=arity^(childExponent+2) := by
      change arity*arity^(childExponent+1)=arity^((childExponent+1)+1)
      exact (pow_succ' _ _).symm
    let originalSlice := fun tensorAddress => decoded shape rowCount polynomialExponent inputPrecision initialLive originalCoefficients
      (pack rawRow (FlatCoordinateLayout.index
        (CompactComplexNonleafChildAddress.insert phaseCoordinate entryPath.visit globalAnchor tensorAddress) polynomialIndex))
    let tensorAddress := CompactComplexNonleafChildAddress.address phaseCoordinate entryPath.visit globalAnchor
    have converted := congrArg
      (fun operation : BinaryColumns.Operator arity (arity^(childExponent+1)) => operation originalSlice tensorAddress)
      (Networks.GaussianHadamardBridge.fullFrame_bridge (addressBits:=arity) (arity^(childExponent+1)))
    change BinaryColumns.tensorColumns (arity^(childExponent+1))
        (Networks.GaussianHadamardBridge.hadamardProduct (Networks.GaussianHadamardBridge.allCoordinates arity))
        originalSlice tensorAddress =
      Networks.GaussianHadamardBridge.normalization^(arity*arity^(childExponent+1)) *
        Networks.GaussianHadamardPhase.tensorPhase (arity^(childExponent+1))
          (ComplexEndpoints.fullFrame (arity^(childExponent+1))
            (Networks.GaussianHadamardPhase.tensorPhase (arity^(childExponent+1)) originalSlice)) tensorAddress at converted
    rw [countEquation,Networks.GaussianHadamardPhase.tensorPhase_apply] at converted
    have finalTensor : decoded shape rowCount polynomialExponent inputPrecision completedDenominator finalArray
        (pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex)) =
        (∏ column : Fin (arity^(childExponent+1)), BinaryPhase.phase (BinaryPhase.weightPhase (tensorAddress column))) *
          ComplexEndpoints.fullFrame (arity^(childExponent+1))
            (Networks.GaussianHadamardPhase.tensorPhase (arity^(childExponent+1)) originalSlice) tensorAddress := by
      calc
        _=(∏ column : Fin (arity^(childExponent+1)), BinaryPhase.phase (BinaryPhase.weightPhase (tensorAddress column))) *
            decoded shape rowCount polynomialExponent inputPrecision completedDenominator beforeArray
              (pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex)) := finalReadout
        _=_ := congrArg (fun value => (∏ column : Fin (arity^(childExponent+1)),
          BinaryPhase.phase (BinaryPhase.weightPhase (tensorAddress column))) * value) (beforeTensor rawRow polynomialIndex globalAnchor)
    rw [finalTensor]
    exact converted.symm

end
end IntegerMultBounds.Machine.CompactComplexPhasedRootExecution
