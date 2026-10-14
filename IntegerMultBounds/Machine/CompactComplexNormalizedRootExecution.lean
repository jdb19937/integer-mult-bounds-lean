module

public import IntegerMultBounds.Machine.CompactComplexPhasedRootExecution
public import IntegerMultBounds.Machine.NativeHadamardNormalizationRootBank

/-! One fixed program executes both Hadamard phases, the entire actual recursive
root and complete physical normalization. The same final source and true live
word have exact normalized Hadamard semantics with no external factor. Original
readiness, genuine Paths and ledgers discharge all normalization prerequisites;
public paper-format parsing/rounding and stopped/scalar wrappers remain open. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexNormalizedRootExecution
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



attribute [local irreducible] CompactComplexPhasedRootExecution.program
  NativeHadamardNormalizationRootBank.program

def program (packingLimit : ℕ) (headerStack pcStack liveStack : Fin stackCount) :=
  (⟨_,seq (CompactComplexPhasedRootExecution.program packingLimit headerStack pcStack liveStack).2
    (NativeHadamardNormalizationRootBank.program (stackCount:=stackCount)).2⟩ :
      Σ stateCount,Program (CompactComplexActualCallFullAlignment.tapes stackCount roles) stateCount prime)

def constant (packingLimit : ℕ) : ℝ :=
  CompactComplexPhasedRootExecution.constant packingLimit+(NativeHadamardNormalizationOriginal.constant : ℝ)+1

theorem constant_positive (packingLimit : ℕ) : 0<constant packingLimit := by
  have rootPositive := CompactComplexPhasedRootExecution.constant_positive packingLimit
  have normalizationNonnegative : (0 : ℝ)≤NativeHadamardNormalizationOriginal.constant := Nat.cast_nonneg _
  unfold constant
  linarith

/-- The actual original aligned bank executes the complete nonstopped normalized
Hadamard trace. Exact final words, physical live denominator, grids, cleanup and
original headers are retained on that same output witness. One fixed positive
packing-limit-only coefficient pays every phase/root/normalization transition
and joining edge. No normalization factor, execution provider or output premise
is supplied; the public signed-format layer adapter remains separate. -/
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
      NativeHadamardNormalizationRootLive.Ready
        (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)+
          NativeHadamardNormalizationFactor.denominatorIncrease (arity^(childExponent+2))) outputBank ∧
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
        (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)+
          NativeHadamardNormalizationFactor.denominatorIncrease (arity^(childExponent+2)))
        (2*(CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*entryReturned)*
          4^(2*arity^(childExponent+2)))) outputArray ∧
      ∀ (rawRow : Fin rowCount) (polynomialIndex : Fin (2^polynomialExponent)) (globalAnchor : BinaryWalsh.Address shape.bits),
        decoded shape rowCount polynomialExponent inputPrecision
            (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)+
          NativeHadamardNormalizationFactor.denominatorIncrease (arity^(childExponent+2))) outputArray
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
  let normalizationIncrease := NativeHadamardNormalizationFactor.denominatorIncrease (arity^(childExponent+2))
  obtain ⟨rootElapsed,beforeBank,beforeArray,beforeClean,beforeHeaders,beforeLive,rootRuntime,rootRun,beforeWord,beforeHead,
      beforeWidth,beforeGrid,beforeTensor⟩ :=
    CompactComplexPhasedRootExecution.root_runs phaseCoordinate activeFits pair polynomialExponent
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
  have nativeWidth : ∀ index,(beforeArray index).1.length=NativePolynomialStageShape.width shape metadataPrecision ∧
      (beforeArray index).2.length=NativePolynomialStageShape.width shape metadataPrecision := by
    intro index
    simpa only [NativePolynomialStageShape.width,metadataPrecision,ButterflyGuard.width,
      ButterflyIndependentGuardSemantics.half_eq] using beforeWidth index
  have storedWidth : Width shape rowCount polynomialExponent inputPrecision beforeArray := by
    intro index
    simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using beforeWidth index
  have selectedWidth : stage.slots*stage.f=arity^(childExponent+2) := by
    change arity*arity^(childExponent+1)=arity^((childExponent+1)+1)
    exact (pow_succ' _ _).symm
  have selectedFits : stage.slots*stage.f≤shape.bits := by
    rw [selectedWidth]
    have visitFits := entryPath.visit.fits
    unfold Shape.bits
    nlinarith
  have liveFits := NativeHadamardNormalizationRootLive.network_live_volume entryPath baselineLive inputPrecision initialLive
    rowCount polynomialExponent (baselineFits.trans baselineFitsPrecision) denominatorRoom initialLedger rowsPositive
  have normalizationRun := NativeHadamardNormalizationRootBank.runs stage metadataPrecision completedDenominator
    rowsPositive (by omega) axesPositive chunkPositive unitPayload selectedFits liveFits beforeArray nativeWidth
    beforeBank beforeClean beforeHeaders beforeWord beforeHead beforeLive
  let finalArray := NativeHadamardNormalizationArray.result beforeArray
  let finalBank := NativeHadamardNormalizationRootBank.output stage completedDenominator beforeArray beforeBank
  have finalClean := NativeHadamardNormalizationRootBank.output_clean stage completedDenominator beforeArray beforeBank beforeClean
  have finalHeaders := NativeHadamardNormalizationRootBank.output_headers stage metadataPrecision completedDenominator beforeArray beforeBank beforeHeaders
  have increaseEquation : NativeHadamardNormalizationHeaders.increase stage=normalizationIncrease :=
    congrArg NativeHadamardNormalizationFactor.denominatorIncrease selectedWidth
  have finalLive := NativeHadamardNormalizationRootBank.output_live stage completedDenominator beforeArray beforeBank
  rw [increaseEquation] at finalLive
  have finalWidth := NativeHadamardNormalizationArray.result_width beforeArray (half shape inputPrecision+1) beforeWidth
  have dependencyRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant≤shape.chunk := by omega
  have pendingFits : 2*arity^(childExponent+2)≤shape.bits := NativeHadamardPhaseCompletedGrid.double_visit_le_bits entryPath.visit (by omega)
  let numeratorBound := CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*entryReturned)*
    4^(2*arity^(childExponent+2))
  have fullGuard := CompactSpectatorInheritedGrid.guard_from_path shape inputPrecision entryPath baselinePrecision growthConstant
    (2*arity^(childExponent+2)) baselineFitsPrecision dependencyRoom pendingFits
  have signedGuard : 2*numeratorBound<2^(half shape inputPrecision) := by dsimp only [numeratorBound]; omega
  have finalGrid := NativeHadamardNormalizationGrid.result_grid (exponent:=childExponent+2) inputPrecision completedDenominator
    numeratorBound beforeArray storedWidth beforeGrid signedGuard
  have signedBounds : ∀ index,|ButterflySigned.signedValue (half shape inputPrecision) (beforeArray index).1|≤(numeratorBound : ℤ) ∧
      |ButterflySigned.signedValue (half shape inputPrecision) (beforeArray index).2|≤(numeratorBound : ℤ) :=
    fun index => ButterflyGuard.represented_bound _ _ completedDenominator numeratorBound (beforeGrid index)
  have integerGuard : 2*(numeratorBound : ℤ)<(2^(half shape inputPrecision) : ℕ) := by exact_mod_cast signedGuard
  let normalizationBudget := NativeHadamardNormalizationOriginal.constant*
    CompactNativeRoleTransferBudget.volume rowCount shape polynomialExponent metadataPrecision
  refine ⟨rootElapsed+normalizationBudget+1,finalBank,finalArray,finalClean,finalHeaders,finalLive,?_,?_,?_,?_,finalWidth,finalGrid,?_⟩
  · have factorBound := CompactComplexInputPhasedRootExecution.stage_factor_one_le (shape:=shape) axesPositive (childExponent+1)
    have volumePositive : 0<CompactNativeRoleTransferBudget.volume rowCount shape polynomialExponent metadataPrecision :=
      Nat.mul_pos rowsPositive (CompactNativeRoleTransferBudget.symbols_pos shape polynomialExponent metadataPrecision)
    have volumeBound : (1 : ℝ)≤CompactNativeRoleTransferBudget.volume rowCount shape polynomialExponent metadataPrecision := by
      exact_mod_cast volumePositive
    have joinBound := one_le_mul_of_one_le_of_one_le volumeBound factorBound
    have normalizationBound := mul_le_mul_of_nonneg_left factorBound
      (mul_nonneg (Nat.cast_nonneg NativeHadamardNormalizationOriginal.constant)
        (Nat.cast_nonneg (CompactNativeRoleTransferBudget.volume rowCount shape polynomialExponent metadataPrecision)))
    simp only [mul_one] at normalizationBound
    dsimp only [normalizationBudget]
    push_cast
    unfold constant
    dsimp only [metadataPrecision] at rootRuntime joinBound normalizationBound ⊢
    nlinarith only [rootRuntime,joinBound,normalizationBound]
  · exact (rootRun.seq normalizationRun).consequence (fun _ equality => equality) (fun _ equality => equality)
      (by dsimp only [normalizationBudget]; omega)
  · dsimp only [finalBank,NativeHadamardNormalizationRootBank.output,SharedPlacementAlphabet.setTape]
    rw [Function.update_self]
    rfl
  · dsimp only [finalBank,NativeHadamardNormalizationRootBank.output,SharedPlacementAlphabet.setTape]
    rw [Function.update_self]
  · intro rawRow polynomialIndex globalAnchor
    have exactReadout := NativeHadamardNormalizationArray.result_normalization beforeArray (half shape inputPrecision)
      completedDenominator (childExponent+2) beforeWidth (numeratorBound : ℤ) signedBounds integerGuard
      (pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex))
    change decoded shape rowCount polynomialExponent inputPrecision (completedDenominator+normalizationIncrease) finalArray
      (pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex))=_
    exact exactReadout.trans (beforeTensor rawRow polynomialIndex globalAnchor)

end
end IntegerMultBounds.Machine.CompactComplexNormalizedRootExecution
