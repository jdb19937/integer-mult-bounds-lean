module

public import IntegerMultBounds.Machine.CompactComplexPublicRootExecution
public import IntegerMultBounds.Machine.NativeHadamardPhaseRootBank

/-! Actual input-phase correction and full nonstopped recursive root execution
compose on the same fixed bank. Every transition, including the joining edge,
is paid uniformly; output tensor readout derives from the original coefficients.
The output phase, normalization and public paper-format adapter remain separate. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexInputPhasedRootExecution
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

/-- One fixed program before every shape, input, exponent and history. -/
def program (packingLimit : ℕ) (headerStack pcStack liveStack : Fin stackCount) :=
  (⟨_,seq (NativeHadamardPhaseRootBank.program (stackCount:=stackCount)).2
    (CompactComplexPublicRootExecution.program packingLimit headerStack pcStack liveStack).2⟩ :
      Σ stateCount,Program (CompactComplexActualCallFullAlignment.tapes stackCount roles) stateCount prime)

/-- The input phase and one joining edge have one fixed additional coefficient. -/
def constant (packingLimit : ℕ) : ℝ :=
  CompactComplexUniformRootConstant.constant packingLimit+(NativeHadamardPhaseOriginal.constant : ℝ)+1

theorem constant_positive (packingLimit : ℕ) : 0<constant packingLimit := by
  have rootPositive := CompactComplexUniformRootConstant.constant_positive packingLimit
  have phaseNonnegative : (0 : ℝ)≤NativeHadamardPhaseOriginal.constant := Nat.cast_nonneg _
  unfold constant
  linarith

theorem stage_factor_one_le (axesPositive : 0<shape.axes) (exponent : ℕ) :
    1≤CompactComplexUniformRuntimeCoefficient.stageFactor shape exponent := by
  have sigmaNonnegative : 0≤Parameters.sigma := by norm_num [Parameters.sigma]
  have leafPowerNonnegative : 0≤Parameters.beta*(1-Parameters.sigma) := by
    norm_num [Parameters.beta,Parameters.sigma]
  have widthPower := Real.one_le_rpow (x:=((arity^exponent : ℕ) : ℝ))
    (by exact_mod_cast Nat.one_le_pow exponent arity (by decide)) sigmaNonnegative
  have leafPower := Real.one_le_rpow (x:=(shape.axes : ℝ)) (by exact_mod_cast axesPositive) leafPowerNonnegative
  have localNonnegative : 0≤(shape.guard : ℝ)^Parameters.tau *
      (shape.axes : ℝ)^(Parameters.beta*(Parameters.tau-Parameters.sigma)) := by positivity
  unfold CompactComplexUniformRuntimeCoefficient.stageFactor
  exact one_le_mul_of_one_le_of_one_le widthPower (leafPower.trans (le_add_of_nonneg_right localNonnegative))

/-- The literal input phase runs before the entire actual root trace, retaining
its exact halted output and cleanup. All transformed-input guards and readiness
are derived from original Paths and the unchanged initial bank; no phase run,
recursive execution, child result, transform or total-time assertion is assumed. -/
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
        (fun bank => bank=alignedBank (outputBank.append
          (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))) elapsedSteps ∧
      outputBank.tape CompactComplexSourceReadyOrientation.source=CompactSpectatorLeafAxis.word outputArray ∧
      outputBank.head CompactComplexSourceReadyOrientation.source=0 ∧
      (∀ index,(outputArray index).1.length=half shape inputPrecision+1 ∧
        (outputArray index).2.length=half shape inputPrecision+1) ∧
      Grid shape rowCount polynomialExponent inputPrecision
        (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1))
        (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*entryReturned)*
          4^(2*arity^(childExponent+2))) outputArray ∧
      ∀ (rawRow : Fin rowCount) (polynomialIndex : Fin (2^polynomialExponent)) (globalAnchor : BinaryWalsh.Address shape.bits),
        decoded shape rowCount polynomialExponent inputPrecision
          (CompactComplexDenominatorPolicy.networkTarget initialLive (childExponent+1)) outputArray
          (pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex))=
        ComplexEndpoints.fullFrame (arity^(childExponent+1))
          (Networks.GaussianHadamardPhase.tensorPhase (arity^(childExponent+1))
            (fun tensorAddress => decoded shape rowCount polynomialExponent inputPrecision initialLive originalCoefficients
              (pack rawRow (FlatCoordinateLayout.index
                (CompactComplexNonleafChildAddress.insert phaseCoordinate entryPath.visit globalAnchor tensorAddress) polynomialIndex))))
          (CompactComplexNonleafChildAddress.address phaseCoordinate entryPath.visit globalAnchor) := by
  let metadataPrecision := ButterflyIndependentGuardHeaders.reservation shape.bits inputPrecision
  let stage := parent phaseCoordinate entryPath.visit activeFits pair
  let phasedInput := NativeHadamardPhaseOriginal.result stage metadataPrecision originalCoefficients
  have rowGuards := CompactComplexRecursivePathRows.recursive_row_guards entryPath activeFits roles shape.chunk
    (by unfold roles CompactComplexRolePhaseSite.roleCount; positivity) chunkPositive (by omega)
  have rowsPositive : 0<rowCount := by
    rw [rowsPadded]
    exact lt_of_lt_of_le rowGuards.2.2.2.1 (Nat.div_le_self _ _)
  have originalWidth : ∀ index,(originalCoefficients index).1.length=NativePolynomialStageShape.width shape metadataPrecision ∧
      (originalCoefficients index).2.length=NativePolynomialStageShape.width shape metadataPrecision := by
    intro index
    simpa only [NativePolynomialStageShape.width,metadataPrecision,ButterflyIndependentGuardSemantics.half_eq,
      ButterflyGuard.width] using inputWidth index
  have phasedWidth : Width shape rowCount polynomialExponent inputPrecision phasedInput := by
    intro index
    exact NativeHadamardPhaseOriginal.result_width stage metadataPrecision _ originalCoefficients inputWidth index
  have dependencyRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant≤shape.chunk := by omega
  have phasedGrid : Grid shape rowCount polynomialExponent inputPrecision initialLive
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*entryReturned))
      phasedInput := NativeHadamardPhaseOriginal.grid_from_path stage inputPrecision baselinePrecision growthConstant initialLive
        entryPath baselineFitsPrecision dependencyRoom originalCoefficients inputWidth inputGrid
  have phaseRun := NativeHadamardPhaseRootBank.runs stage metadataPrecision rfl rowsPositive (by omega)
    axesPositive guardFitsChunk unitPayload originalCoefficients originalWidth controlBank queueBank scalarHeaders tailBank
    originalStorage auxiliaryBank
  obtain ⟨childPathBudget,rootElapsed,outputBank,outputArray,clean,outputHeaders,rootNaturalBound,rootRuntime,rootRun,
      outputWord,outputHead,outputWidth,outputGrid,rootTensor⟩ :=
    CompactComplexPublicRootExecution.root_runs phaseCoordinate activeFits pair polynomialExponent
      inputPrecision baselinePrecision growthConstant baselineLive packingLimit guardPositive guardFitsChunk
      headerStack pcStack liveStack largeAxes activePositive axesPositive chunkPositive unitPayload packingFamily
      childChunkRoom scalarChunkRoom precisionReserve baselineFits baselineFitsPrecision growthReserve denominatorRoom
      childExponent entryPath rowsPadded nodeNonstopped initialLive phasedInput phasedWidth phasedGrid
      controlBank queueBank scalarHeaders tailBank originalStorage auxiliaryBank countBlank currentReady targetBlank
      clockBlank auxiliaryFree exponentReady control28Blank control29Blank initialLedger stackOrigin savedAssociated
      pcHeaderDistinct pcLiveDistinct headerLiveDistinct originalProtectedTails
  let phaseBudget := NativeHadamardPhaseOriginal.constant*
    CompactNativeRoleTransferBudget.volume rowCount shape polynomialExponent metadataPrecision
  refine ⟨phaseBudget+rootElapsed+1,outputBank,outputArray,clean,outputHeaders,?_,?_,outputWord,outputHead,outputWidth,outputGrid,?_⟩
  · have factorBound := stage_factor_one_le (shape:=shape) axesPositive (childExponent+1)
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
    dsimp only [metadataPrecision,CompactComplexUniformRecursiveRootExecution.constant] at rootRuntime joinBound phaseBound ⊢
    nlinarith only [rootRuntime,joinBound,phaseBound]
  · exact (phaseRun.seq rootRun).consequence (fun bank equality => equality)
      (fun bank equality => equality) (by dsimp only [phaseBudget]; omega)
  · intro rawRow polynomialIndex globalAnchor
    rw [rootTensor]
    have tensorInput : (fun tensorAddress => decoded shape rowCount polynomialExponent inputPrecision initialLive phasedInput
        (pack rawRow (FlatCoordinateLayout.index
          (CompactComplexNonleafChildAddress.insert phaseCoordinate entryPath.visit globalAnchor tensorAddress) polynomialIndex))) =
        Networks.GaussianHadamardPhase.tensorPhase (arity^(childExponent+1))
          (fun tensorAddress => decoded shape rowCount polynomialExponent inputPrecision initialLive originalCoefficients
            (pack rawRow (FlatCoordinateLayout.index
              (CompactComplexNonleafChildAddress.insert phaseCoordinate entryPath.visit globalAnchor tensorAddress) polynomialIndex))) := by
      funext tensorAddress
      have corrected := NativeHadamardPhaseRootBank.decoded_at_node phaseCoordinate entryPath activeFits pair
        inputPrecision baselinePrecision growthConstant initialLive baselineFitsPrecision dependencyRoom originalCoefficients
        inputWidth inputGrid rawRow polynomialIndex
        (CompactComplexNonleafChildAddress.insert phaseCoordinate entryPath.visit globalAnchor tensorAddress)
      rw [Networks.GaussianHadamardPhase.tensorPhase_apply]
      simpa only [phasedInput,stage,metadataPrecision,CompactComplexChildHeadersData.parent,
        CompactComplexNonleafChildAddress.address_insert] using corrected
    rw [tensorInput]

end
end IntegerMultBounds.Machine.CompactComplexInputPhasedRootExecution
