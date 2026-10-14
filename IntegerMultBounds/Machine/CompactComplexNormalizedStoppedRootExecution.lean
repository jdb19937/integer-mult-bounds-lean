module

public import IntegerMultBounds.Machine.CompactComplexNormalizedRootExecution
public import IntegerMultBounds.Machine.NativeHadamardStoppedInputPhase

/-! Positive stopped roots execute both physical phases, their actual stopped
leaf, and physical normalization on the same fixed program as nonstopped roots.
All readiness, source words, signed guards and true denominator progress derive
from the original public-bank certificates, genuine Path and input grid. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexNormalizedStoppedRootExecution
noncomputable section
open Networks
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactRecursiveDependencyBudget (Path)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Grid Width half decoded)
open CompactComplexSourceReadyScalarWorkspace (roles scratch)
open CompactComplexSourceReadyWorkspace (publicTapes ready)
open CompactComplexSourceReadyStoppedLeafCount (returned)
open NativeHadamardStoppedRootPorts (phased)
open CompactComplexAlignedBoundaryPaths (alignedBank)
open RecursiveInterchangeRows (pack)
open SharedPlacementAlphabet (setTape)
variable {stackCount : ℕ} {shape : Shape}
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount ComplexRank25.program
  CompactComplexNormalizedRootExecution.program CompactComplexPhasedRootExecution.program
  CompactComplexInputPhasedRootExecution.program CompactComplexPublicRootExecution.program
  NativeHadamardPhaseRootBank.program NativeHadamardNormalizationRootBank.program

/-- The same fixed normalized root program supports genuine positive stopped
roots. Exact normalized Hadamard output, literal source/live words, full cleanup,
retained originals and true grids have the common positive packing-limit-only
runtime coefficient. No phase/normalization or leaf execution is assumed. -/
theorem positive_root_halts (packingLimit : ℕ) (headerStack pcStack liveStack : Fin stackCount)
    (rows polynomialExponent precision : ℕ) (chunkIndex : Fin shape.chunk)
    {childLeft childExponent levels frames count : ℕ}
    (dependency : Path shape.active childLeft (childExponent+1) levels frames count)
    (activeFits : shape.active≤shape.axes) (pair : BinaryRowProgram.Op (Fin arity))
    (liveDenominator : ℕ) (inputBank : Tapes (publicTapes stackCount roles) 2)
    (stackEmpty : (ready inputBank).tape (CompactComplexSourceReadyOrientationInvariants.savedSlot pcStack)
      ((ready inputBank).head (CompactComplexSourceReadyOrientationInvariants.savedSlot pcStack)-1)=blank)
    (guardReady : CompactComplexSourceReadyGuard.Ready inputBank)
    (dimensionReady : inputBank.head CompactComplexSourceReadyGuard.dimension=1 ∧
      inputBank.tape CompactComplexSourceReadyGuard.dimension=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits shape.axes))
    (rootStopped : ComplexRecursiveCallSchema.stopped shape.axes (childExponent+1)=true)
    (sourceArray : Array shape rows polynomialExponent)
    (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes) (rowsPositive : 0<rows)
    (guardFitsChunk : shape.guard+1≤shape.chunk) (unitPayload : shape.payload=1)
    (sourceWidth : Width shape rows polynomialExponent precision sourceArray)
    (rawHeaders : Placement.active CompactComplexNonleafRoleEntry.headerPlacement (CompactComplexNonleafRoleSourceReturn.base inputBank)=
      ActiveRepairRankHeadersCommands.bank (NativeEndpointCharacterPrepare.raw
        (CompactBinaryBasisSchedule.stage (CompactComplexRecursiveGeometry.node chunkIndex dependency.visit activeFits) pair) rows polynomialExponent
        (ButterflyIndependentGuardHeaders.reservation shape.bits precision)))
    (publicSourceReady : inputBank.head (NativeHadamardStoppedRootPorts.source (stackCount:=stackCount))=0 ∧
      inputBank.tape (NativeHadamardStoppedRootPorts.source (stackCount:=stackCount))=CompactSpectatorLeafAxis.word sourceArray)
    (liveReady : inputBank.head CompactComplexNonleafRoleChildBank.current=1 ∧
      inputBank.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits liveDenominator))
    (targetBlank : inputBank.head CompactComplexNonleafRoleChildBank.target=0 ∧
      inputBank.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank))
    (exponentWord : inputBank.tape (CompactComplexNonleafRoleChildBank.control 1)=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits (childExponent+1)))
    (exponentHead : inputBank.head (CompactComplexNonleafRoleChildBank.control 1)=1)
    (scalarRowLimit basePrecision usedRows growthConstant : ℕ)
    (baselineFits : basePrecision≤precision) (rowsUsedBound : usedRows≤scalarRowLimit)
    (denominatorRoom : CompactComplexDenominatorCapacity.room scalarRowLimit≤shape.chunk)
    (liveLedgerBound : liveDenominator≤CompactComplexDenominatorCapacity.ledger scalarRowLimit basePrecision levels frames count usedRows)
    (publicClean : CompactComplexStoppedRootWorkspaceClean.PublicClean inputBank)
    (dependencyChunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant≤shape.chunk)
    (inputGrid : Grid shape rows polynomialExponent precision liveDenominator
      (CompactRecursiveGridBudget.bound basePrecision growthConstant levels (frames+2*count)) sourceArray) :
    let metadataPrecision := ButterflyIndependentGuardHeaders.reservation shape.bits precision
    let stage := CompactBinaryBasisSchedule.stage (CompactComplexRecursiveGeometry.node chunkIndex dependency.visit activeFits) pair
    let finalDenominator := CompactComplexDenominatorPolicy.leafTarget liveDenominator (childExponent+1)+
      NativeHadamardNormalizationFactor.denominatorIncrease (arity^(childExponent+1))
    ∃ elapsedSteps : ℕ,∃ outputBank : Tapes (CompactComplexSourceReadyWorkspace.tapes stackCount roles) 2,
    ∃ outputArray : Array shape rows polynomialExponent,
      CompactComplexRootWorkspaceClean.Clean outputBank ∧
      NativeHadamardPhaseRootHeaders.Ready stage rows polynomialExponent metadataPrecision outputBank ∧
      NativeHadamardNormalizationRootLive.Ready finalDenominator outputBank ∧
      (elapsedSteps : ℝ)≤CompactComplexNormalizedRootExecution.constant packingLimit*
        (CompactNativeRoleTransferBudget.volume rows shape polynomialExponent metadataPrecision : ℝ)*
        CompactComplexUniformRuntimeCoefficient.stageFactor shape (childExponent+1) ∧
      HoareTime (CompactComplexNormalizedRootExecution.program packingLimit headerStack pcStack liveStack).2
        (fun bank => bank=alignedBank ((ready inputBank).append (SharedBank.empty scratch 2)))
        (fun bank => bank=alignedBank (outputBank.append (SharedBank.empty scratch 2))) elapsedSteps ∧
      outputBank.tape CompactComplexSourceReadyOrientation.source=CompactSpectatorLeafAxis.word outputArray ∧
      outputBank.head CompactComplexSourceReadyOrientation.source=0 ∧
      (∀ index,(outputArray index).1.length=half shape precision+1 ∧ (outputArray index).2.length=half shape precision+1) ∧
      Grid shape rows polynomialExponent precision finalDenominator
        (2*(CompactRecursiveGridBudget.bound basePrecision growthConstant levels (frames+2*count)*4^(arity^(childExponent+1)))) outputArray ∧
      ∀ (rawRow : Fin rows) (polynomialIndex : Fin (2^polynomialExponent)) (globalAnchor : BinaryWalsh.Address shape.bits),
        decoded shape rows polynomialExponent precision finalDenominator outputArray
          (pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex))=
        BinaryColumns.tensorColumns (arity^childExponent)
          (GaussianHadamardBridge.hadamardProduct (GaussianHadamardBridge.allCoordinates arity))
          (fun tensorAddress => decoded shape rows polynomialExponent precision liveDenominator sourceArray
            (pack rawRow (FlatCoordinateLayout.index
              (CompactComplexNonleafChildAddress.insert chunkIndex dependency.visit globalAnchor tensorAddress) polynomialIndex)))
          (CompactComplexNonleafChildAddress.address chunkIndex dependency.visit globalAnchor) := by
  let metadataPrecision := ButterflyIndependentGuardHeaders.reservation shape.bits precision
  let stage := CompactBinaryBasisSchedule.stage (CompactComplexRecursiveGeometry.node chunkIndex dependency.visit activeFits) pair
  let phasedArray := NativeHadamardPhaseOriginal.result stage metadataPrecision sourceArray
  let phasedBank := phased stage metadataPrecision sourceArray inputBank
  let stoppedDenominator := CompactComplexDenominatorPolicy.leafTarget liveDenominator (childExponent+1)
  have chunkPositive : 0<shape.chunk := by omega
  have inputCertificate := NativeHadamardStoppedInputPhase.prepares stage precision basePrecision growthConstant liveDenominator
    dependency pcStack inputBank sourceArray rfl rowsPositive guardPositive axesPositive guardFitsChunk unitPayload baselineFits
    dependencyChunkRoom sourceWidth inputGrid rawHeaders stackEmpty guardReady dimensionReady publicSourceReady liveReady targetBlank
    exponentWord exponentHead publicClean
  have inputPhase := inputCertificate.execution
  have phasedRaw := inputCertificate.raw
  have phasedGrid := inputCertificate.grid
  have rightFits : stage.right≤shape.active := by have := stage.activeAxes; omega
  obtain ⟨rootElapsed,rootNatural,rootRuntime,rootClean,rootWidth,rootGrid,rootTensor,rootRun⟩ :=
    CompactComplexPublicStoppedRootExecution.positive_root_halts packingLimit headerStack pcStack liveStack shape
      rows polynomialExponent metadataPrecision chunkIndex dependency stage.right stage.source.val stage.target.val liveDenominator
      phasedBank (SharedBank.empty scratch 2) (SharedBank.empty (CompactComplexActualCallFullAlignment.localTapes roles) prime)
      inputCertificate.stackEmpty inputCertificate.guardReady
      inputCertificate.dimension rootStopped phasedArray
      guardPositive axesPositive rowsPositive (by dsimp [metadataPrecision,ButterflyIndependentGuardHeaders.reservation]; omega)
      inputCertificate.widths phasedRaw inputCertificate.source
      inputCertificate.current inputCertificate.target inputCertificate.exponentWord inputCertificate.exponentHead
      scalarRowLimit basePrecision usedRows unitPayload rightFits (by exact Nat.le_of_lt stage.source.isLt)
      (by exact Nat.le_of_lt stage.target.isLt) (by simpa only [metadataPrecision,ButterflyIndependentGuardHeaders.reservation,Nat.add_sub_cancel] using baselineFits)
      rowsUsedBound denominatorRoom liveLedgerBound inputCertificate.clean growthConstant dependencyChunkRoom
      (by simpa only [metadataPrecision,ButterflyIndependentGuardHeaders.reservation,Nat.add_sub_cancel,phasedArray] using phasedGrid)
  have metadataReduction : metadataPrecision-2*shape.bits=precision := by
    dsimp only [metadataPrecision,ButterflyIndependentGuardHeaders.reservation]
    exact Nat.add_sub_cancel _ _
  rw [metadataReduction] at rootWidth rootGrid rootTensor rootRun rootClean
  let rootArray := CompactSpectatorLeafGuardOriginal.result .forward shape rows polynomialExponent precision chunkIndex dependency.visit phasedArray
  let rootBank := ready (returned phasedBank (CompactSpectatorLeafAxis.word rootArray) stoppedDenominator)
  have rootHeaders := NativeHadamardStoppedRootPorts.returned_headers stage rows polynomialExponent metadataPrecision phasedBank
    phasedRaw (CompactSpectatorLeafAxis.word rootArray) stoppedDenominator
  have rootLive := NativeHadamardStoppedRootPorts.returned_live phasedBank (CompactSpectatorLeafAxis.word rootArray) stoppedDenominator
  have rootStored : Width shape rows polynomialExponent precision rootArray := by
    intro index
    simpa only [CompactNativeRoleHeaders.recordWidth,metadataPrecision,ButterflyGuard.width,
      ButterflyIndependentGuardSemantics.half_eq] using rootWidth index
  have rootNativeWidth : ∀ index,(rootArray index).1.length=NativePolynomialStageShape.width shape metadataPrecision ∧
      (rootArray index).2.length=NativePolynomialStageShape.width shape metadataPrecision := rootWidth
  have rootSource : rootBank.tape CompactComplexSourceReadyOrientation.source=CompactSpectatorLeafAxis.word rootArray ∧
      rootBank.head CompactComplexSourceReadyOrientation.source=0 :=
    NativeHadamardStoppedRootPorts.returned_source phasedBank (CompactSpectatorLeafAxis.word rootArray) stoppedDenominator
  have pendingFits : arity^(childExponent+1)≤shape.bits := by
    have visitFits := dependency.visit.fits
    have widthActive : arity^(childExponent+1)≤shape.active := by omega
    have activeBits : shape.active≤shape.bits := by
      unfold Shape.bits
      nlinarith only [chunkPositive]
    exact widthActive.trans activeBits
  have selectedWidth : stage.slots*stage.f=arity^(childExponent+1) := by
    change arity*arity^childExponent=arity^(childExponent+1)
    exact (pow_succ' _ _).symm
  have outputPhase := NativeHadamardPhaseOutputBank.runs stage metadataPrecision rfl rowsPositive guardPositive axesPositive
    guardFitsChunk unitPayload rootArray rootNativeWidth rootBank rootClean rootHeaders rootSource.1 rootSource.2
  let phasedResult := NativeHadamardPhaseOriginal.result stage metadataPrecision rootArray
  let beforeNormalization := NativeHadamardPhaseOutputBank.output stage metadataPrecision rootArray rootBank
  have beforeClean := NativeHadamardPhaseOutputBank.output_clean stage metadataPrecision rootArray rootBank rootClean
  have beforeHeaders := NativeHadamardPhaseOutputBank.output_headers stage metadataPrecision rootArray rootBank rootHeaders
  have beforeLive := NativeHadamardNormalizationRootLive.source_update stoppedDenominator rootBank rootLive
    (putWord (fun _ => blank) 0 (NativeZeroPaddingArray.word phasedResult)) 0
  have beforeGrid := NativeHadamardPhaseCompletedGrid.grid_from_growth stage precision basePrecision growthConstant stoppedDenominator
    (arity^(childExponent+1)) dependency baselineFits dependencyChunkRoom pendingFits rootArray rootStored rootGrid
  have beforeWidth := NativeHadamardPhaseOriginal.result_width stage metadataPrecision (half shape precision+1) rootArray
    (by intro index; simpa only [CompactNativeRoleHeaders.recordWidth,metadataPrecision,ButterflyGuard.width,
      ButterflyIndependentGuardSemantics.half_eq] using rootWidth index)
  have beforeNative : ∀ index,(phasedResult index).1.length=NativePolynomialStageShape.width shape metadataPrecision ∧
      (phasedResult index).2.length=NativePolynomialStageShape.width shape metadataPrecision :=
    NativeHadamardPhaseOriginal.result_width stage metadataPrecision _ rootArray rootNativeWidth
  have liveFits := CompactComplexDenominatorCapacity.target_volume dependency scalarRowLimit basePrecision precision usedRows
    liveDenominator stoppedDenominator rows polynomialExponent baselineFits rowsUsedBound denominatorRoom liveLedgerBound
    (by unfold stoppedDenominator CompactComplexDenominatorPolicy.leafTarget; omega) rowsPositive
  have volumeEquation : ButterflySpectatorGeometry.Size rows shape.bits (2^polynomialExponent)*(2*(half shape precision+2))=
      CompactNativeRoleTransferBudget.volume rows shape polynomialExponent metadataPrecision := by
    rw [CompactSpectatorVisitGeometry.coefficient_count]
    unfold CompactNativeRoleTransferBudget.volume CompactNativeRoleOriginal.symbols CompactNativeRoleOriginal.inner
      CompactNativeRoleHeaders.recordWidth ButterflyGuard.width half metadataPrecision ButterflyIndependentGuardHeaders.reservation ButterflyGuard.halfWidth
    ring
  rw [volumeEquation] at liveFits
  have normalizationRun := NativeHadamardNormalizationRootBank.runs stage metadataPrecision stoppedDenominator rowsPositive
    guardPositive axesPositive chunkPositive unitPayload (by rw [selectedWidth]; exact pendingFits) liveFits phasedResult beforeNative
    beforeNormalization beforeClean beforeHeaders (by simp [beforeNormalization,NativeHadamardPhaseOutputBank.output,setTape]; rfl)
    (by simp [beforeNormalization,NativeHadamardPhaseOutputBank.output,setTape]) beforeLive
  let finalArray := NativeHadamardNormalizationArray.result phasedResult
  let finalBank := NativeHadamardNormalizationRootBank.output stage stoppedDenominator phasedResult beforeNormalization
  let increase := NativeHadamardNormalizationFactor.denominatorIncrease (arity^(childExponent+1))
  have increaseEquation : NativeHadamardNormalizationHeaders.increase stage=increase := congrArg NativeHadamardNormalizationFactor.denominatorIncrease selectedWidth
  have finalLive := NativeHadamardNormalizationRootBank.output_live stage stoppedDenominator phasedResult beforeNormalization
  rw [increaseEquation] at finalLive
  let numeratorBound := CompactRecursiveGridBudget.bound basePrecision growthConstant levels (frames+2*count)*4^(arity^(childExponent+1))
  have fullGuard := CompactSpectatorInheritedGrid.guard_from_path shape precision dependency basePrecision growthConstant
    (arity^(childExponent+1)) baselineFits dependencyChunkRoom pendingFits
  have signedGuard : 2*numeratorBound<2^(half shape precision) := by dsimp only [numeratorBound]; omega
  have finalGrid := NativeHadamardNormalizationGrid.result_grid (exponent:=childExponent+1) precision stoppedDenominator numeratorBound
    phasedResult (by intro index; simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using beforeWidth index) beforeGrid signedGuard
  have signedBounds : ∀ index,|ButterflySigned.signedValue (half shape precision) (phasedResult index).1|≤(numeratorBound : ℤ) ∧
      |ButterflySigned.signedValue (half shape precision) (phasedResult index).2|≤(numeratorBound : ℤ) :=
    fun index => ButterflyGuard.represented_bound _ _ stoppedDenominator numeratorBound (beforeGrid index)
  have integerGuard : 2*(numeratorBound : ℤ)<(2^(half shape precision) : ℕ) := by exact_mod_cast signedGuard
  let phaseBudget := NativeHadamardPhaseOriginal.constant*CompactNativeRoleTransferBudget.volume rows shape polynomialExponent metadataPrecision
  let normalizationBudget := NativeHadamardNormalizationOriginal.constant*CompactNativeRoleTransferBudget.volume rows shape polynomialExponent metadataPrecision
  refine ⟨phaseBudget+rootElapsed+phaseBudget+normalizationBudget+3,finalBank,finalArray,
    NativeHadamardNormalizationRootBank.output_clean _ _ _ _ beforeClean,
    NativeHadamardNormalizationRootBank.output_headers _ _ _ _ _ beforeHeaders,finalLive,?_,?_,?_,?_,
    NativeHadamardNormalizationArray.result_width _ _ beforeWidth,finalGrid,?_⟩
  · have factorBound := CompactComplexInputPhasedRootExecution.stage_factor_one_le (shape:=shape) axesPositive (childExponent+1)
    have volumePositive : 0<CompactNativeRoleTransferBudget.volume rows shape polynomialExponent metadataPrecision :=
      Nat.mul_pos rowsPositive (CompactNativeRoleTransferBudget.symbols_pos shape polynomialExponent metadataPrecision)
    have volumeBound : (1 : ℝ)≤CompactNativeRoleTransferBudget.volume rows shape polynomialExponent metadataPrecision := by exact_mod_cast volumePositive
    have joinBound := one_le_mul_of_one_le_of_one_le volumeBound factorBound
    have phaseBound := mul_le_mul_of_nonneg_left factorBound
      (mul_nonneg (Nat.cast_nonneg NativeHadamardPhaseOriginal.constant) (Nat.cast_nonneg (CompactNativeRoleTransferBudget.volume rows shape polynomialExponent metadataPrecision)))
    have normalizationBound := mul_le_mul_of_nonneg_left factorBound
      (mul_nonneg (Nat.cast_nonneg NativeHadamardNormalizationOriginal.constant) (Nat.cast_nonneg (CompactNativeRoleTransferBudget.volume rows shape polynomialExponent metadataPrecision)))
    simp only [mul_one] at phaseBound normalizationBound
    dsimp only [phaseBudget,normalizationBudget]
    push_cast
    unfold CompactComplexNormalizedRootExecution.constant CompactComplexPhasedRootExecution.constant
      CompactComplexInputPhasedRootExecution.constant
    dsimp only [metadataPrecision] at rootRuntime joinBound phaseBound normalizationBound ⊢
    nlinarith only [rootRuntime,joinBound,phaseBound,normalizationBound]
  · have stoppedRun : HoareTime (CompactComplexPublicRootExecution.program packingLimit headerStack pcStack liveStack).2
        (fun bank => bank=alignedBank ((ready phasedBank).append (SharedBank.empty scratch 2)))
        (fun bank => bank=alignedBank (rootBank.append (SharedBank.empty scratch 2))) rootElapsed := rootRun
    unfold CompactComplexNormalizedRootExecution.program CompactComplexPhasedRootExecution.program CompactComplexInputPhasedRootExecution.program
    exact (((inputPhase.seq stoppedRun).seq outputPhase).seq normalizationRun).consequence (fun _ equality => equality)
      (fun _ equality => equality) (by dsimp only [phaseBudget,normalizationBudget,metadataPrecision]; omega)
  · dsimp only [finalBank,NativeHadamardNormalizationRootBank.output,setTape]
    rw [Function.update_self]
    rfl
  · dsimp only [finalBank,NativeHadamardNormalizationRootBank.output,setTape]
    rw [Function.update_self]
  · intro rawRow polynomialIndex globalAnchor
    have tensorInput : (fun tensorAddress => decoded shape rows polynomialExponent precision liveDenominator phasedArray
        (pack rawRow (FlatCoordinateLayout.index
          (CompactComplexNonleafChildAddress.insert chunkIndex dependency.visit globalAnchor tensorAddress) polynomialIndex)))=
        GaussianHadamardPhase.tensorPhase (arity^childExponent)
          (fun tensorAddress => decoded shape rows polynomialExponent precision liveDenominator sourceArray
            (pack rawRow (FlatCoordinateLayout.index
              (CompactComplexNonleafChildAddress.insert chunkIndex dependency.visit globalAnchor tensorAddress) polynomialIndex))) := by
      funext tensorAddress
      have corrected := NativeHadamardPhaseRootBank.decoded_at_node chunkIndex dependency activeFits pair precision basePrecision growthConstant
        liveDenominator baselineFits dependencyChunkRoom sourceArray sourceWidth inputGrid rawRow polynomialIndex
        (CompactComplexNonleafChildAddress.insert chunkIndex dependency.visit globalAnchor tensorAddress)
      rw [GaussianHadamardPhase.tensorPhase_apply]
      simpa only [phasedArray,stage,metadataPrecision,CompactComplexNonleafChildAddress.address_insert] using corrected
    have outputReadout := NativeHadamardPhaseCompletedGrid.decoded_at_node_from_growth chunkIndex dependency activeFits pair precision basePrecision
      growthConstant stoppedDenominator (arity^(childExponent+1)) baselineFits dependencyChunkRoom pendingFits rootArray rootStored rootGrid
      rawRow polynomialIndex globalAnchor
    let originalSlice := fun tensorAddress => decoded shape rows polynomialExponent precision liveDenominator sourceArray
      (pack rawRow (FlatCoordinateLayout.index
        (CompactComplexNonleafChildAddress.insert chunkIndex dependency.visit globalAnchor tensorAddress) polynomialIndex))
    let address := CompactComplexNonleafChildAddress.address chunkIndex dependency.visit globalAnchor
    have converted := congrArg (fun operation : BinaryColumns.Operator arity (arity^childExponent) => operation originalSlice address)
      (GaussianHadamardBridge.fullFrame_bridge (addressBits:=arity) (arity^childExponent))
    change BinaryColumns.tensorColumns (arity^childExponent) (GaussianHadamardBridge.hadamardProduct (GaussianHadamardBridge.allCoordinates arity))
        originalSlice address=GaussianHadamardBridge.normalization^(arity*arity^childExponent)*
        GaussianHadamardPhase.tensorPhase (arity^childExponent)
          (ComplexEndpoints.fullFrame (arity^childExponent) (GaussianHadamardPhase.tensorPhase (arity^childExponent) originalSlice)) address at converted
    rw [show arity*arity^childExponent=arity^(childExponent+1) from (pow_succ' _ _).symm,GaussianHadamardPhase.tensorPhase_apply] at converted
    have exactRoot := rootTensor rawRow polynomialIndex globalAnchor
    rw [tensorInput] at exactRoot
    have normalized := NativeHadamardNormalizationArray.result_normalization phasedResult (half shape precision) stoppedDenominator
      (childExponent+1) beforeWidth (numeratorBound : ℤ) signedBounds integerGuard
      (pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex))
    calc
      _=GaussianHadamardBridge.normalization^(arity^(childExponent+1))*
          decoded shape rows polynomialExponent precision stoppedDenominator phasedResult
            (pack rawRow (FlatCoordinateLayout.index globalAnchor polynomialIndex)) := normalized
      _=GaussianHadamardBridge.normalization^(arity^(childExponent+1)) *
          ((∏ column : Fin (arity^childExponent),BinaryPhase.phase (BinaryPhase.weightPhase (address column))) *
            ComplexEndpoints.fullFrame (arity^childExponent) (GaussianHadamardPhase.tensorPhase (arity^childExponent) originalSlice) address) := by
        rw [outputReadout,exactRoot]
      _=_ := converted.symm

end
end IntegerMultBounds.Machine.CompactComplexNormalizedStoppedRootExecution
