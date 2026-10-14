module

public import IntegerMultBounds.Machine.NativeHadamardPhaseReadout
public import IntegerMultBounds.Machine.NativeEndpointCharacterCanonicalOriginalBudget
public import IntegerMultBounds.Machine.CompactSpectatorInheritedGrid
public import IntegerMultBounds.Networks.ComplexEndpointGrid

/-! One fixed physical unit-weight phase program for the actual native source
word. Existing original-header setup, shared tape placement, signed arithmetic,
full cleanup and parent-volume cost are reused unchanged. -/

@[expose] public section
namespace IntegerMultBounds.Machine.NativeHadamardPhaseOriginal
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactComplexRecursiveGeometry (arity)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Width Grid decoded)
variable {shape : Shape} {rows ell tapeCount : ℕ}

def fixedWeights : List (ZMod 4) := NativeHadamardPhaseReadout.weights arity

theorem fixedWeights_length : fixedWeights.length=arity :=
  NativeHadamardPhaseReadout.weights_length arity

attribute [local irreducible] arity fixedWeights NativeEndpointCharacterCanonicalOriginal.program

/-- Fixed before every shape, visit depth, polynomial width and input word. -/
def program (focus : Fin 15 → Fin tapeCount) (source : Fin tapeCount) :=
  NativeEndpointCharacterCanonicalOriginal.program focus source 1 arity fixedWeights

def constant : ℕ := NativeEndpointCharacterCanonicalOriginalBudget.constant 1

theorem constant_pos : 0<constant := by
  unfold constant NativeEndpointCharacterCanonicalOriginalBudget.constant
  omega

def coefficients (input : Array shape rows ell) :
    Fin ((rows*2^shape.bits)*2^ell) → ButterflyStreamData.Coefficient :=
  fun index => input (Fin.cast (Nat.mul_assoc rows (2^shape.bits) (2^ell)) index)

def result (stage : Stage shape) (metadataPrecision : ℕ) (input : Array shape rows ell) : Array shape rows ell :=
  fun index => AllAxisPolynomialLiteralEndpoint.result
    (NativePolynomialStageShape.stage stage ell metadataPrecision) arity fixedWeights
    (coefficients input) (Fin.cast (Nat.mul_assoc rows (2^shape.bits) (2^ell)).symm index)

def resultCaller (caller : Tapes tapeCount 2) (source : Fin tapeCount)
    (stage : Stage shape) (metadataPrecision : ℕ) (input : Array shape rows ell) :=
  SharedPlacementAlphabet.setTape caller source
    (putWord (fun _ => blank) 0 (NativeZeroPaddingArray.word (result stage metadataPrecision input))) 0

theorem coefficients_word (input : Array shape rows ell) :
    UnitPhaseFullStreamNormalized.serialized (coefficients input)=NativeZeroPaddingArray.word input := by
  unfold UnitPhaseFullStreamNormalized.serialized NativeZeroPaddingArray.word coefficients
  congr 1
  exact (List.ofFn_congr (Nat.mul_assoc rows (2^shape.bits) (2^ell)).symm
    (fun index => ButterflyStreamData.encoded (input index))).symm

theorem result_word (stage : Stage shape) (metadataPrecision : ℕ) (input : Array shape rows ell) :
    UnitPhaseFullStreamNormalized.serialized
      (AllAxisPolynomialLiteralEndpoint.result (NativePolynomialStageShape.stage stage ell metadataPrecision)
        arity fixedWeights (coefficients input)) =
      NativeZeroPaddingArray.word (result stage metadataPrecision input) := by
  unfold UnitPhaseFullStreamNormalized.serialized NativeZeroPaddingArray.word result
  congr 1
  exact List.ofFn_congr (Nat.mul_assoc rows (2^shape.bits) (2^ell))
    (fun index => ButterflyStreamData.encoded
      (AllAxisPolynomialLiteralEndpoint.result (NativePolynomialStageShape.stage stage ell metadataPrecision)
        arity fixedWeights (coefficients input) index))

/-- Complete physical source/sink correction with one geometry-independent
coefficient. Only source changes; arbitrary caller frames are preserved and
all sixty-seven borrowed private tapes are blank again at zero heads. -/
theorem runs (focus : Fin 15 → Fin tapeCount) (source : Fin tapeCount)
    (caller : Tapes tapeCount 2) (stage : Stage shape) (metadataPrecision : ℕ)
    (slotCount : stage.slots=arity) (rowsPositive : 0<rows)
    (guardPositive : 0<shape.guard) (axesPositive : 0<shape.axes)
    (guardFits : shape.guard+1≤shape.chunk) (unitPayload : shape.payload=1)
    (input : Array shape rows ell)
    (inputWidth : ∀ index, (input index).1.length=NativePolynomialStageShape.width shape metadataPrecision ∧
      (input index).2.length=NativePolynomialStageShape.width shape metadataPrecision)
    (headersReady : ∀ header, caller.tape (focus header)=RadixZeroFill.encodedBinary
      (NativeEndpointCharacterCopy.words stage rows ell metadataPrecision header))
    (headersPositioned : ∀ header, caller.head (focus header)=1)
    (sourceReady : caller.tape source=putWord (fun _ => blank) 0 (NativeZeroPaddingArray.word input))
    (sourcePositioned : caller.head source=0) :
    HoareTime (program focus source)
      (fun bank => bank=caller.append (FixedHeaderBankCopy.empty 67))
      (fun bank => bank=(resultCaller caller source stage metadataPrecision input).append
        (FixedHeaderBankCopy.empty 67))
      (constant*CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision) := by
  let nativeCoefficients : Fin (((rows/1)*2^shape.bits)*2^ell) → ButterflyStreamData.Coefficient :=
    fun index => coefficients input (Fin.cast (by rw [Nat.div_one]) index)
  have inputCoefficientsWidth : ∀ index, (nativeCoefficients index).1.length=
      NativePolynomialStageShape.width shape metadataPrecision ∧
      (nativeCoefficients index).2.length=NativePolynomialStageShape.width shape metadataPrecision :=
    fun index => inputWidth _
  have countEquation : ((rows/1)*2^shape.bits)*2^ell=(rows*2^shape.bits)*2^ell := by rw [Nat.div_one]
  have serializedNative : UnitPhaseFullStreamNormalized.serialized nativeCoefficients=NativeZeroPaddingArray.word input := by
    calc
      _=UnitPhaseFullStreamNormalized.serialized (coefficients input) := by
        unfold UnitPhaseFullStreamNormalized.serialized nativeCoefficients
        congr 1
        rw [List.ofFn_congr countEquation]
        simp only [Fin.cast_cast,Fin.cast_refl,id_eq]
      _=_ := coefficients_word input
  have serializedResult : UnitPhaseFullStreamNormalized.serialized
      (AllAxisPolynomialLiteralEndpoint.result (NativePolynomialStageShape.stage stage ell metadataPrecision)
        arity fixedWeights nativeCoefficients)=NativeZeroPaddingArray.word (result stage metadataPrecision input) := by
    calc
      _=UnitPhaseFullStreamNormalized.serialized
          (AllAxisPolynomialLiteralEndpoint.result (NativePolynomialStageShape.stage stage ell metadataPrecision)
            arity fixedWeights (coefficients input)) := by
        unfold UnitPhaseFullStreamNormalized.serialized
        congr 1
        rw [List.ofFn_congr countEquation]
        apply List.ofFn_inj.mpr
        funext index
        simp only [AllAxisPolynomialLiteralEndpoint.result,nativeCoefficients,
          Fin.cast_cast,Fin.cast_refl,id_eq,Fin.val_cast]
      _=_ := result_word stage metadataPrecision input
  have original := NativeEndpointCharacterCanonicalOriginal.runs focus source caller 1 (by decide)
    stage rows ell metadataPrecision guardPositive axesPositive (by omega) (by simpa using rowsPositive)
    fixedWeights (slotCount.trans fixedWeights_length.symm)
  have execution := original nativeCoefficients inputCoefficientsWidth
    headersReady headersPositioned (by rw [serializedNative]; exact sourceReady) sourcePositioned
  rw [slotCount] at execution
  have paid := NativeEndpointCharacterCanonicalOriginalBudget.cost_linear (t:=tapeCount) 1
    stage rows ell metadataPrecision (by simpa using rowsPositive) axesPositive guardPositive guardFits unitPayload
  apply execution.consequence (fun _ equality => equality) _ paid
  intro bank equality
  unfold NativeEndpointCharacterLifecycle.resultCaller at equality
  change bank=(SharedPlacementAlphabet.setTape caller source
    (putWord (fun _ => blank) 0 (UnitPhaseFullStreamNormalized.serialized
      (AllAxisPolynomialLiteralEndpoint.result (N:=(rows/1)*2^shape.bits) (R:=2^ell)
        (NativePolynomialStageShape.stage stage ell metadataPrecision) arity fixedWeights nativeCoefficients))) 0).append
      (FixedHeaderBankCopy.empty 67) at equality
  rw [serializedResult] at equality
  exact equality

theorem result_width (stage : Stage shape) (metadataPrecision wordWidth : ℕ) (input : Array shape rows ell)
    (inputWidth : ∀ index, (input index).1.length=wordWidth ∧ (input index).2.length=wordWidth)
    (index : Fin (rows*(2^shape.bits*2^ell))) :
    (result stage metadataPrecision input index).1.length=wordWidth ∧
      (result stage metadataPrecision input index).2.length=wordWidth := by
  exact AllAxisPolynomialLiteralEndpoint.result_width _ _ _ _ wordWidth
    (fun index => inputWidth _) _

/-- Actual emitted signed words have the literal scanner-selected unit phase,
with no new denominator, extra numerator reserve, or semantic output premise. -/
theorem signed_decoded (stage : Stage shape) (metadataPrecision numeratorBits denominator : ℕ)
    (input : Array shape rows ell)
    (inputWidth : ∀ index, (input index).1.length=numeratorBits+1 ∧ (input index).2.length=numeratorBits+1)
    (signedGuard : ∀ index, |ButterflySigned.signedValue numeratorBits (input index).1|<(2^numeratorBits : ℕ) ∧
      |ButterflySigned.signedValue numeratorBits (input index).2|<(2^numeratorBits : ℕ))
    (index : Fin (rows*(2^shape.bits*2^ell))) :
    ButterflyStreamSemantics.decode numeratorBits denominator (result stage metadataPrecision input index) =
      Networks.BinaryPhase.phase ((AllAxisPolynomialLiteralEndpoint.phase
        (NativePolynomialStageShape.stage stage ell metadataPrecision) arity fixedWeights
        (index.val/2^ell)).val : ZMod 4) *
        ButterflyStreamSemantics.decode numeratorBits denominator (input index) := by
  have decodedPhase := UnitPhaseSigned.words_phase
    (AllAxisPolynomialLiteralEndpoint.phase (NativePolynomialStageShape.stage stage ell metadataPrecision)
      arity fixedWeights (index.val/2^ell))
    (UnitPhasePolynomialArray.components (input index)) numeratorBits denominator
    (by intro component; unfold UnitPhasePolynomialArray.components;
        split_ifs <;> first | exact (inputWidth index).1 | exact (inputWidth index).2)
    (by intro component; fin_cases component <;>
        first | exact (signedGuard index).1 | exact (signedGuard index).2)
  simpa only [result,AllAxisPolynomialLiteralEndpoint.result,coefficients,
    Fin.cast_cast,Fin.cast_refl,Fin.val_cast,id_eq,ButterflyStreamSemantics.decode,
    UnitPhasePolynomialArray.components,ite_true,show (1 : ℕ)≠0 by decide,ite_false] using decodedPhase

/-- The phase scanner's physical index for the original coefficient's address
record, including the unchanged expanded polynomial codec payload. -/
def recordIndex (metadataPrecision : ℕ) (index : Fin (rows*(2^shape.bits*2^ell))) :
    Fin (rows*(NativePolynomialStageShape.shape shape ell metadataPrecision).recordWidth) :=
  ⟨(index.val/2^ell)*(NativePolynomialStageShape.shape shape ell metadataPrecision).payload, by
    have recordFits : index.val/2^ell<rows*2^shape.bits := by
      apply (Nat.div_lt_iff_lt_mul (pow_pos (by decide) ell)).mpr
      simpa only [Nat.mul_assoc] using index.isLt
    have payloadPositive : 0<(NativePolynomialStageShape.shape shape ell metadataPrecision).payload := by
      have := NativePolynomialStageShape.payload_fits shape ell metadataPrecision
      change 0<NativePolynomialStageShape.payload shape ell metadataPrecision
      omega
    have fits := Nat.mul_lt_mul_of_pos_right recordFits payloadPositive
    simpa only [Shape.recordWidth,NativePolynomialStageShape.bits,Nat.mul_assoc] using fits⟩

theorem recordIndex_quotient (metadataPrecision : ℕ) (index : Fin (rows*(2^shape.bits*2^ell))) :
    (recordIndex metadataPrecision index).val/
      (NativePolynomialStageShape.shape shape ell metadataPrecision).payload=index.val/2^ell := by
  apply Nat.mul_div_cancel
  have := NativePolynomialStageShape.payload_fits shape ell metadataPrecision
  change 0<NativePolynomialStageShape.payload shape ell metadataPrecision
  omega

/-- The actual scanner-selected phase in every emitted coefficient is the
exact front/back tensor correction, derived from its original physical record. -/
theorem phase_readout (stage : Stage shape) (metadataPrecision : ℕ) (slotCount : stage.slots=arity)
    (index : Fin (rows*(2^shape.bits*2^ell))) :
    Networks.BinaryPhase.phase ((AllAxisPolynomialLiteralEndpoint.phase
      (NativePolynomialStageShape.stage stage ell metadataPrecision) arity fixedWeights
      (index.val/2^ell)).val : ZMod 4) =
      ∏ column : Fin stage.f, Networks.BinaryPhase.phase (Networks.BinaryPhase.weightPhase
        (NativeEndpointCharacterReadout.coordinates (NativePolynomialStageShape.stage stage ell metadataPrecision)
          (recordIndex metadataPrecision index) column)) := by
  have weightsEquation : fixedWeights=NativeHadamardPhaseReadout.weights stage.slots := by
    rw [slotCount]
    unfold fixedWeights
    rfl
  have accumulator := NativeHadamardPhaseReadout.accumulator
    (NativePolynomialStageShape.stage stage ell metadataPrecision) (recordIndex metadataPrecision index)
  rw [recordIndex_quotient] at accumulator
  change ((AllAxisPhaseFlagsCaller.phase (NativePolynomialStageShape.stage stage ell metadataPrecision)
    stage.slots (NativeHadamardPhaseReadout.weights stage.slots)
    (BinaryAddressTableData.row (NativePolynomialStageShape.shape shape ell metadataPrecision).bits
      (index.val/2^ell))).val : ZMod 4) =
      ∑ column : Fin stage.f, Networks.BinaryPhase.weightPhase
        (NativeEndpointCharacterReadout.coordinates (NativePolynomialStageShape.stage stage ell metadataPrecision)
          (recordIndex metadataPrecision index) column) at accumulator
  unfold AllAxisPolynomialLiteralEndpoint.phase
  rw [←slotCount,weightsEquation]
  rw [accumulator,Networks.BinaryPhase.phase_sum]

/-- Original dependency Paths derive exact tensor-phase readout of the actual
emitted word. No phase, signed-guard or corrected-output assertion is assumed. -/
theorem decoded_from_path (stage : Stage shape) (slotCount : stage.slots=arity)
    (precision baseline growthConstant denominator : ℕ) {left exponent levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path shape.active left exponent levels frames returned)
    (baselineFits : baseline≤precision)
    (dependencyFits : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant≤shape.chunk)
    (input : Array shape rows ell) (inputWidth : Width shape rows ell precision input)
    (inputGrid : Grid shape rows ell precision denominator
      (CompactRecursiveGridBudget.bound baseline growthConstant levels (frames+2*returned)) input)
    (index : Fin (rows*(2^shape.bits*2^ell))) :
    decoded shape rows ell precision denominator
        (result stage (ButterflyIndependentGuardHeaders.reservation shape.bits precision) input) index =
      (∏ column : Fin stage.f, Networks.BinaryPhase.phase (Networks.BinaryPhase.weightPhase
        (NativeEndpointCharacterReadout.coordinates
          (NativePolynomialStageShape.stage stage ell (ButterflyIndependentGuardHeaders.reservation shape.bits precision))
          (recordIndex (ButterflyIndependentGuardHeaders.reservation shape.bits precision) index) column))) *
        decoded shape rows ell precision denominator input index := by
  rw [decoded,signed_decoded]
  · rw [phase_readout stage _ slotCount]
    rfl
  · intro coefficient
    simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using inputWidth coefficient
  · exact fun coefficient => CompactSpectatorInheritedGrid.signed_guards_from_path shape rows ell precision
      path baseline growthConstant denominator baselineFits dependencyFits input inputGrid coefficient

/-- Genuine inherited dependency Paths supply the signed guard for the physical
correction. Its denominator and the original bounded grid are unchanged. -/
theorem grid_from_path (stage : Stage shape) (precision baseline growthConstant denominator : ℕ)
    {left exponent levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path shape.active left exponent levels frames returned)
    (baselineFits : baseline≤precision)
    (dependencyFits : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant≤shape.chunk)
    (input : Array shape rows ell) (inputWidth : Width shape rows ell precision input)
    (inputGrid : Grid shape rows ell precision denominator
      (CompactRecursiveGridBudget.bound baseline growthConstant levels (frames+2*returned)) input) :
    Grid shape rows ell precision denominator
      (CompactRecursiveGridBudget.bound baseline growthConstant levels (frames+2*returned))
      (result stage (ButterflyIndependentGuardHeaders.reservation shape.bits precision) input) := by
  intro index
  rw [decoded,signed_decoded]
  · exact Networks.GaussianPrecision.bounded_I_pow_mul _ (inputGrid index)
  · intro coefficient
    simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using inputWidth coefficient
  · exact fun coefficient => CompactSpectatorInheritedGrid.signed_guards_from_path shape rows ell precision
      path baseline growthConstant denominator baselineFits dependencyFits input inputGrid coefficient

end
end IntegerMultBounds.Machine.NativeHadamardPhaseOriginal
