module

public import IntegerMultBounds.Machine.ActivePrefixStageNativePolynomialWord
public import IntegerMultBounds.Machine.ActivePrefixStageNativePairInverse
public import IntegerMultBounds.Machine.CompactNativeTensorPhaseCoordinates

/-! One literal complex-edge basis word transports actual serialized polynomial
coefficients to its native reached row. The all-axis phase at that same row,
followed by the reverse word, decodes at the original row to the full original
edge tensor phase. Coordinate action and exact row restoration refer to this
same word and coefficient bank. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactNativeStagePhaseCoordinates
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageTripleWords (count)
open ActivePrefixStageNativePolynomial (rows symbols)
open ActivePrefixStageNativePolynomialWord (word word_width)
open ActivePrefixStageNativePairCoordinates (run start)
open ActivePrefixStageNativePairSchedule (result)
open ButterflyStreamData (Coefficient)
open UnitPhaseStreamEndpoint (components)
open Networks Networks.ComplexPhaseRowSchedule
variable {shape : Shape} {coefficientCount : ℕ}

/-- The actual signed coefficient rotation selected by the all-axis scanner. -/
def rotate (phase : Fin 4) (coefficient : Coefficient) : Coefficient :=
  (UnitPhaseNumerator.words phase 0 (components coefficient),
    UnitPhaseNumerator.words phase 1 (components coefficient))

/-- Computed forward basis, reached-row phase and reverse basis on the same
polynomial array; no coordinate interchange or coefficient callback is assumed. -/
def phasedBasisResult (inputs : Inputs shape) (slotsCorrect : inputs.stage.slots=25^3)
    (edge : Edge) (edgePositive : 0 < dimension edge)
    (coefficients : Fin (count inputs) → Fin coefficientCount → Coefficient) :=
  let basisWord := CompactComplexPhasePhysical.word inputs slotsCorrect edge
  word inputs basisWord.reverse (fun reachedRow polynomialIndex =>
    rotate (CompactNativeTensorPhaseCoordinates.phase inputs slotsCorrect edge edgePositive reachedRow)
      (word inputs basisWord coefficients reachedRow polynomialIndex))

/-- A true common stage/phase endpoint: the SAME literal word has its binary
coordinate action and exact serialized-row transport, reverses back to the
original row bank, and computes the original complex25 edge tensor phase on
every coefficient after that physical forward/local/reverse chronology. -/
theorem stage_and_phase (inputs : Inputs shape) (slotsCorrect : inputs.stage.slots=25^3)
    (edge : Edge) (edgePositive : 0 < dimension edge)
    (coefficients : Fin (count inputs) → Fin coefficientCount → Coefficient)
    (signedWidth denominator : ℕ)
    (coefficientWidths : ∀ row polynomialIndex,
      (coefficients row polynomialIndex).1.length=signedWidth+1 ∧
      (coefficients row polynomialIndex).2.length=signedWidth+1)
    (coefficientGuards : ∀ row polynomialIndex (component : Fin 2),
      |ButterflySigned.signedValue signedWidth (components (coefficients row polynomialIndex) component.val)|<
        (2^signedWidth : ℕ)) :
    let basisWord := CompactComplexPhasePhysical.word inputs slotsCorrect edge
    let sourceRows := rows inputs coefficients coefficientWidths
    (∀ originalRow,ActivePrefixStageRuntimeOrdinal.rawCoordinates inputs.stage (start inputs (ActivePrefixStageNativePairCoordinates.run inputs basisWord originalRow))=
      BinaryRowColumns.run basisWord (ActivePrefixStageRuntimeOrdinal.rawCoordinates inputs.stage (start inputs originalRow))) ∧
    (∀ originalRow payloadPosition,
      result inputs basisWord sourceRows (ActivePrefixStageNativePairCoordinates.run inputs basisWord originalRow) payloadPosition=sourceRows originalRow payloadPosition) ∧
    result inputs basisWord.reverse (result inputs basisWord sourceRows)=sourceRows ∧
    (∀ originalRow polynomialIndex,
      ButterflySigned.complexValue
        (ButterflySigned.signedValue signedWidth
          (phasedBasisResult inputs slotsCorrect edge edgePositive coefficients originalRow polynomialIndex).1)
        (ButterflySigned.signedValue signedWidth
          (phasedBasisResult inputs slotsCorrect edge edgePositive coefficients originalRow polynomialIndex).2) denominator=
      (∏ axis : Fin inputs.stage.f,BinaryPhase.phase
        (CompactAllAxisPhaseReadout.delta inputs slotsCorrect edge (start inputs originalRow) axis))*
        ButterflySigned.complexValue (ButterflySigned.signedValue signedWidth (coefficients originalRow polynomialIndex).1)
          (ButterflySigned.signedValue signedWidth (coefficients originalRow polynomialIndex).2) denominator) := by
  dsimp only
  let basisWord := CompactComplexPhasePhysical.word inputs slotsCorrect edge
  refine ⟨ActivePrefixStageNativePairCoordinates.run_coordinates inputs basisWord,
    ActivePrefixStageNativePairCoordinates.run_entry inputs basisWord (rows inputs coefficients coefficientWidths),
    ActivePrefixStageNativePairInverse.reverse_restores inputs basisWord (rows inputs coefficients coefficientWidths),?_⟩
  intro originalRow polynomialIndex
  have outputCoefficient : phasedBasisResult inputs slotsCorrect edge edgePositive coefficients originalRow polynomialIndex=
      rotate (CompactNativeTensorPhaseCoordinates.phase inputs slotsCorrect edge edgePositive (ActivePrefixStageNativePairCoordinates.run inputs basisWord originalRow))
        (coefficients originalRow polynomialIndex) := by
    exact ActivePrefixStageNativePolynomialWord.conjugated_entry inputs basisWord
      (fun reachedRow rowCoefficients polynomialIndex =>
        rotate (CompactNativeTensorPhaseCoordinates.phase inputs slotsCorrect edge edgePositive reachedRow)
          (rowCoefficients polynomialIndex)) coefficients originalRow polynomialIndex
  rw [outputCoefficient]
  have componentWidths : ∀ component,
      (components (coefficients originalRow polynomialIndex) component).length=signedWidth+1 := by
    intro component
    by_cases realComponent : component=0
    · simpa only [components,realComponent,ite_true] using (coefficientWidths originalRow polynomialIndex).1
    · simpa only [components,ite_eq_right realComponent] using (coefficientWidths originalRow polynomialIndex).2
  have phaseValue := CompactNativeTensorPhaseCoordinates.coefficient_phase inputs slotsCorrect edge edgePositive originalRow
    (components (coefficients originalRow polynomialIndex)) signedWidth denominator componentWidths
    (coefficientGuards originalRow polynomialIndex)
  simpa only [rotate,components,ite_true,show ¬((1 : ℕ)=0) by decide,ite_false] using phaseValue

end
end IntegerMultBounds.Machine.CompactNativeStagePhaseCoordinates
