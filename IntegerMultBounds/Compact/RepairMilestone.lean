module

public import IntegerMultBounds.Compact.RepairPipeline

/-! A common dyadic packed-control instance has exact early and late repaired
outputs, the manuscript exceptional fraction, and the written three-volume
repair allowance. Both guarantees use the same control digits, density
parameter and certified record/address cost assumptions. -/

@[expose] public section
namespace IntegerMultBounds.Compact
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Early exceptional extraction has the same certified dyadic cutoff as the
late branch, on the actual early address space and extraction pipeline. -/
theorem early_extracted_le (densityParameter : ℝ) (digitCount radixExponent recordExponent : ℕ)
    (parameterLarge : 1 ≤ densityParameter) (digitsFit : (digitCount : ℝ) ≤ densityParameter)
    (parameterFits : densityParameter ≤ (2 : ℝ)^radixExponent)
    (recordFits : 8*radixExponent+16 ≤ recordExponent) {addressCount : ℕ}
    (addressOrder : EarlyAddress ((2 : ℤ)^(4*radixExponent+6)) ((2 : ℤ)^(recordExponent-1)) digitCount ≃ Fin addressCount)
    (actual ideal : Equiv.Perm (EarlyAddress ((2 : ℤ)^(4*radixExponent+6)) ((2 : ℤ)^(recordExponent-1)) digitCount))
    (records : EarlyAddress ((2 : ℤ)^(4*radixExponent+6)) ((2 : ℤ)^(recordExponent-1)) digitCount → List Bool) :
    ((extracted addressOrder actual ideal
      (fun address => ¬earlyGood ((2 : ℤ)^(4*radixExponent+6)) ((2 : ℤ)^(recordExponent-1)) digitCount address)
      records).length : ℝ) ≤ min 1 (5/(128*densityParameter^3))*
        Nat.card (EarlyAddress ((2 : ℤ)^(4*radixExponent+6)) ((2 : ℤ)^(recordExponent-1)) digitCount) := by
  have densityBound := (dyadic_actual_repair_density densityParameter digitCount radixExponent recordExponent
    parameterLarge digitsFit parameterFits recordFits).1
  have addressPositive : 0 < (Nat.card
      (EarlyAddress ((2 : ℤ)^(4*radixExponent+6)) ((2 : ℤ)^(recordExponent-1)) digitCount) : ℝ) := by
    rw [early_total_real _ _ (by positivity) (by positivity)]
    positivity
  rw [extracted_length,card_bad_eq_fraction _ addressPositive]
  gcongr

/-- The written logical-volume cost charges the original scan, descriptor
setup and sorting/reinsertion work on exactly the extracted records. -/
def repairWork {Address : Type*} [Fintype Address] {addressCount : ℕ}
    (addressOrder : Address ≃ Fin addressCount) (actual ideal : Equiv.Perm Address)
    (good : Address → Prop) [DecidablePred good] (records : Address → List Bool)
    (recordCost addressCost : ℝ) : ℝ :=
  Nat.card Address*recordCost+Nat.card Address*addressCost^3+
    ((extracted addressOrder actual ideal (fun address => ¬good address) records).length : ℝ)*
      addressCost*(recordCost+addressCost)

/-- One actual packed repair instance, including its exact stream endpoint,
exceptional record bound and complete written logical-volume allowance. -/
structure RepairPipelineGuarantee {Address : Type*} [Fintype Address] {addressCount : ℕ}
    (addressOrder : Address ≃ Fin addressCount) (actual ideal : Equiv.Perm Address)
    (good : Address → Prop) [DecidablePred good] (addressBits : ℕ)
    (records : Address → List Bool) (densityParameter recordCost addressCost : ℝ) : Prop where
  exact_output : pipeline addressOrder actual ideal (fun address => ¬good address) addressBits records=
    stream addressOrder (fun address => ¬good address) (records ∘ ideal.symm)
  density : badFraction good ≤ 5/(128*densityParameter^3)
  extracted_count : ((extracted addressOrder actual ideal (fun address => ¬good address) records).length : ℝ) ≤
    5/(128*densityParameter^3)*Nat.card Address
  repair_cost : repairWork addressOrder actual ideal good records recordCost addressCost ≤
    3*(Nat.card Address*recordCost)

/-- For the same dyadic radices and control digits, both genuine packed
programs repair to their ideal toggles, extract at most the manuscript
exceptional fraction, and satisfy the certified three-logical-volume bound. -/
theorem repair_pipeline_exact_density
    (densityParameter : ℝ) (radixExponent recordExponent addressBits : ℕ) (controlDigits : List ℤ)
    (parameterLarge : 1 ≤ densityParameter) (digitsFit : (controlDigits.length : ℝ) ≤ densityParameter)
    (parameterFits : densityParameter ≤ (2 : ℝ)^radixExponent)
    (recordFits : 8*radixExponent+16 ≤ recordExponent) (digitsBinary : Bits controlDigits)
    {earlyCount lateCount : ℕ}
    (earlyOrder : EarlyAddress ((2 : ℤ)^(4*radixExponent+6)) ((2 : ℤ)^(recordExponent-1)) controlDigits.length ≃ Fin earlyCount)
    (lateOrder : LateAddress ((2 : ℤ)^(4*radixExponent+6)) ((2 : ℤ)^(recordExponent-1)) controlDigits.length ≃ Fin lateCount)
    (earlyRanksFit : earlyCount ≤ 2^addressBits) (lateRanksFit : lateCount ≤ 2^addressBits)
    (earlyRecords : EarlyAddress ((2 : ℤ)^(4*radixExponent+6)) ((2 : ℤ)^(recordExponent-1)) controlDigits.length → List Bool)
    (lateRecords : LateAddress ((2 : ℤ)^(4*radixExponent+6)) ((2 : ℤ)^(recordExponent-1)) controlDigits.length → List Bool)
    (recordCost addressCost : ℝ) (recordNonnegative : 0 ≤ recordCost) (addressNonnegative : 0 ≤ addressCost)
    (addressFitsRecord : addressCost ≤ recordCost) (setupFitsRecord : addressCost^3 ≤ recordCost)
    (exceptionalCostFits : (5/(128*densityParameter^3))*addressCost ≤ 1/2) :
    let radix := (2 : ℤ)^(4*radixExponent+6)
    let halfRecordRadix := (2 : ℤ)^(recordExponent-1)
    let positiveHalf : 0 < halfRecordRadix := by positivity
    let actualEarly := packedEarlyPerm (2*halfRecordRadix) radix (by positivity) (by positivity) controlDigits
    let actualLate := packedLatePerm (2*halfRecordRadix) radix (by positivity) (by positivity) controlDigits
    let idealEarly := earlyIdeal radix halfRecordRadix positiveHalf controlDigits digitsBinary
    let idealLate := lateIdeal radix halfRecordRadix positiveHalf controlDigits digitsBinary
    RepairPipelineGuarantee earlyOrder actualEarly idealEarly
      (earlyGood radix halfRecordRadix controlDigits.length) addressBits earlyRecords densityParameter recordCost addressCost ∧
    RepairPipelineGuarantee lateOrder actualLate idealLate
      (lateGood radix halfRecordRadix controlDigits.length) addressBits lateRecords densityParameter recordCost addressCost := by
  dsimp only
  let radix := (2 : ℤ)^(4*radixExponent+6)
  let halfRecordRadix := (2 : ℤ)^(recordExponent-1)
  have radixAtLeastOne : 1 ≤ radix := one_le_pow₀ (by norm_num)
  have positiveHalf : 0 < halfRecordRadix := by dsimp only [halfRecordRadix];positivity
  have parameterPositive : 0 < densityParameter := by linarith
  have densityNonnegative : 0 ≤ 5/(128*densityParameter^3) := by positivity
  have densities := dyadic_actual_repair_density densityParameter controlDigits.length radixExponent recordExponent
    parameterLarge digitsFit parameterFits recordFits
  have earlyDensity : badFraction (earlyGood radix halfRecordRadix controlDigits.length) ≤ 5/(128*densityParameter^3) :=
    densities.1.trans (min_le_right _ _)
  have lateDensity : badFraction (lateGood radix halfRecordRadix controlDigits.length) ≤ 5/(128*densityParameter^3) :=
    densities.2.trans (min_le_right _ _)
  have earlyPositive : 0 < (Nat.card (EarlyAddress radix halfRecordRadix controlDigits.length) : ℝ) := by
    rw [early_total_real _ _ (by omega) positiveHalf]
    positivity
  have latePositive : 0 < (Nat.card (LateAddress radix halfRecordRadix controlDigits.length) : ℝ) := by
    rw [late_total_real _ _ (by omega) positiveHalf]
    positivity
  have earlyExtracted := early_extracted_le densityParameter controlDigits.length radixExponent recordExponent
    parameterLarge digitsFit parameterFits recordFits earlyOrder
    (packedEarlyPerm (2*halfRecordRadix) radix (by positivity) (by omega) controlDigits)
    (earlyIdeal radix halfRecordRadix positiveHalf controlDigits digitsBinary) earlyRecords
  have lateExtracted := late_extracted_le densityParameter controlDigits.length radixExponent recordExponent
    parameterLarge digitsFit parameterFits recordFits lateOrder
    (packedLatePerm (2*halfRecordRadix) radix (by positivity) (by omega) controlDigits)
    (lateIdeal radix halfRecordRadix positiveHalf controlDigits digitsBinary) lateRecords
  have densityFactor : min 1 (5/(128*densityParameter^3)) ≤ 5/(128*densityParameter^3) := min_le_right _ _
  refine ⟨⟨?_,earlyDensity,?_,?_⟩,⟨?_,lateDensity,?_,?_⟩⟩
  · exact early_pipeline_exact radix halfRecordRadix radixAtLeastOne positiveHalf controlDigits digitsBinary
      earlyOrder addressBits earlyRanksFit earlyRecords
  · exact earlyExtracted.trans (mul_le_mul_of_nonneg_right densityFactor earlyPositive.le)
  · exact pipeline_cost_le earlyOrder _ _ (earlyGood radix halfRecordRadix controlDigits.length) earlyRecords
      recordCost addressCost (5/(128*densityParameter^3)) earlyPositive recordNonnegative addressNonnegative
      addressFitsRecord setupFitsRecord densityNonnegative earlyDensity exceptionalCostFits
  · exact late_pipeline_exact radix halfRecordRadix radixAtLeastOne positiveHalf controlDigits digitsBinary
      lateOrder addressBits lateRanksFit lateRecords
  · exact lateExtracted.trans (mul_le_mul_of_nonneg_right densityFactor latePositive.le)
  · exact pipeline_cost_le lateOrder _ _ (lateGood radix halfRecordRadix controlDigits.length) lateRecords
      recordCost addressCost (5/(128*densityParameter^3)) latePositive recordNonnegative addressNonnegative
      addressFitsRecord setupFitsRecord densityNonnegative lateDensity exceptionalCostFits

end
end IntegerMultBounds.Compact
