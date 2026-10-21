module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Total
public import IntegerMultBounds.MathlibTM2.M8.Machine.BinaryRadixRootEncoding

/-! Runtime-budget assembly for the actual radix machine and paid binary
range wrapper. This module bounds costs; machine composition is separate. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.BinaryRadixRangeRuntimeBudget
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
open ArbitraryWidthHighLayout (originalDescriptor)
open IntegerMultBounds.MathlibTM2.M8.Stage2Machine (Total.Capacity)
open IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Total (tau tau_range)
variable [Total.Capacity]

def rootDescriptor (P G B u : ℕ) := originalDescriptor P (RadixRangeDescriptors.exponent prime u) G B
def originalVolume (P G B u : ℕ) := RadixRangePadding.volume P (2^u) G B
def rootCost (P G B u : ℕ) := Stage2Machine.Total.cost (rootDescriptor P G B u)

omit [Total.Capacity] in
theorem root_volume_bound (P G B u : ℕ) :
    volume prime (rootDescriptor P G B u) ≤ (prime*prime)*originalVolume P G B u := by
  rw [rootDescriptor,BinaryRadixRootEncoding.volume_eq]
  exact BinaryRadixRangePrepare.volume_bound prime P G B u Shared50ModularControl.prime_prime.two_le

omit [Total.Capacity] in
theorem width_power_bound (u : ℕ) :
    ((max 1 (RadixRangeDescriptors.exponent prime u) : ℕ) : ℝ)^tau ≤ ((max 1 u : ℕ) : ℝ)^tau := by
  apply Real.rpow_le_rpow (Nat.cast_nonneg _)
  · exact_mod_cast max_le_max_left 1 (RadixRangeDescriptors.exponent_le prime u Shared50ModularControl.prime_prime.two_le)
  · exact tau_range.1.le

theorem root_uniform_bound : ∃ C : ℝ, 0 < C ∧ ∀ (P G B u : ℕ),
    (rootCost P G B u : ℝ) ≤ C*(originalVolume P G B u : ℝ)*((max 1 u : ℕ) : ℝ)^tau := by
  obtain ⟨C,hC,hbound⟩ := Stage2Machine.Total.uniform_bound
  have hprime : 0 < ((prime*prime : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos Shared50ModularControl.prime_prime.pos Shared50ModularControl.prime_prime.pos
  refine ⟨C*((prime*prime : ℕ) : ℝ),mul_pos hC hprime,?_⟩
  intro P G B u
  have hb := hbound (rootDescriptor P G B u)
  have hv : (volume prime (rootDescriptor P G B u) : ℝ) ≤
      ((prime*prime : ℕ) : ℝ)*(originalVolume P G B u : ℝ) := by
    exact_mod_cast root_volume_bound P G B u
  have hp := width_power_bound u
  have hrpow : 0 ≤ ((max 1 (RadixRangeDescriptors.exponent prime u) : ℕ) : ℝ)^tau :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hscaled := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hC.le) hrpow
  have hco : 0 ≤ C*(((prime*prime : ℕ) : ℝ)*(originalVolume P G B u : ℝ)) :=
    mul_nonneg hC.le (mul_nonneg hprime.le (Nat.cast_nonneg _))
  have hwidth := mul_le_mul_of_nonneg_left hp hco
  change (rootCost P G B u : ℝ) ≤ _ at hb
  change (rootCost P G B u : ℝ) ≤ _
  calc
    _ ≤ C*(volume prime (rootDescriptor P G B u) : ℝ)*
        ((max 1 (RadixRangeDescriptors.exponent prime u) : ℕ) : ℝ)^tau := hb
    _ ≤ C*(((prime*prime : ℕ) : ℝ)*(originalVolume P G B u : ℝ))*
        ((max 1 (RadixRangeDescriptors.exponent prime u) : ℕ) : ℝ)^tau := hscaled
    _ ≤ C*(((prime*prime : ℕ) : ℝ)*(originalVolume P G B u : ℝ))*
        ((max 1 u : ℕ) : ℝ)^tau := hwidth
    _ = _ := by ring

def overheadCoefficient := BinaryRadixRangePrepare.prepareConstant prime+80+54+BinaryRadixRangePrepare.finishConstant prime

def combinedCost (P G B u : ℕ) :=
  overheadCoefficient*originalVolume P G B u+rootCost P G B u+4

theorem uniform_bound : ∃ C : ℝ, 0 < C ∧ ∀ (P G B u : ℕ), 0 < P → 0 < G → 0 < B →
    (combinedCost P G B u : ℝ) ≤ C*(originalVolume P G B u : ℝ)*((max 1 u : ℕ) : ℝ)^tau := by
  obtain ⟨C,hC,hbound⟩ := root_uniform_bound
  have ho : 0 ≤ (overheadCoefficient : ℝ) := Nat.cast_nonneg _
  refine ⟨C+(overheadCoefficient : ℝ)+4,by linarith,?_⟩
  intro P G B u hP hG hB
  have hb := hbound P G B u
  have hVnat := lt_of_lt_of_le (Nat.two_pow_pos u) (BinaryRadixRangePrepare.range_le_volume P G B u hP hG hB)
  have hV : 1 ≤ (originalVolume P G B u : ℝ) := by exact_mod_cast hVnat
  have hp : 1 ≤ ((max 1 u : ℕ) : ℝ)^tau := Real.one_le_rpow
    (by exact_mod_cast le_max_left 1 u) tau_range.1.le
  have hVP : 1 ≤ (originalVolume P G B u : ℝ)*((max 1 u : ℕ) : ℝ)^tau := by nlinarith
  have hlin := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ (overheadCoefficient : ℝ)*(originalVolume P G B u : ℝ) from mul_nonneg ho (Nat.cast_nonneg _))
  unfold combinedCost
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  nlinarith only [hb,hVP,hlin]

end
end IntegerMultBounds.MathlibTM2.M8.Machine.BinaryRadixRangeRuntimeBudget
