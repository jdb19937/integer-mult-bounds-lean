module

public import IntegerMultBounds.Networks.GaussianHadamardBridge
public import IntegerMultBounds.Machine.CompactComplexRecursiveGeometry

/-! Native power-of-arity widths are one modulo eight. Their exact Gaussian
normalization is one fixed multiplication by (1-I), followed by a denominator
increase; there is no repeated per-coordinate scaling or runtime unit phase. -/

@[expose] public section
namespace IntegerMultBounds.Machine.NativeHadamardNormalizationFactor
noncomputable section
open Networks.GaussianHadamardBridge (normalization)
open CompactComplexRecursiveGeometry (arity)

def denominatorIncrease (selectedCount : ℕ) : ℕ := (selectedCount+1)/2

private theorem normalization_square : normalization^2=-Complex.I/2 := by
  unfold normalization
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem normalization_eighth : normalization^8=(1/16 : ℂ) := by
  calc
    _=(normalization^2)^4 := by rw [←pow_mul]
    _=(-Complex.I/2)^4 := by rw [normalization_square]
    _=_ := by norm_num [div_pow,neg_pow,Complex.I_pow_four]

theorem normalization_of_mod_eight (selectedCount : ℕ) (nativeResidue : selectedCount%8=1) :
    normalization^selectedCount=(1-Complex.I)/(2 : ℂ)^denominatorIncrease selectedCount := by
  have countEquation : selectedCount=8*(selectedCount/8)+1 := by omega
  have increaseEquation : denominatorIncrease selectedCount=4*(selectedCount/8)+1 := by
    unfold denominatorIncrease
    omega
  rw [countEquation,pow_add,pow_mul,normalization_eighth,pow_one]
  rw [←countEquation,increaseEquation,pow_add,pow_mul]
  unfold normalization
  norm_num
  rw [div_pow]
  field_simp
  simp

theorem native_residue (exponent : ℕ) : arity^exponent%8=1 := by
  have arityResidue : arity%8=1 := by decide
  rw [Nat.pow_mod,arityResidue]
  simp

/-- Exact normalization selected by the original native visit width, including
exponent zero. Only one fixed Gaussian numerator pass is needed. -/
theorem native_normalization (exponent : ℕ) :
    normalization^(arity^exponent)=(1-Complex.I)/(2 : ℂ)^denominatorIncrease (arity^exponent) :=
  normalization_of_mod_eight _ (native_residue exponent)

theorem increase_positive (exponent : ℕ) : 0<denominatorIncrease (arity^exponent) := by
  have countPositive : 0<arity^exponent := pow_pos (by decide) _
  unfold denominatorIncrease
  omega

theorem increase_le_count (selectedCount : ℕ) (countPositive : 0<selectedCount) :
    denominatorIncrease selectedCount≤selectedCount := by unfold denominatorIncrease; omega

end
end IntegerMultBounds.Machine.NativeHadamardNormalizationFactor
