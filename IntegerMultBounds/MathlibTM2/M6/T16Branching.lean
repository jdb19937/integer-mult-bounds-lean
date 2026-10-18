module

public import IntegerMultBounds.MathlibTM2.M6.T16Node
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The branching bound of the T16 node with rank-one children

The fitted T16 program makes `F = 1,041,408` rank-one child calls (`T16Node.fitted_children`) on
`W = 14,336` data families of width `m = 73`, so `F / W = 72.64… < 73`. With every child of rank
one, the uniform branching recurrence of the layer machine applies with the exponent
`σ = 1 - 1/875`, just below the limit `log_73 (F / W) = 1 - 1.143088 · 10^-3`.

* `branching_cert`: the integer certificate `F^875 < 73^874 · W^875`.
* `branching_lt`: `F / W < 73^σ`, the counterpart of `Cost.br_branching`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M6.T16Branching

/-- The complex branching exponent of the T16 node with rank-one children. -/
noncomputable def sigma16 : ℝ := 1 - 1 / 875

theorem sigma16_lt_one : sigma16 < 1 := by norm_num [sigma16]

theorem sigma16_pos : 0 < sigma16 := by norm_num [sigma16]

/-- The integer certificate: `F^875 < 73^874 · W^875`. -/
theorem branching_cert : (1041408 : ℕ) ^ 875 < 73 ^ 874 * 14336 ^ 875 := by decide +kernel

/-- **The T16 branching bound**: `F / W < 73^σ` with `σ = 1 - 1/875`. -/
theorem branching_lt : ((1041408 : ℝ) / 14336) < (73 : ℝ) ^ sigma16 := by
  have hcert : ((1041408 : ℝ) / 14336) ^ 875 < (73 : ℝ) ^ 874 := by
    rw [div_pow, div_lt_iff₀ (by positivity)]
    exact_mod_cast branching_cert
  calc (1041408 : ℝ) / 14336 = (((1041408 : ℝ) / 14336) ^ 875) ^ ((875 : ℕ) : ℝ)⁻¹ := by
        rw [Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]
    _ < ((73 : ℝ) ^ 874) ^ ((875 : ℕ) : ℝ)⁻¹ :=
        Real.rpow_lt_rpow (by positivity) hcert (by positivity)
    _ = (73 : ℝ) ^ sigma16 := by
        rw [← Real.rpow_natCast (73 : ℝ) 874, ← Real.rpow_mul (by norm_num)]
        congr 1
        norm_num [sigma16]

end IntegerMultBounds.MathlibTM2.M6.T16Branching
