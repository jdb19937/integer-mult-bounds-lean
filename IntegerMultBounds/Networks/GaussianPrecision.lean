module

public import IntegerMultBounds.Networks.GaussianDyadic

/-! Concrete integer numerator bounds for the actual binary translation
kernels and their column products. These bounds concern exact arithmetic;
they do not assert a tape implementation or charge arithmetic as one step. -/

@[expose] public section

namespace IntegerMultBounds.Networks.GaussianPrecision

open BinaryPhase BinaryWalsh

/-- A Gaussian dyadic grid point with both integer numerators bounded. -/
def BoundedGrid (n M : ℕ) (z : ℂ) : Prop :=
  ∃ a b : ℤ, z * (2 : ℂ) ^ n = (a : ℂ) + (b : ℂ) * Complex.I ∧
    |a| ≤ (M : ℤ) ∧ |b| ≤ (M : ℤ)

theorem bounded_zero (n M : ℕ) : BoundedGrid n M 0 := ⟨0, 0, by simp⟩

theorem bounded_int (a : ℤ) (M : ℕ) (ha : |a| ≤ (M : ℤ)) :
    BoundedGrid 0 M (a : ℂ) := ⟨a, 0, by simp [ha]⟩

theorem bound_mono {n M N : ℕ} {z : ℂ} (hMN : M ≤ N) (hz : BoundedGrid n M z) :
    BoundedGrid n N z := by
  obtain ⟨a, b, he, ha, hb⟩ := hz
  exact ⟨a, b, he, ha.trans (Int.ofNat_le.mpr hMN), hb.trans (Int.ofNat_le.mpr hMN)⟩

theorem bounded_add {n M N : ℕ} {z w : ℂ}
    (hz : BoundedGrid n M z) (hw : BoundedGrid n N w) : BoundedGrid n (M + N) (z + w) := by
  obtain ⟨a, b, he, ha, hb⟩ := hz
  obtain ⟨c, d, hf, hc, hd⟩ := hw
  refine ⟨a + c, b + d, ?_, ?_, ?_⟩
  · push_cast
    rw [add_mul, he, hf]
    ring
  · calc
      |a + c| ≤ |a| + |c| := abs_add_le a c
      _ ≤ (M + N : ℕ) := by push_cast; omega
  · calc
      |b + d| ≤ |b| + |d| := abs_add_le b d
      _ ≤ (M + N : ℕ) := by push_cast; omega

theorem bounded_neg {n M : ℕ} {z : ℂ} (hz : BoundedGrid n M z) : BoundedGrid n M (-z) := by
  obtain ⟨a, b, he, ha, hb⟩ := hz
  refine ⟨-a, -b, ?_, by simpa using ha, by simpa using hb⟩
  push_cast
  rw [neg_mul, he]
  ring

/-- Halving increases the denominator exponent but leaves the numerators intact. -/
theorem bounded_half {n M : ℕ} {z : ℂ} (hz : BoundedGrid n M z) :
    BoundedGrid (n + 1) M (z / 2) := by
  obtain ⟨a, b, he, ha, hb⟩ := hz
  refine ⟨a, b, ?_, ha, hb⟩
  rw [pow_succ, show z / 2 * (2 ^ n * 2) = z * 2 ^ n by ring, he]


end IntegerMultBounds.Networks.GaussianPrecision
