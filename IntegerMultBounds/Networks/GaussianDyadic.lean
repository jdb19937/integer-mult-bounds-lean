module

public import IntegerMultBounds.Networks.BinaryColumns

/-! Exact arithmetic closure for the binary phase interfaces. A grid at precision
`n` consists of Gaussian integers divided by `2^n`. Each literal translation
kernel increases precision by at most one, and a whole-column factor by at most
the number of columns. These are arithmetic bounds, not tape runtimes. -/

@[expose] public section

namespace IntegerMultBounds.Networks.GaussianDyadic

open BinaryPhase BinaryWalsh

/-- A complex number with two integer numerators and a common binary scale. -/
def Grid (n : ℕ) (z : ℂ) : Prop :=
  ∃ a b : ℤ, z * (2 : ℂ) ^ n = (a : ℂ) + (b : ℂ) * Complex.I

theorem grid_zero (n : ℕ) : Grid n 0 := ⟨0, 0, by simp⟩

theorem grid_int (a : ℤ) : Grid 0 (a : ℂ) := ⟨a, 0, by simp⟩

theorem grid_I : Grid 0 Complex.I := ⟨0, 1, by simp⟩

theorem grid_add {n : ℕ} {z w : ℂ} (hz : Grid n z) (hw : Grid n w) : Grid n (z + w) := by
  obtain ⟨a, b, ha⟩ := hz
  obtain ⟨c, d, hc⟩ := hw
  refine ⟨a + c, b + d, ?_⟩
  push_cast
  rw [add_mul, ha, hc]
  ring

theorem grid_neg {n : ℕ} {z : ℂ} (hz : Grid n z) : Grid n (-z) := by
  obtain ⟨a, b, ha⟩ := hz
  refine ⟨-a, -b, ?_⟩
  push_cast
  rw [neg_mul, ha]
  ring

theorem grid_mul {n m : ℕ} {z w : ℂ} (hz : Grid n z) (hw : Grid m w) :
    Grid (n + m) (z * w) := by
  obtain ⟨a, b, ha⟩ := hz
  obtain ⟨c, d, hc⟩ := hw
  refine ⟨a * c - b * d, a * d + b * c, ?_⟩
  rw [pow_add, show z * w * (2 ^ n * 2 ^ m) = (z * 2 ^ n) * (w * 2 ^ m) by ring, ha, hc]
  push_cast
  calc
    _ = (a : ℂ) * c + ((a : ℂ) * d + (b : ℂ) * c) * Complex.I +
        (b : ℂ) * d * Complex.I ^ 2 := by ring
    _ = _ := by rw [Complex.I_sq]; ring

theorem grid_half {n : ℕ} {z : ℂ} (hz : Grid n z) : Grid (n + 1) (z / 2) := by
  obtain ⟨a, b, ha⟩ := hz
  refine ⟨a, b, ?_⟩
  rw [pow_succ, show z / 2 * (2 ^ n * 2) = z * 2 ^ n by ring, ha]

end IntegerMultBounds.Networks.GaussianDyadic
