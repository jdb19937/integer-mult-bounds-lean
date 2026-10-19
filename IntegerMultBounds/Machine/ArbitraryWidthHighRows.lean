module

public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Computable least high-digit row count for arbitrary-width pieces. The
selector is an exact natural ceiling logarithm; no guessed real parameter
or uncharged physical controller is asserted by these semantic theorems. -/

@[expose] public section

namespace IntegerMultBounds.Machine.ArbitraryWidthHighRows

/-- Least number of paired high radix digits whose row count dominates D. -/
def rho (q D : ℕ) : ℕ := Nat.clog (q*q) D

def rowCount (q D : ℕ) : ℕ := q^(2*rho q D)

theorem square_base (q : ℕ) (hq : 2 ≤ q) : 1 < q*q := by nlinarith

theorem square_power (q n : ℕ) : q^(2*n) = (q*q)^n := by
  rw [pow_mul,pow_two]

/-- The selector is equivalently the first exponent accepted by the exact
integer comparison D≤q^(2n), suitable for a power-until controller. -/
theorem rho_le_iff (q D n : ℕ) (hq : 2 ≤ q) : rho q D ≤ n ↔ D ≤ q^(2*n) := by
  rw [square_power]
  exact Nat.clog_le_iff_le_pow (square_base q hq)

theorem dominates (q D : ℕ) (hq : 2 ≤ q) : D ≤ rowCount q D :=
  (rho_le_iff q D (rho q D) hq).mp le_rfl

theorem before_iff (q D n : ℕ) (hq : 2 ≤ q) : n < rho q D ↔ q^(2*n) < D := by
  rw [square_power]
  exact Nat.lt_clog_iff_pow_lt (square_base q hq)

theorem previous_lt (q D : ℕ) (hq : 2 ≤ q) (hr : 0 < rho q D) :
    q^(2*(rho q D-1)) < D :=
  (before_iff q D (rho q D-1) hq).mp (by omega)

@[simp] theorem rho_one (q : ℕ) : rho q 1 = 0 := Nat.clog_one_right _

/-- Minimal selection overshoots by less than one paired-digit factor,
including the D=1 edge case where zero high digits are selected. -/
theorem row_lt (q D : ℕ) (hq : 2 ≤ q) (hD : 0 < D) : rowCount q D < q*q*D := by
  by_cases hr : rho q D = 0
  · simp only [rowCount,hr,mul_zero,pow_zero]
    have hb := square_base q hq
    nlinarith
  · have hp := previous_lt q D hq (by omega)
    have he : rho q D = (rho q D-1)+1 := by omega
    change q^(2*rho q D) < q*q*D
    rw [square_power,he,pow_succ]
    rw [square_power] at hp
    calc
      (q*q)^(rho q D-1)*(q*q) < D*(q*q) :=
        Nat.mul_lt_mul_of_pos_right hp (Nat.mul_pos (by omega) (by omega))
      _ = q*q*D := Nat.mul_comm _ _

/-- The exact selector is the manuscript's real ceiling expression when
the target is W^k. Both natural computations therefore select the same rho. -/
theorem rho_manuscript (q W k : ℕ) (hq : 2 ≤ q) :
    rho q (W^k) = ⌈(k : ℝ)*Real.log W/(2*Real.log q)⌉₊ := by
  rw [rho,← Real.natCeil_logb_natCast]
  congr 1
  rw [Real.logb]
  simp only [Nat.cast_pow,Real.log_pow,Nat.cast_mul]
  rw [Real.log_mul (by exact_mod_cast (show q ≠ 0 by omega))
    (by exact_mod_cast (show q ≠ 0 by omega))]
  congr 1
  ring

end IntegerMultBounds.Machine.ArbitraryWidthHighRows
