module

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.ToDual
public import Mathlib.Algebra.Group.Nat.Defs

/-! Integer width bounds for a possible dyadic dimension generator.
These arithmetic lemmas neither redefine executable sizes nor assert a time improvement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.CompactDyadicRootRoom

private theorem successor_power_lt {n : ℕ} (hn : 7≤n) : (n+1)^18<16*n^18 := by
  have hstep : 7*(n+1)≤8*n := by omega
  have hpow := Nat.pow_le_pow_left hstep 18
  rw [mul_pow,mul_pow] at hpow
  have hratio : (8:ℕ)^18<16*7^18 := by norm_num
  have hpos : 0<n^18 := pow_pos (by omega) _
  have hscaled := Nat.mul_lt_mul_of_pos_right hratio hpos
  have hresult : 7^18*(n+1)^18<7^18*(16*n^18) := by nlinarith only [hpow,hscaled]
  exact Nat.lt_of_mul_lt_mul_left hresult

/-- A fixed thirty-two-bit allowance pays the squared cap for the sixty-fourth root of `b^9`. -/
theorem eighteenth_power_lt (b : ℕ) : (b+1)^18<2^(4*b+32) := by
  induction b with
  | zero => norm_num
  | succ b ih =>
    by_cases hb : b<6
    · interval_cases b <;> norm_num
    · have hstep := successor_power_lt (n := b+1) (by omega)
      have hscaled := Nat.mul_lt_mul_of_pos_left ih (by decide : 0<16)
      calc
        (b+1+1)^18<16*(b+1)^18 := hstep
        _ < 16*2^(4*b+32) := hscaled
        _ = 2^(4*(b+1)+32) := by
          calc
            16*2^(4*b+32) = 2^(4*b+32)*2^4 := by ring
            _ = 2^((4*b+32)+4) := (pow_add _ _ _).symm
            _ = 2^(4*(b+1)+32) := by congr 1

/-- The actual capped-root input fits the universal eighteenth-power envelope. -/
theorem squared_ninth_cap_le (b : ℕ) : (b^9+1)^2≤(b+1)^18 := by
  have h : b^9+1≤(b+1)^9 := by
    simpa only [one_pow] using
      (pow_add_pow_le (Nat.zero_le b) (by decide : (0:ℕ)≤1) (by decide : 9≠0))
  calc
    (b^9+1)^2≤((b+1)^9)^2 := Nat.pow_le_pow_left h 2
    _ = (b+1)^18 := by rw [←pow_mul]

/-- The literal cap-square premise of the existing capped-squaring root routine. -/
theorem squared_ninth_cap_lt (b : ℕ) : (b^9+1)^2<2^(4*b+32) :=
  (squared_ninth_cap_le b).trans_lt (eighteenth_power_lt b)

/-- A sixty-fourth root of the ninth power retains the seventh-power size cap. -/
theorem seventh_power_le {d b : ℕ} (hb : 1≤b) (hroot : d^64≤b^9) : d^7≤b := by
  apply (Nat.pow_le_pow_iff_left (by decide : 64≠0)).mp
  calc
    (d^7)^64=(d^64)^7 := by rw [←pow_mul,←pow_mul]
    _ ≤ (b^9)^7 := Nat.pow_le_pow_left hroot 7
    _ = b^63 := by rw [←pow_mul]
    _ ≤ b^64 := Nat.pow_le_pow_right (by omega) (by decide)

end IntegerMultBounds.MathlibTM2.Mult.CompactDyadicRootRoom
