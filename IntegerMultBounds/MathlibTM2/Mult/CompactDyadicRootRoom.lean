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

private theorem successor_fortieth_le {n : ℕ} (hn : 64≤n) : (n+1)^40≤2*n^40 := by
  have hpow := Nat.pow_le_pow_left (show 64*(n+1)≤65*n by omega) 40
  rw [mul_pow,mul_pow] at hpow
  have hratio : 65^40*n^40≤64^40*(2*n^40) := by
    calc 65^40*n^40≤(64^40*2)*n^40 := Nat.mul_le_mul_right _ (by norm_num)
      _ = 64^40*(2*n^40) := by ring
  exact Nat.le_of_mul_le_mul_left (hpow.trans hratio) (by norm_num)

set_option exponentiation.threshold 512 in
/-- The fortieth power is below the exponential from `512` on. -/
theorem fortieth_power_lt {n : ℕ} (hn : 512≤n) : n^40<2^n := by
  induction n, hn using Nat.le_induction with
  | base =>
    calc (512:ℕ)^40 = 2^360 := by rw [show (512:ℕ) = 2^9 by norm_num, ←pow_mul]
      _ < 2^512 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  | succ n hn ih =>
    calc (n+1)^40≤2*n^40 := successor_fortieth_le (by omega)
      _ < 2*2^n := by omega
      _ = 2^(n+1) := by rw [pow_succ]; ring

/-- The cap-square premise of the capped-squaring root routine at the thirty-first power,
from `512 ≤ b`. -/
theorem squared_thirty_first_cap_lt {b : ℕ} (hb : 512≤b) : (b^31+1)^2<2^(4*b+32) := by
  have h1 : b^31+1≤2*b^31 := by
    have : 1≤b^31 := Nat.one_le_pow _ _ (by omega)
    omega
  have h2 : (b^40)^4<(2^b)^4 := Nat.pow_lt_pow_left (fortieth_power_lt hb) (by norm_num)
  have h3 : b^62≤(b^40)^4 := by
    rw [←pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by norm_num)
  calc (b^31+1)^2≤(2*b^31)^2 := Nat.pow_le_pow_left h1 2
    _ = 4*b^62 := by ring
    _ < 4*(2^b)^4 := by omega
    _ = 2^(4*b+2) := by ring
    _ ≤ 2^(4*b+32) := Nat.pow_le_pow_right (by norm_num) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.CompactDyadicRootRoom
