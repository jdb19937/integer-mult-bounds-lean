module

public import IntegerMultBounds.MathlibTM2.Fast.DistWidth

/-!
# Compatibility of a wider parameter table

The candidate width adds sixteen bits to the current allocation. Its distribution compatibility
is proved separately, without changing the allocated width or the current dimension.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds.MathlibTM2.Mult
open IntegerMultBounds.MathlibTM2.Mult.Sizes

/-- Candidate parameter-table width with room for the dyadic dimension search. -/
def compactParameterWidth (n : ℕ) : ℕ := 4 * Nat.size n + 32

/-- A dimension-independent width comparison: only the two smallest precision values require
the stronger lower bound on the long axis. -/
theorem compactParameterWidth_le_core {b L r w a : ℕ}
    (hb : 1 ≤ b) (hL : L ≤ b + 1) (hw : 6 * b + 7 ≤ w)
    (hr : 2 ≤ r) (hsmall : b ≤ 2 → 4 ≤ r) :
    4 * L + 32 ≤ r * w + (a ^ 2 + a + 4) := by
  by_cases h : b ≤ 2
  · have h4 := hsmall h
    have := Nat.mul_le_mul_right w h4
    nlinarith
  · have := Nat.mul_le_mul_right w hr
    nlinarith

/-- The current dimension gives a long axis of at least four at precision one or two. -/
theorem compactParameterWidth_small_r {n : ℕ} (hn : 2 ≤ n) (hb : b n ≤ 2) :
    4 ≤ r n := by
  have hpow : 2 ^ b n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) hb
  have hn4 := (le_two_pow_b n).trans hpow
  norm_num at hn4
  interval_cases n <;> decide

/-- The candidate width fits the actual distribution long-axis word for every input `n ≥ 2`. -/
theorem compactParameterWidth_le_dsWL {n : ℕ} (hn : 2 ≤ n) :
    compactParameterWidth n ≤ dsWL n (dsW n) := by
  have hw : 6 * b n + 7 ≤ dsW n := by
    have : 4 ≤ Chirp.chirpGuard (d n) := by unfold Chirp.chirpGuard; omega
    unfold dsW p
    omega
  exact compactParameterWidth_le_core (one_le_b hn) pm_size_le hw (ds_two_le_r hn)
    (compactParameterWidth_small_r hn)

/-- Uniform linear bound, usable in table-machine cost estimates. -/
theorem compactParameterWidth_le (n : ℕ) : compactParameterWidth n ≤ 36 * (b n + 1) := by
  have := pm_size_le (n := n)
  unfold compactParameterWidth
  omega

end IntegerMultBounds.MathlibTM2.Fast.TableVM
