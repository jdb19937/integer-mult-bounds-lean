module

public import IntegerMultBounds.MathlibTM2.Routing.BlockExchange
public import IntegerMultBounds.MathlibTM2.Node.CompactSwapPass

/-!
# Interval exchanges are the existing physical digit interchanges

The bit action of the actual rank map is the explicit coordinate exchange.
All outer row bits and intervening coordinates are preserved.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits

def blockExchangeLen (a b w : ℕ) : Fin 4 → ℕ := ![a, w, b - (a + w), w]

theorem blockExchange_off (a b w : ℕ) (hab : a + w ≤ b) :
    fieldOff (blockExchangeLen a b w) 1 = a ∧
      fieldOff (blockExchangeLen a b w) 3 = b := by
  have h0 := fieldOff_zero (blockExchangeLen a b w) 0 rfl
  have h1 := fieldOff_succ (blockExchangeLen a b w) 0 (by decide)
  have h2 := fieldOff_succ (blockExchangeLen a b w) 1 (by decide)
  have h3 := fieldOff_succ (blockExchangeLen a b w) 2 (by decide)
  simp_all [blockExchangeLen]

def blockExchangeIdx (a b w i : ℕ) : ℕ :=
  swapIdx (blockExchangeLen a b w) 1 3 i

private theorem digit_bit (a b w i : ℕ) (f : Fin 4) (r : ℕ)
    (hr : r < blockExchangeLen a b w f) :
    (digit (blockExchangeLen a b w) f i).testBit r =
      i.testBit (fieldOff (blockExchangeLen a b w) f + r) := by
  simp [digit, Nat.testBit_mod_two_pow, hr, Nat.testBit_div_two_pow, Nat.add_comm]

theorem blockExchangeIdx_bit (a b w : ℕ) (hab : a + w ≤ b) (i q : ℕ) :
    (blockExchangeIdx a b w i).testBit q = i.testBit (blockExchange a b w q) := by
  obtain ⟨ho1, ho3⟩ := blockExchange_off a b w hab
  simp only [blockExchangeIdx, swapIdx, testBit_setDigit, ho1, ho3]
  by_cases hb : b ≤ q ∧ q < b + w
  · have hq : q - b < blockExchangeLen a b w 1 := by change q - b < w; omega
    have hd := digit_bit a b w i 1 (q - b) hq
    rw [ho1] at hd
    have ha : ¬(a ≤ q ∧ q < a + w) := by omega
    simpa [blockExchangeLen, hb, ha, blockExchange] using hd
  · by_cases ha : a ≤ q ∧ q < a + w
    · have hq : q - a < blockExchangeLen a b w 3 := by change q - a < w; omega
      have hd := digit_bit a b w i 3 (q - a) hq
      rw [ho3] at hd
      simpa [blockExchangeLen, hb, ha, blockExchange] using hd
    · simp [blockExchangeLen, hb, ha, blockExchange]

theorem blockExchangeIdx_involutive (a b w : ℕ) (hab : a + w ≤ b) :
    Function.Involutive (blockExchangeIdx a b w) := by
  intro i
  apply Nat.eq_of_testBit_eq
  intro q
  rw [blockExchangeIdx_bit a b w hab, blockExchangeIdx_bit a b w hab,
    blockExchange_involutive a b w hab]

theorem blockExchangeIdx_div (n a b w : ℕ) (hab : a + w ≤ b) (hb : b + w ≤ n)
    (i : ℕ) : blockExchangeIdx a b w i / 2 ^ n = i / 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro q
  simp only [Nat.testBit_div_two_pow, blockExchangeIdx_bit a b w hab]
  rw [blockExchange_outside a b w (q + n) (by omega) (by omega)]

theorem blockExchangeIdx_lt (n a b w : ℕ) (hab : a + w ≤ b) (hb : b + w ≤ n)
    {R i : ℕ} (hi : i < R * 2 ^ n) : blockExchangeIdx a b w i < R * 2 ^ n := by
  have hd := blockExchangeIdx_div n a b w hab hb i
  have h := (Nat.div_lt_iff_lt_mul (show 0 < 2 ^ n by positivity)).mpr hi
  rw [← hd] at h
  exact (Nat.div_lt_iff_lt_mul (by positivity)).mp h

def blockExchangeRank (n a b w R : ℕ) (hab : a + w ≤ b) (hb : b + w ≤ n) :
    Equiv.Perm (Fin (R * 2 ^ n)) where
  toFun i := ⟨blockExchangeIdx a b w i.val, blockExchangeIdx_lt n a b w hab hb i.isLt⟩
  invFun i := ⟨blockExchangeIdx a b w i.val, blockExchangeIdx_lt n a b w hab hb i.isLt⟩
  left_inv i := Fin.ext (blockExchangeIdx_involutive a b w hab i.val)
  right_inv i := Fin.ext (blockExchangeIdx_involutive a b w hab i.val)

/-- The host rank permutation implements the proved coordinate placement. -/
theorem blockExchangeRank_bit (n a b w R : ℕ) (hab : a + w ≤ b) (hb : b + w ≤ n)
    (i : Fin (R * 2 ^ n)) (q : Fin n) :
    (blockExchangeRank n a b w R hab hb i).val.testBit q.val =
      i.val.testBit (blockExchangePerm n a b w hab hb q).val :=
  blockExchangeIdx_bit a b w hab i.val q.val

end IntegerMultBounds.MathlibTM2.Routing
