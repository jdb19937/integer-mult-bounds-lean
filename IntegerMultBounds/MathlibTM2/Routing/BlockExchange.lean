module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Data.Nat.Basic

/-!
# Coordinate action of an equal-width interval interchange

The exchange is explicit on every coordinate, including the intervening gap and
outer spectators. This is the coordinate permutation to connect to the existing
rectangular-interchange execution theorem, not an unpriced routing primitive.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

def blockExchange (a b w i : ℕ) : ℕ :=
  if a ≤ i ∧ i < a + w then b + (i - a)
  else if b ≤ i ∧ i < b + w then a + (i - b) else i

theorem blockExchange_left (a b w r : ℕ) (hab : a + w ≤ b) (hr : r < w) :
    blockExchange a b w (a + r) = b + r := by
  simp only [blockExchange]
  split_ifs <;> omega

theorem blockExchange_right (a b w r : ℕ) (hab : a + w ≤ b) (hr : r < w) :
    blockExchange a b w (b + r) = a + r := by
  simp only [blockExchange]
  split_ifs <;> omega

theorem blockExchange_outside (a b w i : ℕ)
    (ha : ¬ (a ≤ i ∧ i < a + w)) (hb : ¬ (b ≤ i ∧ i < b + w)) :
    blockExchange a b w i = i := by simp [blockExchange, ha, hb]

theorem blockExchange_involutive (a b w : ℕ) (hab : a + w ≤ b) :
    Function.Involutive (blockExchange a b w) := by
  intro i
  by_cases ha : a ≤ i ∧ i < a + w
  · have hr : i - a < w := by omega
    have he : a + (i - a) = i := by omega
    have hl := blockExchange_left a b w (i - a) hab hr
    rw [he] at hl
    rw [hl, blockExchange_right a b w (i - a) hab hr]
    omega
  · by_cases hb : b ≤ i ∧ i < b + w
    · have hr : i - b < w := by omega
      have he : b + (i - b) = i := by omega
      have hl := blockExchange_right a b w (i - b) hab hr
      rw [he] at hl
      rw [hl, blockExchange_left a b w (i - b) hab hr]
      omega
    · rw [blockExchange_outside a b w i ha hb, blockExchange_outside a b w i ha hb]

theorem blockExchange_lt (n a b w i : ℕ) (hab : a + w ≤ b) (hb : b + w ≤ n)
    (hi : i < n) : blockExchange a b w i < n := by
  unfold blockExchange
  split_ifs <;> omega

def blockExchangePerm (n a b w : ℕ) (hab : a + w ≤ b) (hb : b + w ≤ n) :
    Equiv.Perm (Fin n) where
  toFun i := ⟨blockExchange a b w i.val, blockExchange_lt n a b w i.val hab hb i.isLt⟩
  invFun i := ⟨blockExchange a b w i.val, blockExchange_lt n a b w i.val hab hb i.isLt⟩
  left_inv i := Fin.ext (blockExchange_involutive a b w hab i.val)
  right_inv i := Fin.ext (blockExchange_involutive a b w hab i.val)

end IntegerMultBounds.MathlibTM2.Routing
