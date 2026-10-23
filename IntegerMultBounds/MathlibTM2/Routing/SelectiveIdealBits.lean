module

public import IntegerMultBounds.MathlibTM2.Routing.SelectiveIdeal
public import IntegerMultBounds.MathlibTM2.Routing.SelectiveLayout

/-! Bit-level contract of the all-address exact primitive. These facts connect
its physical destination ranks to coordinate placement and restored spectators. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable {p : Par} {X : ℕ} (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

theorem selectiveIdealIdx_bit (i q : ℕ) :
    (selectiveIdealIdx p X active s i).testBit q =
      if p.wc ≤ q ∧ q < p.wc + p.wy then
        Bool.xor (i.testBit q)
          ((targetWord p active s (selectiveView p X i).y (selectiveView p X i).x).testBit (q - p.wc))
      else i.testBit q := by
  rw [selectiveIdealIdx, testBit_setDigit]
  have hoff : fieldOff (selectiveLen p X) 1 = p.wc := selectiveFieldOff p X 1
  rw [hoff]
  change (if p.wc ≤ q ∧ q < p.wc + p.wy then _ else _) = _
  split
  · rename_i hq
    have hy : (selectiveView p X i).y.testBit (q - p.wc) = i.testBit q := by
      change ((i / 2 ^ fieldOff (selectiveLen p X) 1) % 2 ^ p.wy).testBit (q - p.wc) = _
      rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, hoff]
      simp [show q - p.wc < p.wy by omega, show q - p.wc + p.wc = q by omega]
    simp [Nat.testBit_xor, hy]
  · rfl

theorem selectiveIdealIdx_target_bit (hK : 0 < p.K) (i : ℕ) (c : Fin p.n) :
    (selectiveIdealIdx p X active s i).testBit (p.wc + posS p c.val) =
      Bool.xor (i.testBit (p.wc + posS p c.val))
        (active c && (s c).physical (selectiveView p X i).y (selectiveView p X i).x) := by
  have hc : posS p c.val < p.wy := by
    have hmul := Nat.mul_lt_mul_of_pos_right c.isLt hK
    unfold posS Par.wy
    omega
  rw [selectiveIdealIdx_bit]
  simp only [Nat.le_add_right, Nat.add_lt_add_iff_left, hc, and_self, ite_true,
    Nat.add_sub_cancel_left, targetWord_bit hK]

theorem selectiveIdealIdx_other_bit (hK : 0 < p.K) (i q : ℕ)
    (hq : ∀ c : Fin p.n, active c = true → q ≠ p.wc + posS p c.val) :
    (selectiveIdealIdx p X active s i).testBit q = i.testBit q := by
  rw [selectiveIdealIdx_bit]
  split
  · rename_i hfield
    rw [targetWord_other_bit hK active s _ _ (q - p.wc)]
    · simp
    · intro c hc he
      exact hq c hc (by omega)
  · rfl

theorem selectiveIdealIdx_row (i : ℕ) :
    selectiveIdealIdx p X active s i / 2 ^ fieldsLen (selectiveLen p X) =
      i / 2 ^ fieldsLen (selectiveLen p X) := by
  exact setDigit_div_total (selectiveLen p X) 1 _ i

end IntegerMultBounds.MathlibTM2.Routing
