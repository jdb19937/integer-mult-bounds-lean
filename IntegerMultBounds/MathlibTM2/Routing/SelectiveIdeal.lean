module

public import IntegerMultBounds.MathlibTM2.Routing.SelectiveIndex

/-!
# The all-address ideal selective XOR

Repair needs an ideal permutation on every address, including failed guards.
Its source observation is unchanged by the sparse XOR itself, without any
no-carry hypothesis. Sources may therefore include inactive low target bits.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable {p : Par} {X : ℕ} (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

include hK

/-- The loaded word has support only at selected digit starts. -/
theorem targetWord_and_mask (y x : ℕ) :
    targetWord p active s y x &&& maskVal p.n (posS p) = targetWord p active s y x := by
  apply Nat.eq_of_testBit_eq
  intro q
  by_cases hm : ∃ c < p.n, posS p c = q
  · simp [Nat.testBit_and, testBit_maskVal (posS_mono hK), hm]
  · have hw := targetWord_other_bit hK active s y x q (by
      intro c _ he
      exact hm ⟨c, c.isLt, he.symm⟩)
    simp [Nat.testBit_and, hw]

/-- A sparse XOR word contributes only its low bit to each complete segment. -/
theorem targetWord_seg (y x : ℕ) (c : Fin p.n) :
    seg p.ρ p.K c.val (targetWord p active s y x) =
      (active c && (s c).physical y x).toNat := by
  rw [← targetWord_and_mask hK active s y x, seg_and_sel hK c.isLt,
    targetWord_bit hK active s]

private theorem targetWord_low (y x : ℕ) :
    targetWord p active s y x % 2 ^ p.ρ = 0 := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [Nat.testBit_mod_two_pow]
  by_cases hq : q < p.ρ
  · have hw := targetWord_other_bit hK active s y x q (by
      intro c _ he
      unfold posS at he
      omega)
    simp [hq, hw]
  · simp [hq]

private theorem targetWord_high (y x : ℕ) :
    targetWord p active s y x / 2 ^ (p.ρ + p.n * p.K) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [Nat.testBit_div_two_pow]
  have hw := targetWord_other_bit hK active s y x (q + (p.ρ + p.n * p.K)) (by
    intro c _ he
    unfold posS at he
    have hc' := Nat.mul_lt_mul_of_pos_right c.isLt hK
    omega)
  simp [hw]

/-- All source-visible coordinates survive the ideal XOR on every address. -/
theorem slotView_xor_targetWord (y x : ℕ) :
    slotView p active (y ^^^ targetWord p active s y x) = slotView p active y := by
  unfold slotView
  rw [xor_mod_two_pow, targetWord_low hK active s, Nat.xor_zero,
    xor_div_two_pow, targetWord_high hK active s, Nat.xor_zero]
  congr 2
  funext c
  rw [seg, window_xor, ← seg, ← seg, targetWord_seg hK active s y x c]
  cases ha : active c
  · simp
  · simp only [Bool.true_and, ite_true]
    rw [show ∀ a b : ℕ, (a ^^^ b) / 2 = a / 2 ^^^ b / 2 from
      fun a b => by simpa using xor_div_two_pow a b 1]
    cases (s c).physical y x <;> simp

/-- Dynamic sources are unchanged even where the packed guard fails. -/
theorem source_xor_targetWord (hs : ∀ c, (s c).Allowed active) (y x : ℕ) (c : Fin p.n) :
    (s c).physical (y ^^^ targetWord p active s y x) x = (s c).physical y x := by
  rw [← SlotSource.observed_physical active (s c) (hs c),
    slotView_xor_targetWord hK active s, SlotSource.observed_physical active (s c) (hs c)]

/-- Loading the actual source a second time gives exactly the same sparse word. -/
theorem targetWord_xor (hs : ∀ c, (s c).Allowed active) (y x : ℕ) :
    targetWord p active s (y ^^^ targetWord p active s y x) x = targetWord p active s y x := by
  apply congrArg (placeVal p.n (posS p))
  funext c
  by_cases hc : c < p.n
  · simp only [dite_eq_left hc, source_xor_targetWord hK active s hs]
  · simp only [dite_eq_right hc]

/-- The requested physical target update, also on exceptional indices. -/
def selectiveIdealIdx (p : Par) (X : ℕ) (active : Fin p.n → Bool)
    (s : Fin p.n → SlotSource p X) (i : ℕ) : ℕ :=
  setDigit (selectiveLen p X) 1 ((selectiveView p X i).y ^^^
    targetWord p active s (selectiveView p X i).y (selectiveView p X i).x) i

theorem selectiveIdeal_view (i : ℕ) :
    selectiveView p X (selectiveIdealIdx p X active s i) =
      { selectiveView p X i with y := (selectiveView p X i).y ^^^ targetWord p active s (selectiveView p X i).y (selectiveView p X i).x } := by
  have hy := Nat.xor_lt_two_pow (selectiveView_fits p X i).y
    (targetWord_lt p X hK active s (selectiveView p X i).y (selectiveView p X i).x)
  simp only [selectiveView, selectiveLen] at hy
  simp [selectiveIdealIdx, selectiveView, digit_setDigit, selectiveLen,
    Nat.mod_eq_of_lt hy]

theorem selectiveIdealIdx_involutive (hs : ∀ c, (s c).Allowed active) :
    Function.Involutive (selectiveIdealIdx p X active s) := by
  intro i
  change setDigit (selectiveLen p X) 1
    ((selectiveView p X (selectiveIdealIdx p X active s i)).y ^^^
      targetWord p active s (selectiveView p X (selectiveIdealIdx p X active s i)).y
        (selectiveView p X (selectiveIdealIdx p X active s i)).x)
      (selectiveIdealIdx p X active s i) = i
  rw [selectiveIdeal_view hK active s]
  simp only
  rw [targetWord_xor hK active s hs, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  exact (setDigit_setDigit_self (selectiveLen p X) 1 _ _ i).trans
    (setDigit_digit (selectiveLen p X) 1 i)

omit hK in
theorem selectiveIdealIdx_lt {R : ℕ} {i : ℕ}
    (hi : i < R * 2 ^ fieldsLen (selectiveLen p X)) :
    selectiveIdealIdx p X active s i < R * 2 ^ fieldsLen (selectiveLen p X) := by
  have hd := (Nat.div_lt_iff_lt_mul (show 0 < 2 ^ fieldsLen (selectiveLen p X) by positivity)).2 hi
  rw [← setDigit_div_total (selectiveLen p X) 1
    ((selectiveView p X i).y ^^^ targetWord p active s (selectiveView p X i).y
      (selectiveView p X i).x) i] at hd
  exact (Nat.div_lt_iff_lt_mul (by positivity)).1 hd

/-- The exact desired destination map, globally bijective without guard promises. -/
def selectiveIdealPerm (R : ℕ) (hs : ∀ c, (s c).Allowed active) :
    Equiv.Perm (Fin (R * 2 ^ fieldsLen (selectiveLen p X))) where
  toFun i := ⟨selectiveIdealIdx p X active s i, selectiveIdealIdx_lt active s i.isLt⟩
  invFun i := ⟨selectiveIdealIdx p X active s i, selectiveIdealIdx_lt active s i.isLt⟩
  left_inv i := Fin.ext (selectiveIdealIdx_involutive hK active s hs i)
  right_inv i := Fin.ext (selectiveIdealIdx_involutive hK active s hs i)

/-- The ideal permutation preserves the physical exceptional set in both directions. -/
theorem selectiveIdeal_good (i : ℕ) :
    Good p (selectiveView p X (selectiveIdealIdx p X active s i)) ↔
      Good p (selectiveView p X i) := by
  rw [selectiveIdeal_view hK active s]
  unfold Good
  simp only
  refine forall₂_congr fun c hc => and_congr_right' (and_congr_right' ?_)
  rw [seg, window_xor, ← seg, ← seg, targetWord_seg hK active s _ _ ⟨c, hc⟩]
  rw [show ∀ a b : ℕ, (a ^^^ b) / 2 = a / 2 ^^^ b / 2 from
    fun a b => by simpa using xor_div_two_pow a b 1]
  cases active ⟨c, hc⟩ <;> cases (s ⟨c, hc⟩).physical
    (selectiveView p X i).y (selectiveView p X i).x <;> simp

end IntegerMultBounds.MathlibTM2.Routing
