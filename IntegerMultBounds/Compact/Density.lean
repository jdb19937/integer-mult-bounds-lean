module

public import IntegerMultBounds.Compact.Counting
public import IntegerMultBounds.Compact.RepairBounds
public import Mathlib.Algebra.Order.Ring.Pow

/-! Fractions of actual exceptional packed addresses. Exact finite counts are
converted to the source's union bounds, then to its uniform numerical estimate.
This file counts records; extracting and sorting them on tapes remains separate. -/

@[expose] public section

namespace IntegerMultBounds.Compact

noncomputable def badFraction {α : Type*} (P : α → Prop) : ℝ :=
  (Nat.card {x // ¬P x} : ℝ) / (Nat.card α : ℝ)

theorem badFraction_eq {α : Type*} [Fintype α] (P : α → Prop)
    (hpos : 0 < (Nat.card α : ℝ)) :
    badFraction P = 1 - (Nat.card {x // P x} : ℝ) / (Nat.card α : ℝ) := by
  classical
  have hle : Nat.card {x // P x} ≤ Nat.card α := by
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_le P
  have hc : Nat.card {x // ¬P x} = Nat.card α - Nat.card {x // P x} := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  rw [badFraction, hc, Nat.cast_sub hle, sub_div, div_self (ne_of_gt hpos)]

private theorem toNat_real (z : ℤ) (hz : 0 ≤ z) : (z.toNat : ℝ) = (z : ℝ) := by
  exact_mod_cast Int.toNat_of_nonneg hz

theorem early_total_real (B L : ℤ) (hB : 0 < B) (hL : 0 < L) (n : ℕ) :
    (Nat.card (EarlyAddress B L n) : ℝ) = (2 * (L : ℝ)) ^ n * (B : ℝ) ^ n := by
  rw [card_earlyAddress, Nat.cast_mul,
    toNat_real _ (pow_nonneg (by omega) n), toNat_real _ (pow_nonneg hB.le n)]
  push_cast
  rfl

theorem early_good_real (B L : ℤ) (hB : 0 < B) (hL : 0 < L)
    (hguard : 4 * B ≤ L) (n : ℕ) :
    (Nat.card {x : EarlyAddress B L n // earlyGood B L n x} : ℝ) =
      (2 * (L : ℝ) - 8 * (B : ℝ)) ^ n * ((B : ℝ) - 1) ^ n := by
  rw [card_earlyGood B L hB hL, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
    toNat_real _ (by omega), toNat_real _ (by omega)]
  push_cast
  rfl

theorem late_total_real (B L : ℤ) (hB : 0 < B) (hL : 0 < L) (n : ℕ) :
    (Nat.card (LateAddress B L n) : ℝ) =
      (B : ℝ) ^ n * ((2 * (L : ℝ)) ^ n * (B : ℝ) ^ n) := by
  rw [Nat.card_prod, Nat.cast_mul, card_field,
    toNat_real _ (pow_nonneg hB.le n), early_total_real B L hB hL]
  push_cast
  rfl

theorem late_good_real (B L : ℤ) (hB : 0 < B) (hL : 0 < L)
    (hguard : 4 * B ≤ L) (n : ℕ) :
    (Nat.card {x : LateAddress B L n // lateGood B L n x} : ℝ) =
      ((B : ℝ) - 1) ^ n *
        ((2 * (L : ℝ) - 8 * (B : ℝ)) ^ n * ((B : ℝ) - 1) ^ n) := by
  rw [Nat.card_congr (lateGoodEquiv B L n), Nat.card_prod, Nat.cast_mul,
    card_restricted_field B hB, card_unsaturated_digit, Nat.cast_pow,
    toNat_real _ (by omega), early_good_real B L hB hL hguard]
  push_cast
  rfl

theorem early_fraction_eq (B L : ℤ) (hB : 0 < B) (hL : 0 < L)
    (hguard : 4 * B ≤ L) (n : ℕ) :
    badFraction (earlyGood B L n) =
      1 - ((2 * (L : ℝ) - 8 * (B : ℝ)) / (2 * (L : ℝ))) ^ n *
        (((B : ℝ) - 1) / (B : ℝ)) ^ n := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  rw [badFraction_eq _ (by rw [early_total_real B L hB hL]; positivity),
    early_total_real B L hB hL, early_good_real B L hB hL hguard,
    mul_div_mul_comm, ← div_pow, ← div_pow]

theorem late_fraction_eq (B L : ℤ) (hB : 0 < B) (hL : 0 < L)
    (hguard : 4 * B ≤ L) (n : ℕ) :
    badFraction (lateGood B L n) =
      1 - (((B : ℝ) - 1) / (B : ℝ)) ^ n *
        (((2 * (L : ℝ) - 8 * (B : ℝ)) / (2 * (L : ℝ))) ^ n *
          (((B : ℝ) - 1) / (B : ℝ)) ^ n) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  rw [badFraction_eq _ (by rw [late_total_real B L hB hL]; positivity),
    late_total_real B L hB hL, late_good_real B L hB hL hguard,
    mul_div_mul_comm, mul_div_mul_comm, ← div_pow, ← div_pow]

private theorem one_sub_mul_le (x y : ℝ) (hx : x ≤ 1) (hy : y ≤ 1) :
    1 - x * y ≤ (1 - x) + (1 - y) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]

private theorem one_sub_pow_le (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    1 - x ^ n ≤ n * (1 - x) := by
  have h := one_add_mul_sub_le_pow (show -1 ≤ x by linarith) n
  linarith

private theorem digit_fractions (B L : ℤ) (hB : 0 < B) (hL : 0 < L)
    (hguard : 4 * B ≤ L) :
    (0 ≤ (2 * (L : ℝ) - 8 * (B : ℝ)) / (2 * (L : ℝ)) ∧
      (2 * (L : ℝ) - 8 * (B : ℝ)) / (2 * (L : ℝ)) ≤ 1) ∧
    (0 ≤ ((B : ℝ) - 1) / (B : ℝ) ∧ ((B : ℝ) - 1) / (B : ℝ) ≤ 1) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hgr : 4 * (B : ℝ) ≤ L := by exact_mod_cast hguard
  constructor
  · exact ⟨div_nonneg (by linarith) (by positivity),
      (div_le_one (by positivity)).mpr (by linarith)⟩
  · exact ⟨div_nonneg (by linarith) hBr.le, (div_le_one hBr).mpr (by linarith)⟩

/-- One temporary block and one guarded target block. -/
theorem early_bad_fraction_le (B L : ℤ) (hB : 0 < B) (hL : 0 < L)
    (hguard : 4 * B ≤ L) (n : ℕ) :
    badFraction (earlyGood B L n) ≤ (n : ℝ) / B + 8 * n * B / (2 * L) := by
  obtain ⟨⟨hu₀, hu₁⟩, ⟨hv₀, hv₁⟩⟩ := digit_fractions B L hB hL hguard
  have hprod := one_sub_mul_le _ _ (pow_le_one₀ hu₀ hu₁ (n := n))
    (pow_le_one₀ hv₀ hv₁ (n := n))
  have hu := one_sub_pow_le _ hu₀ n
  have hv := one_sub_pow_le _ hv₀ n
  rw [early_fraction_eq B L hB hL hguard]
  calc
    _ ≤ n * (1 - (2 * (L : ℝ) - 8 * (B : ℝ)) / (2 * (L : ℝ))) +
        n * (1 - ((B : ℝ) - 1) / (B : ℝ)) := by linarith
    _ = _ := by
      have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hB)
      have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
      field_simp
      ring

/-- Two temporary blocks and one guarded target block. -/
theorem late_bad_fraction_le (B L : ℤ) (hB : 0 < B) (hL : 0 < L)
    (hguard : 4 * B ≤ L) (n : ℕ) :
    badFraction (lateGood B L n) ≤ 2 * (n : ℝ) / B + 8 * n * B / (2 * L) := by
  obtain ⟨⟨hu₀, hu₁⟩, ⟨hv₀, hv₁⟩⟩ := digit_fractions B L hB hL hguard
  have hun := pow_le_one₀ hu₀ hu₁ (n := n)
  have hvn := pow_le_one₀ hv₀ hv₁ (n := n)
  have hprod := one_sub_mul_le _ _ hun hvn
  have hmul := (mul_le_mul_of_nonneg_right hun (pow_nonneg hv₀ n)).trans
    (by simpa only [one_mul] using hvn)
  have hprod' := one_sub_mul_le _ _ hvn hmul
  have hu := one_sub_pow_le _ hu₀ n
  have hv := one_sub_pow_le _ hv₀ n
  rw [late_fraction_eq B L hB hL hguard]
  calc
    _ ≤ n * (1 - (2 * (L : ℝ) - 8 * (B : ℝ)) / (2 * (L : ℝ))) +
        2 * n * (1 - ((B : ℝ) - 1) / (B : ℝ)) := by linarith
    _ = _ := by
      have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hB)
      have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
      field_simp
      ring

end IntegerMultBounds.Compact
