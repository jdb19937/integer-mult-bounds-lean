module

public import IntegerMultBounds.Sizes
public import IntegerMultBounds.NLogN.CoprimeLengths

/-! The source lengths of the assembly. For all large `n`, every choice of
`tᵢ ∈ {r/2, r}` has odd, pairwise coprime `sᵢ` with
`(1 - 2η) tᵢ < sᵢ ≤ (1 - η) tᵢ`, `η = 1/(4d)`. This replaces the manuscript's
short-interval primes: the assembly only uses that the `sᵢ` are odd and
pairwise coprime. -/

@[expose] public section

namespace IntegerMultBounds.Sizes

open Filter Parameters TimeBound

/-- Eventually `ℓ ≥ 84 d³ + 1`, since `ℓ ≥ p / (12 d)` and `d ≤ p^ε` with `4ε < 1`. -/
theorem eventually_ℓ_large : ∀ᶠ n : ℕ in atTop, 84 * d n ^ 3 + 1 ≤ ℓ n := by
  have hexp : 0 < 1 - 4 * epsilon := by norm_num [epsilon]
  have hgrow : ∀ᶠ n : ℕ in atTop, (1020 : ℝ) ≤ precision n ^ (1 - 4 * epsilon) :=
    ((tendsto_rpow_atTop hexp).comp tendsto_precision).eventually_ge_atTop 1020
  filter_upwards [eventually_ℓ_bounds, hgrow] with n ⟨hlo, _⟩ hgrow
  have hp := precision_pos n
  have hd1 : (1 : ℝ) ≤ d n := by exact_mod_cast one_le_d n
  have hdp : (d n : ℝ) ≤ precision n ^ epsilon := d_le n
  have hd4 : (d n : ℝ) ^ 4 ≤ precision n ^ (4 * epsilon) := by
    calc (d n : ℝ) ^ 4 ≤ (precision n ^ epsilon) ^ 4 := by gcongr
      _ = precision n ^ (4 * epsilon) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]; ring_nf
  have hsplit : precision n = precision n ^ (4 * epsilon) * precision n ^ (1 - 4 * epsilon) := by
    rw [← Real.rpow_add hp]; norm_num
  have hpe : 0 ≤ precision n ^ (4 * epsilon) := by positivity
  have hbig : 12 * (d n : ℝ) * (84 * (d n : ℝ) ^ 3 + 1) ≤ precision n := by
    have h1 : 12 * (d n : ℝ) * (84 * (d n : ℝ) ^ 3 + 1) ≤ 1020 * (d n : ℝ) ^ 4 := by
      nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hd1 3]
    nlinarith
  have hd0 : (0 : ℝ) < 12 * d n := by positivity
  have hreal : (84 * (d n : ℝ) ^ 3 + 1) ≤ ℓ n := by
    refine le_trans ?_ hlo
    rw [le_div_iff₀ hd0]
    linarith
  exact_mod_cast hreal

/-- For all large `n` and every `tᵢ ∈ {r/2, r}` there are odd, pairwise coprime
source lengths `sᵢ` with `(1 - 2η) tᵢ < sᵢ ≤ (1 - η) tᵢ`, `η = 1/(4d)`. -/
theorem eventually_coprime_lengths : ∀ᶠ n : ℕ in atTop, ∀ t : Fin (d n) → ℕ,
    (∀ i, t i = 2 ^ (ℓ n - 1) ∨ t i = 2 ^ ℓ n) →
    ∃ s : Fin (d n) → ℕ, (∀ i, Odd (s i)) ∧ Pairwise (fun i i' => Nat.Coprime (s i) (s i')) ∧
      ∀ i, (4 * d n - 2) * t i < 4 * d n * s i ∧ 4 * d n * s i ≤ (4 * d n - 1) * t i := by
  filter_upwards [eventually_ℓ_large] with n hℓ t ht
  have hX : NLogN.CoprimeLengths.bound (d n) ≤ 2 ^ (ℓ n - 1) :=
    (NLogN.CoprimeLengths.bound_le (one_le_d n)).trans
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine NLogN.CoprimeLengths.exists_lengths (one_le_d n) hX t fun i => ?_
  rcases ht i with h | h
  · exact Or.inl h
  · right
    rw [h, ← pow_succ']
    congr 1
    omega

end IntegerMultBounds.Sizes
