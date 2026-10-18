module

public import IntegerMultBounds.Primes.ShortInterval
public import IntegerMultBounds.Primes.NextPrime

/-!
# The first primes of the window below `2^ℓ`

The bridge from the prime supply to the search: eventually in `ℓ`, for every `d ≥ 1` with
`d ≤ ℓ^B`, the `d` primes that `ptEmitC` emits from `lo = ⌊(1 - 2η) 2^ℓ⌋₊` are primes of the
real window `((1 - 2η) 2^ℓ, (1 - η) 2^ℓ]`, `η = 1/(4d)`, in increasing order
(`windowPrime_two_pow`). The window holds at least `d` primes (`window_card_two_pow`), which is
the counting hypothesis of `ptEmitC_do`.
-/

@[expose] public section

namespace IntegerMultBounds.Primes

open Filter

/-- Eventually in `ℓ`, the window below `2^ℓ` holds at least `d` primes for `d ≤ ℓ^B`. -/
theorem window_card_two_pow (B : ℕ) :
    ∀ᶠ ℓ : ℕ in atTop, ∀ d : ℕ, 1 ≤ d → d ≤ ℓ ^ B →
      d ≤ ((Finset.Ioc ⌊(1 - 1 / (2 * (d : ℝ))) * 2 ^ ℓ⌋₊
        ⌊(1 - 1 / (4 * (d : ℝ))) * 2 ^ ℓ⌋₊).filter Nat.Prime).card :=
  primes_in_window_two_pow B

/-- **The first `d` window primes below `2^ℓ`.** Eventually in `ℓ`, for every `d ≥ 1` with
`d ≤ ℓ^B` and every `k < d`, the `k`-th prime above `⌊(1 - 2η) 2^ℓ⌋₊` is a prime of the window
`((1 - 2η) 2^ℓ, (1 - η) 2^ℓ]`, `η = 1/(4d)`. -/
theorem windowPrime_two_pow (B : ℕ) :
    ∀ᶠ ℓ : ℕ in atTop, ∀ d : ℕ, 1 ≤ d → d ≤ ℓ ^ B → ∀ k < d,
      (windowPrime ⌊(1 - 1 / (2 * (d : ℝ))) * 2 ^ ℓ⌋₊ k).Prime ∧
      (1 - 1 / (2 * (d : ℝ))) * 2 ^ ℓ <
        (windowPrime ⌊(1 - 1 / (2 * (d : ℝ))) * 2 ^ ℓ⌋₊ k : ℝ) ∧
      (windowPrime ⌊(1 - 1 / (2 * (d : ℝ))) * 2 ^ ℓ⌋₊ k : ℝ) ≤ (1 - 1 / (4 * (d : ℝ))) * 2 ^ ℓ := by
  filter_upwards [window_card_two_pow B] with ℓ hℓ d hd hdℓ k hk
  have hmem := windowPrime_mem (hℓ d hd hdℓ) hk
  obtain ⟨hIoc, hp⟩ := Finset.mem_filter.mp hmem
  have hhi : (0 : ℝ) ≤ (1 - 1 / (4 * (d : ℝ))) * 2 ^ ℓ := by
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have : 1 / (4 * (d : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    exact mul_nonneg (by linarith) (by positivity)
  obtain ⟨hlo, hle⟩ := mem_window hhi hIoc
  exact ⟨hp, hlo, hle⟩

end IntegerMultBounds.Primes
