module

public import IntegerMultBounds.Primes.SourcePrimes
public import IntegerMultBounds.MathlibTM2.Mult.Sizes

/-!
# The prime supply at the sizes

* `eventually_le_pow_pred`: for any sizing with `b ≤ C d ℓ`, `d^M ≤ b^M'`, `M' < M` and `b → ∞`,
  eventually `d ≤ (ℓ - 1)^(M'+1)`. This is the hypothesis `d ≤ ℓ^B` of
  `primes_in_window_two_pow` for every dimension exponent `ε = M'/M < 1`; at the sizes of
  `Mult/Sizes.lean` `d ≤ 2ℓ` gives it with `B = 2` (`Sizes.eventually_primeSupply`).
* Cost. `ptEmitAtoms_le`, `ptSrcAtoms_le`: the emission below `2^k` uses at most
  `32 (m + 1) 4^k` and `82 (d + 1) 4^k` atoms. `Big.search_cost_le`: under `Big`,
  `2^18 (b + 6)^3 4^ℓ ≤ n`, so the search with `O(b²)` host steps per atom costs at most `n`.
-/

@[expose] public section

namespace IntegerMultBounds.Primes

open Filter Finset IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes

/-! ### `d ≤ (ℓ - 1)^B` for a general sizing -/

/-- For any sizing with `b ≤ C d ℓ`, `d^M ≤ b^M'` and `M' < M`, eventually
`d ≤ (ℓ - 1)^(M' + 1)`. -/
theorem eventually_le_pow_pred {b d ℓ : ℕ → ℕ} {C M M' : ℕ} (hM : M' < M)
    (hb : Tendsto b atTop atTop) (hbdl : ∀ᶠ n in atTop, b n ≤ C * (d n * ℓ n))
    (hdb : ∀ᶠ n in atTop, d n ^ M ≤ b n ^ M') (hd : ∀ᶠ n in atTop, 1 ≤ d n) :
    ∀ᶠ n in atTop, d n ≤ (ℓ n - 1) ^ (M' + 1) := by
  -- `d ≤ C^M' ℓ^M'`
  have hA : ∀ᶠ n in atTop, d n ≤ C ^ M' * ℓ n ^ M' := by
    filter_upwards [hbdl, hdb, hd] with n h1 h2 h3
    have hpow : d n ^ M ≤ d n ^ M' * (C ^ M' * ℓ n ^ M') := by
      calc d n ^ M ≤ b n ^ M' := h2
        _ ≤ (C * (d n * ℓ n)) ^ M' := Nat.pow_le_pow_left h1 _
        _ = d n ^ M' * (C ^ M' * ℓ n ^ M') := by ring
    have hsplit : d n ^ M = d n ^ M' * d n ^ (M - M') := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit] at hpow
    have hle := Nat.le_of_mul_le_mul_left hpow (pow_pos h3 _)
    exact (Nat.le_self_pow (by omega) _).trans hle
  -- `ℓ → ∞`
  have hℓ : Tendsto ℓ atTop atTop := by
    refine tendsto_atTop.2 fun L => ?_
    filter_upwards [hbdl, hA, tendsto_atTop.1 hb (C ^ (M' + 1) * L ^ (M' + 1) + 1)]
      with n h1 h2 h3
    by_contra hc
    have hc' : ℓ n ≤ L := by omega
    have : b n ≤ C ^ (M' + 1) * L ^ (M' + 1) := by
      calc b n ≤ C * (d n * ℓ n) := h1
        _ ≤ C * ((C ^ M' * ℓ n ^ M') * ℓ n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h2)
        _ = C ^ (M' + 1) * ℓ n ^ (M' + 1) := by ring
        _ ≤ C ^ (M' + 1) * L ^ (M' + 1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hc' _)
    omega
  filter_upwards [hA, tendsto_atTop.1 hℓ ((2 * C) ^ M' + 2)] with n h1 h2
  have hl2 : ℓ n ≤ 2 * (ℓ n - 1) := by omega
  calc d n ≤ C ^ M' * ℓ n ^ M' := h1
    _ ≤ C ^ M' * (2 * (ℓ n - 1)) ^ M' := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hl2 _)
    _ = (2 * C) ^ M' * (ℓ n - 1) ^ M' := by ring
    _ ≤ (ℓ n - 1) * (ℓ n - 1) ^ M' := Nat.mul_le_mul_right _ (by omega)
    _ = (ℓ n - 1) ^ (M' + 1) := by ring

/-! ### Cost -/

/-- The emission of `m` primes below `2^k` uses at most `32 (m + 1) 4^k` atoms. -/
theorem ptEmitAtoms_le {lo hi m k : ℕ} (hlh : lo ≤ hi) (hhi : hi ≤ 2 ^ k) :
    ptEmitAtoms lo hi m ≤ 32 * (m + 1) * 4 ^ k := by
  have hP : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h4 : 4 ^ k = 2 ^ k * 2 ^ k := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
  have hPP : 1 ≤ 2 ^ k * 2 ^ k := Nat.mul_le_mul hP hP
  have hsq : Nat.sqrt hi ≤ 2 ^ k := (Nat.sqrt_le_self hi).trans hhi
  have hpa : 3 + ptPrimeAtoms hi ≤ 23 * 2 ^ k := by
    unfold ptPrimeAtoms
    omega
  have hgap : (hi - lo) * (3 + ptPrimeAtoms hi) ≤ 2 ^ k * (23 * 2 ^ k) :=
    Nat.mul_le_mul (by omega) hpa
  have e3 : 2 ^ k * (23 * 2 ^ k) = 23 * (2 ^ k * 2 ^ k) := by ring
  have hg : ptGapAtoms lo hi + 4 ≤ 32 * 4 ^ k := by
    unfold ptGapAtoms
    rw [h4]
    omega
  have e : ptGapAtoms lo hi + 1 + 1 + 2 = ptGapAtoms lo hi + 4 := by ring
  have e2 : 32 * (m + 1) * 4 ^ k = m * (32 * 4 ^ k) + 32 * 4 ^ k := by ring
  have hm := Nat.mul_le_mul_left m hg
  have h41 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  unfold ptEmitAtoms
  rw [e, e2]
  omega

/-- The two-window emission below `2R ≤ 2^k` uses at most `82 (d + 1) 4^k` atoms. -/
theorem ptSrcAtoms_le {d a R k : ℕ} (hd : 1 ≤ d) (had : a ≤ d) (hR : 2 * R ≤ 2 ^ k) :
    ptSrcAtoms d a R ≤ 82 * (d + 1) * 4 ^ k := by
  have h₁ := ptEmitAtoms_le (m := a) (winLo_le_winHi hd R)
    (((Nat.sub_le _ _).trans (by omega : R ≤ 2 * R)).trans hR)
  have h₂ := ptEmitAtoms_le (m := d - a) (winLo_le_winHi hd (2 * R)) ((Nat.sub_le _ _).trans hR)
  have h41 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have e1 : 32 * (a + 1) * 4 ^ k = 32 * a * 4 ^ k + 32 * 4 ^ k := by ring
  have e2 : 32 * (d - a + 1) * 4 ^ k = 32 * (d - a) * 4 ^ k + 32 * 4 ^ k := by ring
  have e3 : 82 * (d + 1) * 4 ^ k = 82 * d * 4 ^ k + 82 * 4 ^ k := by ring
  have hsum : 32 * a * 4 ^ k + 32 * (d - a) * 4 ^ k = 32 * d * 4 ^ k := by
    rw [← Nat.add_mul, ← Nat.mul_add, Nat.add_sub_cancel' had]
  have hd4 : 32 * d * 4 ^ k ≤ 82 * d * 4 ^ k := Nat.mul_le_mul_right _ (by omega)
  unfold ptSrcAtoms
  omega

/-! ### The search against `n` -/

private theorem cube_mul_le_two_pow {m : ℕ} (hm : 64 ≤ m) : 2 ^ 31 * m ^ 3 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h1 : (m + 1) ^ 3 ≤ 2 * m ^ 3 := by
      have h2 : m ^ 2 * 64 ≤ m ^ 2 * m := Nat.mul_le_mul_left _ hm
      have h3 : m * 64 ≤ m * m := Nat.mul_le_mul_left _ hm
      have e : (m + 1) ^ 3 = m ^ 3 + 3 * m ^ 2 + 3 * m + 1 := by ring
      have e2 : m ^ 3 = m ^ 2 * m := by ring
      have e3 : m ^ 2 = m * m := by ring
      omega
    calc 2 ^ 31 * (m + 1) ^ 3 ≤ 2 ^ 31 * (2 * m ^ 3) := Nat.mul_le_mul_left _ h1
      _ = 2 * (2 ^ 31 * m ^ 3) := by ring
      _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (m + 1) := by rw [pow_succ]; ring

/-- **The search is at most `n`.** Under `Big`, `2^18 (b + 6)^3 4^ℓ ≤ n`: `8ℓ ≤ b` and
`b ≥ 2^192`. -/
theorem _root_.IntegerMultBounds.MathlibTM2.Mult.Sizes.Big.search_cost_le {n : ℕ} (hB : Big n) : 2 ^ 18 * (b n + 6) ^ 3 * 4 ^ ℓ n ≤ n := by
  have hd16 : 16 ≤ d n := by have := hB.2; omega
  have hdb := d_le_b n
  have hb : 2 ^ 10 ≤ b n := by have := hB.2; omega
  have h3 := hB.ℓ_bounds.2
  rw [mul_assoc] at h3
  unfold p at h3
  have h16 := Nat.mul_le_mul_right (ℓ n) hd16
  obtain ⟨m, hm⟩ : ∃ m, m = b n / 4 := ⟨_, rfl⟩
  have hℓm : 2 * ℓ n ≤ m := by omega
  have hm64 : 64 ≤ m := by omega
  have h4 : 4 ^ ℓ n ≤ 2 ^ m := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb6 : (b n + 6) ^ 3 ≤ 125 * m ^ 3 := by
    calc (b n + 6) ^ 3 ≤ (5 * m) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ = 125 * m ^ 3 := by ring
  have hc := cube_mul_le_two_pow hm64
  have hn : 2 ^ (b n - 1) < n := by
    have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := n) (by have := hB.1; omega)
    simpa [b, Nat.pred_eq_sub_one] using this
  have h2m : 2 ^ m * 2 ^ m ≤ 2 ^ (b n - 1) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 2 ^ 18 * (b n + 6) ^ 3 * 4 ^ ℓ n ≤ 2 ^ 18 * (125 * m ^ 3) * 2 ^ m :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hb6) h4
    _ ≤ 2 ^ 31 * m ^ 3 * 2 ^ m := Nat.mul_le_mul_right _ (by
        rw [← mul_assoc]; exact Nat.mul_le_mul_right _ (by norm_num))
    _ ≤ 2 ^ m * 2 ^ m := Nat.mul_le_mul_right _ hc
    _ ≤ 2 ^ (b n - 1) := h2m
    _ ≤ n := hn.le

end IntegerMultBounds.Primes
