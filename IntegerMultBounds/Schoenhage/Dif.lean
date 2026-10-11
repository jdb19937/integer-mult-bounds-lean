module

public import IntegerMultBounds.Spec.SyntheticTransformFacts

/-! The in-place decimation-in-frequency recursion of §6 on one axis. A round
at slot `h` pairs the entries whose addresses differ only in bit `h`, writes
their half-sum at bit `0` and their half-difference times `y^(-(2r/2^(h+1)) k)`
at bit `1`, `k` the address bits below `h`. Running the rounds from the top
slot down computes the normalized transform `F⁻` with its output in
bit-reversed order (`difAll_eq`): entry `x` holds `(F⁻ z)_(rev x)`. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Spec.SignedRingProduct NLogN

variable {r : ℕ} [NeZero r]

/-! ### Negative shifts -/

theorem shiftInv_eq_of (e N : ℕ) (h : e ≤ 2 * r * N) (v : Fin r → ℂ) :
    shiftInv e v = shiftNegZ (2 * r * N - e) v := by
  have hr : 0 < 2 * r := by have := NeZero.pos r; omega
  unfold shiftInv
  rw [shiftNegZ_mod (2 * r * N - e)]
  congr 1
  have hq := Nat.mod_add_div e (2 * r)
  set s := e % (2 * r)
  set q := e / (2 * r)
  have hs : s < 2 * r := Nat.mod_lt _ hr
  have hqN : 2 * r * q ≤ 2 * r * N := by nlinarith
  have hqN' : q ≤ N := Nat.le_of_mul_le_mul_left hqN hr
  rcases Nat.eq_zero_or_pos s with h0 | hpos
  · rw [h0, Nat.sub_zero, Nat.mod_self]
    have : 2 * r * N - e = 2 * r * (N - q) := by rw [Nat.mul_sub]; omega
    rw [this, Nat.mul_mod_right]
  · rw [Nat.mod_eq_of_lt (by omega)]
    have hq1 : q + 1 ≤ N := by
      by_contra hc
      have : q = N := by omega
      subst this; omega
    have : 2 * r * N - e = (2 * r - s) + 2 * r * (N - q - 1) := by
      have : 2 * r * N = 2 * r * (N - q - 1) + 2 * r * q + 2 * r := by
        rw [← Nat.mul_add, ← Nat.mul_succ]; congr 1; omega
      omega
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem shiftInv_add (e₁ e₂ : ℕ) (v : Fin r → ℂ) : shiftInv (e₁ + e₂) v = shiftInv e₁ (shiftInv e₂ v) := by
  rw [shiftInv_eq_of (e₁ + e₂) (e₁ + e₂) (by have := NeZero.pos r; nlinarith),
    shiftInv_eq_of e₁ e₁ (by have := NeZero.pos r; nlinarith),
    shiftInv_eq_of e₂ e₂ (by have := NeZero.pos r; nlinarith), shiftNegZ_add]
  congr 1
  have h1 : e₁ ≤ 2 * r * e₁ := by have := NeZero.pos r; nlinarith
  have h2 : e₂ ≤ 2 * r * e₂ := by have := NeZero.pos r; nlinarith
  rw [Nat.mul_add]; omega

theorem shiftNegZ_r_mul (v : Fin r → ℂ) : ∀ j : ℕ, shiftNegZ (r * j) v = (-1 : ℂ) ^ j • v
  | 0 => by simp [shiftNegZ_zero]
  | j + 1 => by
    rw [Nat.mul_succ, add_comm, ← shiftNegZ_add, shiftNegZ_r_mul v j, ← shiftZCLM_apply, map_smul,
      shiftZCLM_apply, shiftNegZ_r, smul_neg, pow_succ, mul_neg_one, neg_smul]

theorem shiftInv_r_mul (j : ℕ) (v : Fin r → ℂ) : shiftInv (r * j) v = (-1 : ℂ) ^ j • v := by
  have e : 2 * r * j - r * j = r * j := by
    have : 2 * r * j = r * j + r * j := by ring
    omega
  rw [shiftInv_eq_of (r * j) j (by nlinarith), e, shiftNegZ_r_mul]

theorem shiftInv_zero (v : Fin r → ℂ) : shiftInv 0 v = v := by
  unfold shiftInv; simp [shiftNegZ_zero]

theorem shiftInv_clm (e : ℕ) (v : Fin r → ℂ) : shiftInv e v = shiftZCLM r ((2 * r - e % (2 * r)) % (2 * r)) v :=
  (shiftZCLM_apply _ _).symm

theorem shiftInv_add_vec (e : ℕ) (v w : Fin r → ℂ) : shiftInv e (v + w) = shiftInv e v + shiftInv e w := by
  simp only [shiftInv_clm, map_add]

theorem shiftInv_sub_vec (e : ℕ) (v w : Fin r → ℂ) : shiftInv e (v - w) = shiftInv e v - shiftInv e w := by
  simp only [shiftInv_clm, map_sub]

theorem shiftInv_neg (e : ℕ) (v : Fin r → ℂ) : shiftInv e (-v) = -shiftInv e v := by
  simp only [shiftInv_clm, map_neg]

theorem shiftInv_smul (e : ℕ) (c : ℂ) (v : Fin r → ℂ) : shiftInv e (c • v) = c • shiftInv e v := by
  simp only [shiftInv_clm, map_smul]

/-! ### Rounds -/

/-- Bit `h` of `x`. -/
def bitAt (x h : ℕ) : ℕ := x / 2 ^ h % 2

/-- One decimation-in-frequency round at slot `h`. -/
noncomputable def difRound (h : ℕ) (z : ℕ → Fin r → ℂ) : ℕ → Fin r → ℂ := fun x =>
  if bitAt x h = 0 then (1 / 2 : ℂ) • (z x + z (x + 2 ^ h))
  else shiftInv (2 * r / 2 ^ (h + 1) * (x % 2 ^ h)) ((1 / 2 : ℂ) • (z (x - 2 ^ h) - z x))

/-- The rounds at slots `a - 1, …, 0`, from the top slot down. -/
noncomputable def difAll : ℕ → (ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ
  | 0, z => z
  | a + 1, z => difAll a (difRound a z)

theorem bitAt_add_mul {x h m : ℕ} (hm : 2 ^ (h + 1) ∣ m) : bitAt (x + m) h = bitAt x h := by
  obtain ⟨c, rfl⟩ := hm
  unfold bitAt
  rw [pow_succ, show 2 ^ h * 2 * c = 2 ^ h * (2 * c) by ring, Nat.add_mul_div_left _ _ (by positivity),
    Nat.add_mul_mod_self_left]

theorem mod_add_mul {x h m : ℕ} (hm : 2 ^ (h + 1) ∣ m) : (x + m) % 2 ^ h = x % 2 ^ h := by
  obtain ⟨c, rfl⟩ := hm
  rw [pow_succ, show 2 ^ h * 2 * c = 2 ^ h * (2 * c) by ring, Nat.add_mul_mod_self_left]

theorem le_of_bitAt {x h : ℕ} (hb : bitAt x h ≠ 0) : 2 ^ h ≤ x := by
  unfold bitAt at hb
  by_contra hc
  rw [Nat.div_eq_of_lt (by omega)] at hb
  simp at hb

theorem difRound_shift (h m : ℕ) (hm : 2 ^ (h + 1) ∣ m) (z : ℕ → Fin r → ℂ) (y : ℕ) :
    difRound h (fun x => z (x + m)) y = difRound h z (y + m) := by
  unfold difRound
  dsimp only
  rw [bitAt_add_mul hm, mod_add_mul hm]
  split_ifs with hb
  · rw [show y + 2 ^ h + m = y + m + 2 ^ h by ring]
  · have := le_of_bitAt hb
    rw [show y - 2 ^ h + m = y + m - 2 ^ h by omega]

theorem difAll_shift : ∀ (a m : ℕ), 2 ^ a ∣ m → ∀ (z : ℕ → Fin r → ℂ) (y : ℕ),
    difAll a (fun x => z (x + m)) y = difAll a z (y + m)
  | 0, m, _, z, y => rfl
  | a + 1, m, hm, z, y => by
    simp only [difAll]
    have e : difRound a (fun x => z (x + m)) = fun x => difRound a z (x + m) :=
      funext fun x => difRound_shift a m hm z x
    rw [e]
    exact difAll_shift a m (dvd_trans (pow_dvd_pow 2 (Nat.le_succ a)) hm) _ y

/-! ### The transform on one axis -/

omit [NeZero r] in
theorem synthExpL_single (t j k : ℕ) : synthExpL r [t] j k = 2 * r / t * (j % t) * (k % t) := by
  simp [synthExpL, digit]

theorem fwdT_single (t : ℕ) (z : ℕ → Fin r → ℂ) (j : ℕ) :
    fwdT [t] z j = (1 / (t : ℂ)) • ∑ k ∈ Finset.range t, shiftInv (2 * r / t * (j % t) * (k % t)) (z k) := by
  simp [fwdT, synthExpL_single]

/-- One step of the recursion: an even or odd frequency of length `2^(a+1)` is a frequency of length
`2^a` of the round's output in the corresponding half. -/
theorem fwdT_dif (a : ℕ) (hr : 2 ^ (a + 1) ∣ 2 * r) (z : ℕ → Fin r → ℂ) {J c : ℕ} (hJ : J < 2 ^ a)
    (hc : c < 2) :
    fwdT [2 ^ (a + 1)] z (2 * J + c) = fwdT [2 ^ a] (fun y => difRound a z (y + c * 2 ^ a)) J := by
  set N := 2 ^ a
  set q := 2 * r / 2 ^ (a + 1)
  have hq2 : q * 2 ^ (a + 1) = 2 * r := Nat.div_mul_cancel hr
  have hqN : q * N = r := by
    have : q * 2 ^ (a + 1) = 2 * (q * N) := by simp only [N, pow_succ]; ring
    omega
  have hq' : 2 * r / N = 2 * q := by
    rw [show 2 * r = 2 * q * N by rw [← hq2, pow_succ]; ring, Nat.mul_div_cancel _ (by positivity)]
  have hN2 : 2 ^ (a + 1) = N + N := by simp only [N, pow_succ]; ring
  rw [fwdT_single, fwdT_single, hN2, Finset.sum_range_add, hq', Nat.mod_eq_of_lt hJ,
    Nat.mod_eq_of_lt (show 2 * J + c < N + N by omega)]
  rw [show 2 * r / (N + N) = q by rw [← hN2]]
  have hcoef : (1 / ((N + N : ℕ) : ℂ)) = (1 / (N : ℂ)) * (1 / 2) := by push_cast; field_simp; ring
  rw [hcoef, ← smul_smul, ← Finset.sum_add_distrib, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < N := Finset.mem_range.mp hk
  rw [Nat.mod_eq_of_lt (show k < N + N by omega), Nat.mod_eq_of_lt (show N + k < N + N by omega),
    Nat.mod_eq_of_lt hk']
  have e2 : q * (2 * J + c) * (N + k) = q * (2 * J + c) * k + r * (2 * J + c) := by
    rw [← hqN]; ring
  rw [e2, shiftInv_add, shiftInv_r_mul, pow_add, pow_mul, neg_one_sq, one_pow, one_mul]
  have hb : bitAt (k + c * N) a = c := by
    unfold bitAt
    rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hk', zero_add, Nat.mod_eq_of_lt hc]
  unfold difRound
  rw [hb]
  interval_cases c
  · simp only [pow_zero, one_smul, zero_mul, add_zero, ↓reduceIte]
    rw [show k + N = N + k by ring, shiftInv_smul, shiftInv_add_vec]
    congr 2
    rw [show 2 * q * J * k = q * (2 * J) * k by ring]
  · simp only [pow_one, one_mul, one_ne_zero, ↓reduceIte, neg_one_smul]
    rw [show k + N - N = k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hk', show k + N = N + k by ring,
      shiftInv_smul, shiftInv_smul, ← shiftInv_add, shiftInv_sub_vec, shiftInv_neg, ← sub_eq_add_neg,
      show 2 * q * J * k + 2 * r / 2 ^ (a + 1) * k = q * (2 * J + 1) * k by simp only [q]; ring]

theorem bit_mod_pow {x a h : ℕ} (hh : h < a) : (x % 2 ^ a) / 2 ^ h % 2 = x / 2 ^ h % 2 := by
  conv_rhs => rw [← Nat.mod_add_div x (2 ^ a)]
  rw [show 2 ^ a = 2 ^ h * (2 * 2 ^ (a - h - 1)) by rw [← pow_succ', ← pow_add]; congr 1; omega,
    Nat.mul_assoc, Nat.add_mul_div_left _ _ (by positivity), Nat.mul_assoc, Nat.add_mul_mod_self_left]

theorem bitrev_mod (a x : ℕ) : bitrev a (x % 2 ^ a) = bitrev a x := by
  unfold bitrev
  congr 1
  apply List.map_congr_left
  intro h hh
  rw [bit_mod_pow (List.mem_range.mp hh)]

/-- `difAll_eq`: the rounds compute `F⁻` in bit-reversed order. -/
theorem difAll_eq : ∀ (a : ℕ), 2 ^ a ∣ 2 * r → ∀ (z : ℕ → Fin r → ℂ) (x : ℕ), x < 2 ^ a →
    difAll a z x = fwdT [2 ^ a] z (bitrev a x)
  | 0, _, z, x, hx => by
    have : x = 0 := by simpa using hx
    subst this
    simp [difAll, fwdT_single, bitrev_zero, shiftInv_zero]
  | a + 1, hr, z, x, hx => by
    have hr' : 2 ^ a ∣ 2 * r := dvd_trans (pow_dvd_pow 2 (Nat.le_succ a)) hr
    set c := x / 2 ^ a
    set y := x % 2 ^ a
    have hc : c < 2 := by
      simp only [c]; rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [pow_succ] at hx; omega
    have hy : y < 2 ^ a := Nat.mod_lt _ (by positivity)
    have hxy : x = y + c * 2 ^ a := by simp only [y, c]; rw [Nat.mod_add_div' x (2 ^ a)]
    simp only [difAll]
    rw [hxy, ← difAll_shift a (c * 2 ^ a) (dvd_mul_left _ _), difAll_eq a hr' _ y hy, bitrev_succ,
      ← hxy, ← bitrev_mod a x]
    have hcb : x / 2 ^ a % 2 = c := Nat.mod_eq_of_lt hc
    rw [hcb, fwdT_dif a hr z (bitrev_lt a y) hc]

end IntegerMultBounds.Schoenhage
