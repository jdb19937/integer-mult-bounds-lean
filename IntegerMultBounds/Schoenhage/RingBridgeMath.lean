module

public import IntegerMultBounds.Schoenhage.RingSpec
public import IntegerMultBounds.Spec.PointwiseProducts

/-! The ring product's word-level output in the paper's format. A record's
component words, most significant bit first, reversed are the multiplier's
least-significant-first words (`compWord_reverse`); on disk grid records their
signed values are the numerators (`coeffs_lsbPairs`); and the output words,
reversed, are the words of `Q_p(f g / r)` (`ringOut_records`): the integer
negacyclic coefficients agree with `NLogN.negacyclicMul`, and truncation of
`2^-(p+ℓ)` times them is `rho0`. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Spec.SignedRingProduct NLogN

/-- The record's words in the multiplier's order and bit order: (real, imaginary) pairs, each reversed. -/
def lsbPairs {r : ℕ} (w : ℕ) (f : Rec r) : List (List Bool × List Bool) :=
  (List.finRange r).map fun j => ((compWord w (f.1 j)).reverse, (compWord w (f.2 j)).reverse)

/-- A record as its list of component words, most significant bit first. -/
def recordWords {r : ℕ} (w : ℕ) (re im : Fin r → ℤ) : List (List Bool) :=
  (List.finRange r).flatMap fun j => [compWord w (re j), compWord w (im j)]

theorem flatten_flatMap_pair {α : Type} (f g : α → List Bool) : ∀ l : List α,
    (l.flatMap fun x => [f x, g x]).flatten = l.flatMap fun x => f x ++ g x
  | [] => rfl
  | x :: l => by simp [flatten_flatMap_pair f g l]

theorem recordWords_flatten {r : ℕ} (w : ℕ) (re im : Fin r → ℤ) :
    (recordWords w re im).flatten = record w re im :=
  flatten_flatMap_pair _ _ _

/-! ### Bit order -/

theorem bits_succ_snoc : ∀ (n v : ℕ), bits (n + 1) v = bits n v ++ [decide (v / 2 ^ n % 2 = 1)]
  | 0, v => by simp [bits]
  | n + 1, v => by
    rw [bits, bits_succ_snoc n (v / 2), bits, Nat.div_div_eq_div_mul, ← pow_succ']
    rfl

theorem msbBits_reverse : ∀ n v : ℕ, (msbBits n v).reverse = bits n v
  | 0, v => rfl
  | n + 1, v => by
    rw [msbBits, List.reverse_cons, msbBits_reverse n v, bits_succ_snoc]

theorem compWord_reverse (w : ℕ) (z : ℤ) : (compWord w z).reverse = tw w z := msbBits_reverse _ _

theorem tw_reverse (w : ℕ) (z : ℤ) : (tw w z).reverse = compWord w z := by
  rw [← compWord_reverse, List.reverse_reverse]

/-! ### Signed values -/

theorem sv_bits {n u : ℕ} (hu : u < 2 ^ (n + 1)) :
    sv (bits (n + 1) u) = u - if 2 ^ n ≤ u then 2 ^ (n + 1) else 0 := by
  rw [sv, bits_succ_snoc, List.dropLast_concat, bval_bits, List.length_append, length_bits]
  simp only [List.getLastD_eq_getLast?, List.getLast?_concat, Option.getD_some, List.length_singleton,
    Nat.add_sub_cancel]
  have hd : u / 2 ^ n < 2 := by rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [pow_succ] at hu; omega
  have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  by_cases h : 2 ^ n ≤ u
  · have h1 : u / 2 ^ n = 1 := by
      have := Nat.div_pos h (by positivity); omega
    have hm : u % 2 ^ n = u - 2 ^ n := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    simp [h1, h, hm, h2]; push_cast [Nat.cast_sub h]; ring
  · have h0 : u / 2 ^ n = 0 := Nat.div_eq_of_lt (by omega)
    simp [h0, h, Nat.mod_eq_of_lt (show u < 2 ^ n by omega)]

theorem sv_tw {w : ℕ} {z : ℤ} (hw : 1 ≤ w) (h1 : -2 ^ (w - 1) ≤ z) (h2 : z < 2 ^ (w - 1)) : sv (tw w z) = z := by
  obtain ⟨n, rfl⟩ : ∃ n, w = n + 1 := ⟨w - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1 h2
  have hp : (0 : ℤ) < 2 ^ (n + 1) := by positivity
  have hm0 := Int.emod_nonneg z hp.ne'
  have hm1 := Int.emod_lt_of_pos z hp
  have hu : (z % 2 ^ (n + 1)).toNat < 2 ^ (n + 1) := by
    have : ((z % 2 ^ (n + 1)).toNat : ℤ) < 2 ^ (n + 1) := by rw [Int.toNat_of_nonneg hm0]; exact hm1
    exact_mod_cast this
  rw [tw, sv_bits hu]
  have e2 : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  by_cases hz : 0 ≤ z
  · have hzm : z % 2 ^ (n + 1) = z := Int.emod_eq_of_lt hz (by omega)
    have : ¬ 2 ^ n ≤ (z % 2 ^ (n + 1)).toNat := by
      rw [hzm]; intro h; have : ((2 ^ n : ℕ) : ℤ) ≤ (z.toNat : ℤ) := by exact_mod_cast h
      rw [Int.toNat_of_nonneg hz] at this; push_cast at this; omega
    simp [this, hzm, Int.toNat_of_nonneg hz]
    try omega
  · have hzm : z % 2 ^ (n + 1) = z + 2 ^ (n + 1) := by
      rw [← Int.add_mul_emod_self_right z 1 (2 ^ (n + 1)), one_mul, Int.emod_eq_of_lt (by omega) (by omega)]
    have : 2 ^ n ≤ (z % 2 ^ (n + 1)).toNat := by
      have : ((2 ^ n : ℕ) : ℤ) ≤ ((z % 2 ^ (n + 1)).toNat : ℤ) := by
        rw [Int.toNat_of_nonneg hm0, hzm]; push_cast; omega
      exact_mod_cast this
    simp only [this, ↓reduceIte]
    rw [Int.toNat_of_nonneg hm0, hzm]; push_cast; ring

theorem lsbPairs_eq {r : ℕ} (w : ℕ) (f : Rec r) :
    lsbPairs w f = (List.finRange r).map fun j => (tw w (f.1 j), tw w (f.2 j)) := by
  simp [lsbPairs, compWord_reverse]

theorem coeffs_lsbPairs {r p w : ℕ} {f : Rec r} (hw : p + 2 ≤ w) (hf : DiskGrid p f.1 f.2) (odd : Bool) :
    coeffs odd (lsbPairs w f) = (List.finRange r).map (if odd then f.2 else f.1) := by
  rw [lsbPairs_eq, coeffs, List.map_map]
  apply List.map_congr_left
  intro j _
  have hb := hf.abs_le j
  have hpw : (2 : ℤ) ^ p < 2 ^ (w - 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
  cases odd
  · have := abs_le.mp hb.1
    simp only [Function.comp_apply, pick, Bool.false_eq_true, ↓reduceIte]
    exact sv_tw (by omega) (by linarith) (by linarith)
  · have := abs_le.mp hb.2
    simp only [Function.comp_apply, pick, ↓reduceIte]
    exact sv_tw (by omega) (by linarith) (by linarith)

/-! ### Negacyclic coefficients -/

theorem getD_map_finRange {r : ℕ} (u : Fin r → ℤ) {j : ℕ} (hj : j < r) :
    ((List.finRange r).map u).getD j 0 = u ⟨j, hj⟩ := by
  simp [List.getD_eq_getElem?_getD, hj]

/-- The integer negacyclic coefficient as a sum over `Fin r`, as in `NLogN.negacyclicMul`. -/
theorem ncCoef_fin {r : ℕ} (u v : Fin r → ℤ) (k : Fin r) :
    ncCoef r ((List.finRange r).map u) ((List.finRange r).map v) k =
      ∑ i : Fin r, (if i ≤ k then 1 else -1) * u i * v (k - i) := by
  unfold ncCoef
  rw [Finset.sum_range (fun i => ∑ j ∈ Finset.range r, _)]
  apply Finset.sum_congr rfl
  intro i _
  have hk := k.isLt; have hi := i.isLt
  have hsub : ((k - i : Fin r) : ℕ) = if i ≤ k then (k : ℕ) - i else k + r - i := by
    rw [Fin.sub_def]; simp only [Fin.le_def]
    split_ifs with h
    · rw [show (r - (i : ℕ) + k) = (k - i) + r by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
  rw [getD_map_finRange u hi]
  by_cases h : i ≤ k
  · have hl : (i : ℕ) ≤ k := h
    rw [Finset.sum_eq_single ((k : ℕ) - i)]
    · rw [if_pos (by omega), getD_map_finRange v (by omega), if_pos h]
      have : (⟨(k : ℕ) - i, by omega⟩ : Fin r) = k - i := Fin.ext (by rw [hsub, if_pos h])
      rw [this]; ring
    · intro j hj hne
      have := Finset.mem_range.mp hj
      rw [if_neg (by omega), if_neg (by omega)]
    · intro hn; exact absurd (Finset.mem_range.mpr (by omega)) hn
  · have hl : (k : ℕ) < i := by rw [Fin.le_def] at h; omega
    rw [Finset.sum_eq_single ((k : ℕ) + r - i)]
    · rw [if_neg (by omega), if_pos (by omega), getD_map_finRange v (by omega), if_neg h]
      have : (⟨(k : ℕ) + r - i, by omega⟩ : Fin r) = k - i := Fin.ext (by rw [hsub, if_neg h])
      rw [this]; ring
    · intro j hj hne
      have := Finset.mem_range.mp hj
      rw [if_neg (by omega), if_neg (by omega)]
    · intro hn; exact absurd (Finset.mem_range.mpr (by omega)) hn

/-! ### Truncation -/

theorem rho0_div (s : ℕ) (n : ℤ) : rho0 ((n : ℝ) / 2 ^ s) = trunc0 s n := by
  have e : ((2 : ℝ) ^ s) = ((2 ^ s : ℕ) : ℝ) := by push_cast; ring
  have hp : (0 : ℝ) < 2 ^ s := by positivity
  unfold rho0 trunc0
  by_cases hn : 0 ≤ n
  · rw [if_pos (div_nonneg (by exact_mod_cast hn) hp.le), if_pos hn, e, Int.floor_div_natCast, Int.floor_intCast]
    push_cast; rfl
  · have hx : ¬ (0 : ℝ) ≤ (n : ℝ) / 2 ^ s := by
      rw [not_le]; exact div_neg_of_neg_of_pos (by exact_mod_cast not_le.mp hn) hp
    rw [if_neg hx, if_neg hn]
    have : (n : ℝ) / 2 ^ s = -(((-n : ℤ) : ℝ) / ((2 ^ s : ℕ) : ℝ)) := by push_cast; ring
    rw [this, Int.ceil_neg, Int.floor_div_natCast, Int.floor_intCast]
    push_cast; rfl

/-! ### The complex product of grid polynomials -/

/-- The integer negacyclic sum. -/
def nsum {r : ℕ} (u v : Fin r → ℤ) (k : Fin r) : ℤ := ∑ i : Fin r, (if i ≤ k then 1 else -1) * u i * v (k - i)

theorem negacyclic_grid {r p : ℕ} (a b c e : Fin r → ℤ) (k : Fin r) :
    (negacyclicMul (gridPoly p a b) (gridPoly p c e) k).re = ((nsum a c k - nsum b e k : ℤ) : ℝ) / 2 ^ (2 * p) ∧
    (negacyclicMul (gridPoly p a b) (gridPoly p c e) k).im = ((nsum a e k + nsum b c k : ℤ) : ℝ) / 2 ^ (2 * p) := by
  have hp : (2 : ℝ) ^ (2 * p) = 2 ^ p * 2 ^ p := by rw [two_mul, pow_add]
  have hp0 : (2 : ℝ) ^ p ≠ 0 := by positivity
  unfold negacyclicMul nsum
  rw [Complex.re_sum, Complex.im_sum]
  constructor
  · rw [← Finset.sum_sub_distrib]; push_cast; rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro i _
    by_cases h : i ≤ k <;> simp [negaSign, negaIdx, h, gridPoly, Complex.mul_re, hp] <;> field_simp <;> ring
  · rw [← Finset.sum_add_distrib]; push_cast; rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro i _
    by_cases h : i ≤ k <;> simp [negaSign, negaIdx, h, gridPoly, Complex.mul_im, Complex.mul_re, hp] <;>
      field_simp <;> ring

theorem div_two_pow_re {p l : ℕ} (z : ℂ) (n : ℤ) (h : z.re = (n : ℝ) / 2 ^ (2 * p)) :
    2 ^ p * (z / ((2 ^ l : ℕ) : ℂ)).re = (n : ℝ) / 2 ^ (p + l) := by
  have e : ((2 ^ l : ℕ) : ℂ) = (((2 : ℝ) ^ l : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.div_ofReal_re, h]
  have : (2 : ℝ) ^ (2 * p) = 2 ^ p * 2 ^ p := by rw [two_mul, pow_add]
  rw [this, pow_add]; field_simp

theorem div_two_pow_im {p l : ℕ} (z : ℂ) (n : ℤ) (h : z.im = (n : ℝ) / 2 ^ (2 * p)) :
    2 ^ p * (z / ((2 ^ l : ℕ) : ℂ)).im = (n : ℝ) / 2 ^ (p + l) := by
  have e : ((2 ^ l : ℕ) : ℂ) = (((2 : ℝ) ^ l : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.div_ofReal_im, h]
  have : (2 : ℝ) ^ (2 * p) = 2 ^ p * 2 ^ p := by rw [two_mul, pow_add]
  rw [this, pow_add]; field_simp

theorem productRe_eq {p l : ℕ} (f g : Rec (2 ^ l)) (k : Fin (2 ^ l)) :
    productRe p (gridPoly p f.1 f.2) (gridPoly p g.1 g.2) k = trunc0 (p + l) (nsum f.1 g.1 k - nsum f.2 g.2 k) := by
  unfold productRe
  rw [div_two_pow_re _ _ (negacyclic_grid f.1 f.2 g.1 g.2 k).1, rho0_div]

theorem productIm_eq {p l : ℕ} (f g : Rec (2 ^ l)) (k : Fin (2 ^ l)) :
    productIm p (gridPoly p f.1 f.2) (gridPoly p g.1 g.2) k = trunc0 (p + l) (nsum f.1 g.2 k + nsum f.2 g.1 k) := by
  unfold productIm
  rw [div_two_pow_im _ _ (negacyclic_grid f.1 f.2 g.1 g.2 k).2, rho0_div]

/-! ### The output records -/

theorem flat_zip_map {α : Type} (f g : α → List Bool) : ∀ l : List α,
    flat (List.zip (l.map f) (l.map g)) = l.flatMap fun x => [f x, g x]
  | [] => rfl
  | x :: l => by simp [flat_zip_map f g l]

theorem range_map_eq {β : Type} (r : ℕ) (h : ℕ → β) :
    (List.range r).map h = (List.finRange r).map fun j : Fin r => h j.val := by
  rw [← List.map_coe_finRange_eq_range, List.map_map]; rfl

/-- The ring product's output words, reversed, are the words of `Q_p(f g / r)` in the paper's format. -/
theorem ringOut_records {p l w : ℕ} (hw : p + 2 ≤ w) {f g : Rec (2 ^ l)} (hf : DiskGrid p f.1 f.2)
    (hg : DiskGrid p g.1 g.2) :
    (flat (ringOut (2 ^ l) (p + l) w (lsbPairs w f) (lsbPairs w g))).map List.reverse =
      recordWords w (prodRec p f g).1 (prodRec p f g).2 := by
  unfold ringOut reCoeffs imCoeffs
  rw [coeffs_lsbPairs hw hf, coeffs_lsbPairs hw hf, coeffs_lsbPairs hw hg, coeffs_lsbPairs hw hg]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [zipWith_ncMul, zipWith_ncMul, List.map_map, List.map_map, range_map_eq, range_map_eq, flat_zip_map,
    List.map_flatMap, recordWords]
  refine List.flatMap_congr (fun k _ => ?_)
  simp only [Function.comp_apply, List.map_cons, List.map_nil, tw_reverse, prodRec]
  rw [ncCoef_fin, ncCoef_fin, ncCoef_fin, ncCoef_fin, productRe_eq, productIm_eq]
  rfl

end IntegerMultBounds.Schoenhage
