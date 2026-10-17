module

public import IntegerMultBounds.MathlibTM2.Layer.LayerRBounds

/-!
# The rounded top with a shrink before the shift

The rounded top `topR` may round an entry past the exact value, so its output can leave the unit
disk. `topRS` first moves each component of the pre-shift value `topPre` toward zero by `c`
(`shrinkZ`), then shifts by `2^s` with truncation toward zero. When `c` bounds the error of
`topPre` (`√2 · piecesErr ≤ c`), every output component is at most the exact component in
absolute value (`topRS_abs_le`), and within `1 + 2c/2^s` of it (`topRS_sub_le`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Layer

open IntegerMultBounds.Networks ComplexFramedExecution

/-- Move an integer toward zero by `c`, stopping at zero. -/
def shrinkI (c : ℕ) (x : ℤ) : ℤ := if 0 ≤ x then max (x - c) 0 else min (x + c) 0

/-- Move both components of a Gaussian integer toward zero by `c`. -/
def shrinkZ (c : ℕ) (z : GaussianInt) : GaussianInt := ⟨shrinkI c z.re, shrinkI c z.im⟩

lemma abs_shrinkI_le {c : ℕ} {x : ℤ} {X : ℝ} (h : |(x : ℝ) - X| ≤ c) :
    |(shrinkI c x : ℝ)| ≤ |X| := by
  rw [abs_le] at h
  unfold shrinkI
  split_ifs with hx
  · rcases le_total (x - c) 0 with hc | hc
    · rw [max_eq_right hc]; simp
    · rw [max_eq_left hc]; push_cast
      have : (0 : ℝ) ≤ x - c := by exact_mod_cast hc
      rw [abs_of_nonneg this]; exact (by linarith : (x : ℝ) - c ≤ X).trans (le_abs_self X)
  · rcases le_total (x + c) 0 with hc | hc
    · rw [min_eq_left hc]; push_cast
      have : (x : ℝ) + c ≤ 0 := by exact_mod_cast hc
      rw [abs_of_nonpos this]; exact (by linarith : -((x : ℝ) + c) ≤ -X).trans (neg_le_abs X)
    · rw [min_eq_right hc]; simp

lemma abs_shrinkI_sub_le (c : ℕ) (x : ℤ) : |(shrinkI c x : ℝ) - x| ≤ c := by
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  unfold shrinkI
  split_ifs with hx
  · have hx' : (0 : ℝ) ≤ x := by exact_mod_cast hx
    rcases le_total (x - c) 0 with h | h
    · rw [max_eq_right h]
      have : (x : ℝ) ≤ c := by have := (Int.cast_le (R := ℝ)).2 h; push_cast at this; linarith
      rw [abs_le]; push_cast; constructor <;> linarith
    · rw [max_eq_left h]; push_cast; rw [abs_le]; constructor <;> linarith
  · have hx' : (x : ℝ) < 0 := by exact_mod_cast not_le.1 hx
    rcases le_total (x + c) 0 with h | h
    · rw [min_eq_left h]; push_cast; rw [abs_le]; constructor <;> linarith
    · rw [min_eq_right h]
      have : -(c : ℝ) ≤ x := by have := (Int.cast_le (R := ℝ)).2 h; push_cast at this; linarith
      rw [abs_le]; push_cast; constructor <;> linarith

lemma abs_truncR_le (x : ℝ) : |(truncR x : ℝ)| ≤ |x| := by
  unfold truncR
  split_ifs with h
  · have h1 := Int.floor_le x
    have h0 : (0 : ℝ) ≤ ⌊x⌋ := by exact_mod_cast Int.floor_nonneg.2 h
    rw [abs_of_nonneg h0, abs_of_nonneg h]; exact h1
  · have hx : x < 0 := not_le.1 h
    have h1 := Int.le_ceil x
    have h0 : (⌈x⌉ : ℝ) ≤ 0 := by exact_mod_cast Int.ceil_le.2 (by push_cast; linarith)
    rw [abs_of_nonpos h0, abs_of_neg hx]; linarith

/-- One component: shrink by `c`, then truncate by `2^s`. -/
lemma shrink_tdiv_le {c s : ℕ} {x : ℤ} {X : ℝ} (h : |(x : ℝ) - X| ≤ c) :
    |((shrinkI c x).tdiv (2 ^ s) : ℝ)| ≤ |X| / 2 ^ s ∧
      |((shrinkI c x).tdiv (2 ^ s) : ℝ) - X / 2 ^ s| ≤ 1 + 2 * c / 2 ^ s := by
  have hpos : (0 : ℝ) < 2 ^ s := by positivity
  rw [tdiv_truncR]
  have hS := abs_shrinkI_le h
  have hD := abs_shrinkI_sub_le c x
  set y := (shrinkI c x : ℝ)
  constructor
  · refine (abs_truncR_le _).trans ?_
    rw [abs_div, abs_of_pos hpos]
    exact div_le_div_of_nonneg_right hS hpos.le
  · have hT := abs_truncR_sub_le_one (y / 2 ^ s)
    have hy : |y / 2 ^ s - X / 2 ^ s| ≤ 2 * c / 2 ^ s := by
      rw [← sub_div, abs_div, abs_of_pos hpos]
      apply div_le_div_of_nonneg_right _ hpos.le
      have := abs_sub_le y x X
      linarith
    have := abs_sub_le ((truncR (y / 2 ^ s) : ℤ) : ℝ) (y / 2 ^ s) (X / 2 ^ s)
    linarith

/-- The rounded top with a shrink by `c` before the shift by `2^s`. -/
noncomputable def topRS {R r n : ℕ} (ds : Directions) (a : ℕ) (low : List (Fin n))
    (top : List (Fin (n + a))) {R₂ : ℕ} (hR₂ : R * 2 ^ a ≤ R₂) (Ps : List (Piece n R₂))
    (g s c : ℕ) (Z : ZArr (Fin R × Fin r) (n + a)) : ZArr (Fin R × Fin r) (n + a) :=
  fun p => tdivZ s (shrinkZ c (topPre ds a low top hR₂ Ps g Z p))

lemma re_two_pow_mul (s : ℕ) (z : ℂ) : ((2 : ℂ) ^ s * z).re = 2 ^ s * z.re := by
  rw [show (2 : ℂ) ^ s = ((2 ^ s : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]

lemma im_two_pow_mul (s : ℕ) (z : ℂ) : ((2 : ℂ) ^ s * z).im = 2 ^ s * z.im := by
  rw [show (2 : ℂ) ^ s = ((2 ^ s : ℝ) : ℂ) by push_cast; rfl, Complex.im_ofReal_mul]

section Top

variable {R r n : ℕ} (ds : Directions) (hd : ComplexPhaseBudget.Realizes ds) (a : ℕ)
    (low : List (Fin n)) (top : List (Fin (n + a))) {R₂ : ℕ} (hR₂ : R * 2 ^ a ≤ R₂)
    (Ps : List (Piece n R₂)) (hinj : ∀ P ∈ Ps, Function.Injective P.e)
    (hcover : (Ps.flatMap Piece.bitsList).Perm low)
    (hsel : (low.map (Fin.castAdd a) ++ top).Nodup) (g s c : ℕ)
    (hs : s = (low.length + top.length + 1) / 2 + top.length + (Ps.map (Piece.expR ds)).sum + g)
    (hc : √2 * piecesErr ds r Ps ≤ c)
    (Z : ZArr (Fin R × Fin r) (n + a)) (p : (Fin R × Fin r) × (Fin (n + a) → ZMod 2))

include hd hinj hcover hsel hs hc

/-- Both components of the pre-shift value are within `c` of `2^s Hl`. -/
lemma topPre_re_im_le :
    |((topPre ds a low top hR₂ Ps g Z p).re : ℝ) -
        (2 ^ s * Hl _ (low.map (Fin.castAdd a) ++ top) (toC Z) p).re| ≤ c ∧
      |((topPre ds a low top hR₂ Ps g Z p).im : ℝ) -
        (2 ^ s * Hl _ (low.map (Fin.castAdd a) ++ top) (toC Z) p).im| ≤ c := by
  have h := (topPre_err ds hd a low top hR₂ Ps hinj hcover hsel g s hs Z p).trans hc
  set w := GaussianInt.toComplex (topPre ds a low top hR₂ Ps g Z p) -
    2 ^ s * Hl _ (low.map (Fin.castAdd a) ++ top) (toC Z) p
  have hre : ((topPre ds a low top hR₂ Ps g Z p).re : ℝ) -
      (2 ^ s * Hl _ (low.map (Fin.castAdd a) ++ top) (toC Z) p).re = w.re := by
    simp [w]
  have him : ((topPre ds a low top hR₂ Ps g Z p).im : ℝ) -
      (2 ^ s * Hl _ (low.map (Fin.castAdd a) ++ top) (toC Z) p).im = w.im := by
    simp [w]
  rw [hre, him]
  exact ⟨(Complex.abs_re_le_norm w).trans h, (Complex.abs_im_le_norm w).trans h⟩

/-- **The shrunk top.** Each output component is at most the exact component of `Hl` in absolute
value and within `1 + 2c/2^s` of it. -/
theorem topRS_err :
    let H := Hl _ (low.map (Fin.castAdd a) ++ top) (toC Z) p
    let y := topRS ds a low top hR₂ Ps g s c Z p
    |(y.re : ℝ)| ≤ |H.re| ∧ |(y.im : ℝ)| ≤ |H.im| ∧
      |(y.re : ℝ) - H.re| ≤ 1 + 2 * c / 2 ^ s ∧ |(y.im : ℝ) - H.im| ≤ 1 + 2 * c / 2 ^ s := by
  intro H y
  obtain ⟨hre, him⟩ := topPre_re_im_le ds hd a low top hR₂ Ps hinj hcover hsel g s c hs hc Z p
  rw [re_two_pow_mul] at hre
  rw [im_two_pow_mul] at him
  have hpos : (0 : ℝ) < 2 ^ s := by positivity
  have e : ∀ x : ℝ, 2 ^ s * x / 2 ^ s = x := fun x => by field_simp
  have habs : ∀ x : ℝ, |2 ^ s * x| / 2 ^ s = |x| := fun x => by
    rw [abs_mul, abs_of_pos hpos]; field_simp
  obtain ⟨h1, h2⟩ := shrink_tdiv_le (s := s) hre
  obtain ⟨h3, h4⟩ := shrink_tdiv_le (s := s) him
  rw [habs] at h1 h3
  rw [e] at h2 h4
  exact ⟨h1, h3, h2, h4⟩

end Top

end IntegerMultBounds.MathlibTM2.Layer
