module

public import IntegerMultBounds.MathlibTM2.M8.Frames.Projector
public import IntegerMultBounds.MathlibTM2.M8.Height
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
public import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.NormNum

/-!
# Heights of the plain-frame projectors

The plain frames use the form `G = 1 − J/9` on `ℚ²³` (`formG`), with `9 G` the integer matrix
`gram9`. For an integer matrix `B` with entries in `[-1, 1]` and invertible Gram matrix, Cramer's
rule writes `proj G B` as `Z / d`, with `d` the determinant of the integer Gram matrix
`M = Bᵀ (9 G) B` and `Z = B adj(M) Bᵀ (9 G)` (`proj_int`). The entries of `M` are at most `4232`,
there are at most `23` columns, and the determinant bound `|det| ≤ k! cᵏ` bounds `d` and the
entries of `adj M`, so every entry of `proj G B` has numerator and denominator at most
`10 ^ 200` (`frame_height_le`, `frame_bounded`), and every entry of `1 − proj G B` has height at
most `2 · 10 ^ 200` (`frame_compl_bounded`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Frames

open Matrix
open scoped Nat

/-- `9 G` for the form `G = 1 − J/9`: `8` on the diagonal, `-1` off it. -/
def gram9 : Matrix (Fin 23) (Fin 23) ℤ := fun i j => if i = j then 8 else -1

/-- An integer matrix as a rational one. -/
abbrev castQ {α β : Type*} (X : Matrix α β ℤ) : Matrix α β ℚ := X.map (Int.castRingHom ℚ)

/-- The form `G = 1 − J/9`. -/
noncomputable def formG : Matrix (Fin 23) (Fin 23) ℚ := (9 : ℚ)⁻¹ • castQ gram9

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The integer Gram matrix `Bᵀ (9 G) B`. -/
def gramZ (Bz : Matrix (Fin 23) κ ℤ) : Matrix κ κ ℤ := Bzᵀ * gram9 * Bz

omit [Fintype κ] [DecidableEq κ] in
theorem gram_eq (Bz : Matrix (Fin 23) κ ℤ) :
    (castQ Bz)ᵀ * formG * castQ Bz = (9 : ℚ)⁻¹ • castQ (gramZ Bz) := by
  rw [formG, gramZ, Matrix.mul_smul, Matrix.smul_mul, castQ, castQ, castQ, Matrix.map_mul,
    Matrix.map_mul, transpose_map]

theorem det_gramZ_ne {Bz : Matrix (Fin 23) κ ℤ}
    (hB : IsUnit ((castQ Bz)ᵀ * formG * castQ Bz).det) : (gramZ Bz).det ≠ 0 := by
  intro h
  rw [gram_eq, det_smul, castQ, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero,
    mul_zero] at hB
  exact not_isUnit_zero hB

/-- **Cramer's rule for the projector.** -/
theorem proj_int {Bz : Matrix (Fin 23) κ ℤ} (hB : IsUnit ((castQ Bz)ᵀ * formG * castQ Bz).det) :
    proj formG (castQ Bz) = ((gramZ Bz).det : ℚ)⁻¹ •
      castQ (Bz * (gramZ Bz).adjugate * Bzᵀ * gram9) := by
  set f := Int.castRingHom ℚ
  have hd : ((gramZ Bz).det : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (det_gramZ_ne hB)
  have hdet : (castQ (gramZ Bz)).det = ((gramZ Bz).det : ℚ) := by
    rw [castQ, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  have hadj : (castQ (gramZ Bz)).adjugate = castQ (gramZ Bz).adjugate := by
    rw [castQ, castQ, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, RingHom.map_adjugate]
  have hinv : ((castQ Bz)ᵀ * formG * castQ Bz)⁻¹ =
      (9 : ℚ) • (((gramZ Bz).det : ℚ)⁻¹ • castQ (gramZ Bz).adjugate) := by
    rw [gram_eq]
    apply inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, ← hadj, mul_adjugate, hdet, smul_smul,
      smul_smul, smul_smul,
      show (9 : ℚ)⁻¹ * 9 * ((gramZ Bz).det : ℚ)⁻¹ * ((gramZ Bz).det : ℚ) = 1 by field_simp,
      one_smul]
  rw [proj, hinv, formG]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [show (9 : ℚ)⁻¹ * (9 * ((gramZ Bz).det : ℚ)⁻¹) = ((gramZ Bz).det : ℚ)⁻¹ by field_simp]
  congr 1
  rw [castQ, castQ, castQ, castQ, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, transpose_map]

/-! ### Entry bounds -/

section Bounds
variable {α β γ : Type*} [Fintype β]

theorem abs_mul_apply_le {X : Matrix α β ℤ} {Y : Matrix β γ ℤ} {a b : ℤ}
    (hX : ∀ i j, |X i j| ≤ a) (hY : ∀ i j, |Y i j| ≤ b) (i : α) (j : γ) :
    |(X * Y) i j| ≤ Fintype.card β * (a * b) := by
  rw [Matrix.mul_apply]
  calc |∑ k, X i k * Y k j| ≤ ∑ k, |X i k * Y k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : β, a * b := Finset.sum_le_sum fun k _ => by
        rw [abs_mul]
        exact mul_le_mul (hX i k) (hY k j) (abs_nonneg _) ((abs_nonneg _).trans (hX i k))
    _ = Fintype.card β * (a * b) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Bounds

theorem abs_det_le {A : Matrix κ κ ℤ} {c : ℤ} (hA : ∀ i j, |A i j| ≤ c) :
    |A.det| ≤ (Fintype.card κ)! * c ^ Fintype.card κ := by
  have := det_le (abv := AbsoluteValue.abs) hA
  rwa [nsmul_eq_mul] at this

theorem abs_adjugate_le {A : Matrix κ κ ℤ} {c : ℤ} (hc : 1 ≤ c) (hA : ∀ i j, |A i j| ≤ c)
    (i j : κ) : |A.adjugate i j| ≤ (Fintype.card κ)! * c ^ Fintype.card κ := by
  rw [adjugate_apply]
  apply abs_det_le
  intro r s
  rw [updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]
    split_ifs <;> simp <;> omega
  · exact hA r s

theorem abs_gram9 (i j : Fin 23) : |gram9 i j| ≤ 8 := by
  unfold gram9
  split_ifs <;> norm_num

/-- At most `23` columns have an invertible Gram matrix. -/
theorem card_le_of_isUnit {Bz : Matrix (Fin 23) κ ℤ}
    (hB : IsUnit ((castQ Bz)ᵀ * formG * castQ Bz).det) : Fintype.card κ ≤ 23 := by
  have h := rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr hB)
  have h2 := (rank_mul_le_right ((castQ Bz)ᵀ * formG) (castQ Bz)).trans
    (rank_le_card_height (castQ Bz))
  rw [h, Fintype.card_fin] at h2
  exact h2

theorem cramer_le {A : ℕ} (hA : A = 23 ! * 4232 ^ 23) : 23 * (23 * (23 * A) * 8) ≤ 10 ^ 200 := by
  rw [hA]
  norm_num [Nat.factorial]

theorem ht_int_div (z d : ℤ) (hd : d ≠ 0) :
    Height.ht ((z : ℚ) / d) ≤ max z.natAbs d.natAbs := by
  rw [← Rat.divInt_eq_div]
  exact Height.ht_divInt z d hd

/-- **Plain-frame heights.** For an integer matrix `B` with entries in `[-1, 1]` and invertible
Gram matrix, every entry of the `G`-orthogonal projector onto its columns has numerator and
denominator at most `10 ^ 200`. -/
theorem frame_height_le {Bz : Matrix (Fin 23) κ ℤ} (hB1 : ∀ i a, |Bz i a| ≤ 1)
    (hB : IsUnit ((castQ Bz)ᵀ * formG * castQ Bz).det) (i j : Fin 23) :
    (proj formG (castQ Bz) i j).num.natAbs ≤ 10 ^ 200 ∧
      (proj formG (castQ Bz) i j).den ≤ 10 ^ 200 := by
  have hk := card_le_of_isUnit hB
  set k := Fintype.card κ with hkdef
  have hd := det_gramZ_ne hB
  -- the Gram entries
  have hM : ∀ a b, |gramZ Bz a b| ≤ 4232 := by
    intro a b
    have h1 : ∀ a l, |(Bzᵀ * gram9) a l| ≤ 23 * (1 * 8) := fun a l => by
      have := abs_mul_apply_le (X := Bzᵀ) (fun a i => by rw [transpose_apply]; exact hB1 i a)
        abs_gram9 a l
      rwa [Fintype.card_fin] at this
    have := abs_mul_apply_le h1 hB1 a b
    rw [Fintype.card_fin] at this
    exact this.trans (by norm_num)
  -- the factorial-power bound
  obtain ⟨A, hAeq⟩ : ∃ A : ℕ, A = 23 ! * 4232 ^ 23 := ⟨_, rfl⟩
  have hA : ((k ! : ℕ) : ℤ) * 4232 ^ k ≤ (A : ℤ) := by
    rw [hAeq, Nat.cast_mul, Nat.cast_pow]
    exact mul_le_mul (by exact_mod_cast Nat.factorial_le hk)
      (pow_le_pow_right₀ (by norm_num) hk) (by positivity) (by positivity)
  have hdet : |(gramZ Bz).det| ≤ A := (abs_det_le hM).trans hA
  have hadj : ∀ a b, |(gramZ Bz).adjugate a b| ≤ A := fun a b =>
    (abs_adjugate_le (by norm_num) hM a b).trans hA
  -- the numerator
  have hk' : (k : ℤ) ≤ 23 := by exact_mod_cast hk
  have hA0 : (0 : ℤ) ≤ A := by positivity
  have hZ : ∀ a b, |(Bz * (gramZ Bz).adjugate * Bzᵀ * gram9) a b| ≤
      ((23 * (23 * (23 * A) * 8) : ℕ) : ℤ) := by
    intro a b
    have h1 : ∀ a b, |(Bz * (gramZ Bz).adjugate) a b| ≤ 23 * (A : ℤ) := fun a b => by
      refine (abs_mul_apply_le hB1 hadj a b).trans ?_
      rw [one_mul]
      exact mul_le_mul_of_nonneg_right hk' hA0
    have h2 : ∀ a b, |(Bz * (gramZ Bz).adjugate * Bzᵀ) a b| ≤ 23 * (23 * (A : ℤ)) := fun a b => by
      refine (abs_mul_apply_le h1 (fun a i => by rw [transpose_apply]; exact hB1 i a) a b).trans ?_
      rw [mul_one]
      exact mul_le_mul_of_nonneg_right hk' (by positivity)
    have h3 := abs_mul_apply_le h2 abs_gram9 a b
    rw [Fintype.card_fin] at h3
    refine h3.trans (le_of_eq ?_)
    push_cast
    ring
  have hdetB : |(gramZ Bz).det| ≤ ((23 * (23 * (23 * A) * 8) : ℕ) : ℤ) := hdet.trans (by
    push_cast
    nlinarith [hA0])
  -- the entry
  have hentry : proj formG (castQ Bz) i j =
      ((Bz * (gramZ Bz).adjugate * Bzᵀ * gram9) i j : ℚ) / ((gramZ Bz).det : ℚ) := by
    rw [proj_int hB, Matrix.smul_apply, smul_eq_mul, castQ, map_apply, eq_intCast, div_eq_inv_mul]
  have hht := ht_int_div ((Bz * (gramZ Bz).adjugate * Bzᵀ * gram9) i j) _ hd
  rw [← hentry] at hht
  have hnat : max ((Bz * (gramZ Bz).adjugate * Bzᵀ * gram9) i j).natAbs (gramZ Bz).det.natAbs ≤
      23 * (23 * (23 * A) * 8) := by
    refine max_le ?_ ?_
    · have := hZ i j
      rw [← Int.natCast_natAbs] at this
      exact_mod_cast this
    · rw [← Int.natCast_natAbs] at hdetB
      exact_mod_cast hdetB
  have hfin := (hht.trans hnat).trans (cramer_le hAeq)
  exact ⟨(Height.num_le_ht _).trans hfin, (Height.den_le_ht _).trans hfin⟩

theorem frame_bounded {Bz : Matrix (Fin 23) κ ℤ} (hB1 : ∀ i a, |Bz i a| ≤ 1)
    (hB : IsUnit ((castQ Bz)ᵀ * formG * castQ Bz).det) :
    Height.Bounded (proj formG (castQ Bz)) (10 ^ 200) := fun i j =>
  max_le (frame_height_le hB1 hB i j).1 (frame_height_le hB1 hB i j).2

/-- The complementary frame `1 − proj G B`, as for the root hyperplanes. -/
theorem frame_compl_bounded {Bz : Matrix (Fin 23) κ ℤ} (hB1 : ∀ i a, |Bz i a| ≤ 1)
    (hB : IsUnit ((castQ Bz)ᵀ * formG * castQ Bz).det) :
    Height.Bounded (1 - proj formG (castQ Bz)) (2 * 10 ^ 200) := fun i j => by
  rw [Matrix.sub_apply]
  have h1 : Height.ht ((1 : Matrix (Fin 23) (Fin 23) ℚ) i j) = 1 := by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  refine (Height.ht_sub _ _).trans ?_
  rw [h1, mul_one]
  exact Nat.mul_le_mul_left 2 (frame_bounded hB1 hB i j)

end IntegerMultBounds.MathlibTM2.M8.Frames
