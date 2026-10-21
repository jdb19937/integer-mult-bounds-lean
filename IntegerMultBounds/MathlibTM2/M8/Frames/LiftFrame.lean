module

public import IntegerMultBounds.MathlibTM2.M8.Frames.SuppRank
public import IntegerMultBounds.MathlibTM2.M8.Exchange
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Root-complement frames of one centre

A design-B node frame is the `G`-complement `W(X)` of the span of the root vectors `X` that the
node reaches: `t_T` for an output `(c, T)`, whose `G`-image is the output covector, and
`w_c = 1 + 7 e_c` for the retained centre `c`, whose `G`-image is the centre covector. For a node
of one centre `c`, the outputs are the triples `{c, u, w}` of a pair mask `M`, and the frame is
`liftFrame c M r`: `1 − A` without the centre and `S − A` with it, where `A` is the frame of the
outputs and `S = starFrame c`.

* `w_c` is `G`-orthogonal to the star of `c` and `G(w_c, w_c) = −14`, so `S` and the line of
  `w_c` are complementary (`starFrame_add_centreLine`). The form is positive definite on the
  star, so every such frame is nondegenerate, with no computation.
* The frames nest as their root sets shrink (`liftFrame_nest`), lie in the hyperplane of every
  output they reach (`liftFrame_hyper`) and in the star when they reach the centre
  (`liftFrame_star`), and contain the frame of any triples that meet each output in one point and
  pass through `c` (`frameOf_lift`).
* The rank is `23 − dimC c M` or `22 − dimC c M` (`liftFrame_rank`), by the pair-graph rank of
  `SuppRank`.
* With the centre, `S − A = 1 − proj G [A's basis, w_c]`, so the entries have height at most
  `2 · 10 ^ 200` (`liftFrame_bounded`), as for the plain frames.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Frames

open Matrix Finset IntegerMultBounds.MathlibTM2.M8.Local
open scoped Nat

noncomputable section

/-! ### Concatenated bases -/

section Concat

variable {κ κ' : Type*} [Fintype κ] [Fintype κ'] [DecidableEq κ] [DecidableEq κ']
  {B₁ : Matrix (Fin 23) κ ℚ} {B₂ : Matrix (Fin 23) κ' ℚ}

omit [Fintype κ] [Fintype κ'] [DecidableEq κ] [DecidableEq κ'] in
theorem gram_fromCols (B₁ : Matrix (Fin 23) κ ℚ) (B₂ : Matrix (Fin 23) κ' ℚ) :
    (fromCols B₁ B₂)ᵀ * formG * fromCols B₁ B₂ =
      fromBlocks (B₁ᵀ * formG * B₁) (B₁ᵀ * formG * B₂) (B₂ᵀ * formG * B₁) (B₂ᵀ * formG * B₂) := by
  rw [transpose_fromCols, fromRows_mul, fromRows_mul_fromCols]

omit [Fintype κ] [Fintype κ'] [DecidableEq κ] [DecidableEq κ'] in
theorem cross_symm (h0 : B₁ᵀ * formG * B₂ = 0) : B₂ᵀ * formG * B₁ = 0 := by
  have := congrArg Matrix.transpose h0
  rwa [transpose_mul, transpose_mul, transpose_transpose, formG_transpose, transpose_zero,
    ← Matrix.mul_assoc] at this

theorem fromCols_gram_isUnit (h₁ : IsUnit (B₁ᵀ * formG * B₁).det)
    (h₂ : IsUnit (B₂ᵀ * formG * B₂).det) (h0 : B₁ᵀ * formG * B₂ = 0) :
    IsUnit ((fromCols B₁ B₂)ᵀ * formG * fromCols B₁ B₂).det := by
  rw [gram_fromCols, h0, cross_symm h0, det_fromBlocks_zero₂₁]
  exact h₁.mul h₂

/-- **Orthogonal bases.** The projector onto two `G`-orthogonal column spaces is the sum. -/
theorem proj_fromCols (h₁ : IsUnit (B₁ᵀ * formG * B₁).det) (h₂ : IsUnit (B₂ᵀ * formG * B₂).det)
    (h0 : B₁ᵀ * formG * B₂ = 0) :
    proj formG (fromCols B₁ B₂) = proj formG B₁ + proj formG B₂ := by
  have hinv : ((fromCols B₁ B₂)ᵀ * formG * fromCols B₁ B₂)⁻¹ =
      fromBlocks (B₁ᵀ * formG * B₁)⁻¹ 0 0 (B₂ᵀ * formG * B₂)⁻¹ := by
    rw [gram_fromCols, h0, cross_symm h0]
    apply inv_eq_left_inv
    rw [fromBlocks_multiply, nonsing_inv_mul _ h₁, nonsing_inv_mul _ h₂]
    simp [fromBlocks_one]
  rw [proj, hinv, fromCols_mul_fromBlocks, transpose_fromCols, fromCols_mul_fromRows, proj, proj]
  simp [Matrix.add_mul, Matrix.mul_assoc]

end Concat

/-! ### The centre vector -/

/-- The centre vector `w_c = 1 + 7 e_c`. -/
def wvec (c : ℕ) : Fin 23 → ℚ := fun i => 1 + 7 * tvec {c} i

/-- The centre vector as an integer column. -/
def wcolZ (c : ℕ) : Matrix (Fin 23) Unit ℤ := fun i _ => if i.val = c then 8 else 1

/-- The centre vector as a column. -/
def wcol (c : ℕ) : Matrix (Fin 23) Unit ℚ := fun i _ => wvec c i

theorem wcolZ_cast (c : ℕ) : castQ (wcolZ c) = wcol c := by
  ext i u
  simp only [castQ, wcolZ, wcol, wvec, tvec, map_apply, mem_singleton]
  split_ifs <;> norm_num

/-- The `G`-orthogonal projector onto the line of `w_c`. -/
def centreLine (c : ℕ) : Matrix (Fin 23) (Fin 23) ℚ := proj formG (wcol c)

theorem sum_wvec {c : ℕ} (hc : c < 23) : ∑ i, wvec c i = 30 := by
  simp only [wvec, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_tvec (S := {c}) (by simpa using hc)]
  norm_num

/-- `w_c` is `G`-orthogonal to every triple through `c`. -/
theorem gform_tvec_wvec {c : ℕ} (hc : c < 23) {S : Finset ℕ} (hS : IsTriple S) (hcS : c ∈ S) :
    gform (tvec S) (wvec c) = 0 := by
  have hdot : tvec S ⬝ᵥ wvec c = 10 := by
    have h1 : tvec S ⬝ᵥ wvec c = (∑ i, tvec S i) + 7 * (tvec S ⬝ᵥ tvec {c}) := by
      simp only [dotProduct, wvec, mul_add, mul_one, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, sum_tvec hS.2, hS.1, dot_tvec (by simpa using hc),
      show S ∩ {c} = {c} from Finset.inter_singleton_of_mem hcS]
    norm_num
  rw [gform_eq, hdot, sum_tvec hS.2, hS.1, sum_wvec hc]
  norm_num

theorem gform_wvec {c : ℕ} (hc : c < 23) : gform (wvec c) (wvec c) = -14 := by
  have hdot : wvec c ⬝ᵥ wvec c = 86 := by
    have h1 : wvec c ⬝ᵥ wvec c = 23 + 14 * (∑ i, tvec {c} i) + 49 * (tvec {c} ⬝ᵥ tvec {c}) := by
      simp only [dotProduct, wvec, Finset.mul_sum]
      rw [show (23 : ℚ) = ∑ _i : Fin 23, (1 : ℚ) by simp, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, sum_tvec (by simpa using hc), dot_tvec (by simpa using hc), Finset.inter_self]
    norm_num
  rw [gform_eq, hdot, sum_wvec hc]
  norm_num

theorem wcol_gram_isUnit {c : ℕ} (hc : c < 23) : IsUnit ((wcol c)ᵀ * formG * wcol c).det := by
  rw [isUnit_iff_ne_zero, det_unique, gram_apply]
  change gform (wvec c) (wvec c) ≠ 0
  rw [gform_wvec hc]
  norm_num

/-- Columns of triples through `c` are `G`-orthogonal to `w_c`. -/
theorem cross_wcol {𝒮 : Finset (Finset ℕ)} {c : ℕ} (h : InStar 𝒮 c) :
    (basisMat 𝒮)ᵀ * formG * wcol c = 0 := by
  ext b u
  rw [gram_apply, Matrix.zero_apply]
  obtain ⟨S, hS, hb⟩ := Finset.mem_image.mp (basisOf_sub 𝒮 b.2)
  change gform b.1 (wvec c) = 0
  rw [← hb]
  exact gform_tvec_wvec h.1 (h.2 S hS).1 (h.2 S hS).2

/-! ### The star and the centre line -/

theorem eq_zero_of_rank {A : Matrix (Fin 23) (Fin 23) ℚ} (h : A.rank = 0) : A = 0 := by
  rw [Matrix.rank] at h
  have hbot := Submodule.finrank_eq_zero.mp h
  ext i j
  have hv : A.mulVecLin (Pi.single j 1) ∈ LinearMap.range A.mulVecLin := ⟨_, rfl⟩
  rw [hbot, Submodule.mem_bot] at hv
  have := congrFun hv i
  simpa [Matrix.mulVecLin_apply, mulVec_single] using this

private theorem star_ok : ∀ c < 23, okC c (pairsWithout c) = true ∧ dimC c (pairsWithout c) = 22 := by
  decide +kernel

theorem one_ok {c M : ℕ} (hc : c < 23) (hM : subB M (pairsWithout c) = true) : (Supp.one c M).Ok :=
  ⟨hc, fun i hi => (testBit_pairsWithout hc i).mp (subB_spec hM i hi)⟩

theorem relP_one (c M : ℕ) : relP c (.one c M) = some M := by
  simp [relP]

theorem starSet_eq {c : ℕ} (hc : c < 23) : starSet c = suppSet (.one c (pairsWithout c)) := by
  ext S
  simp only [starSet, suppSet, mem_filter, mem_allTriples]
  constructor
  · rintro ⟨hS, hcS⟩; exact ⟨hS, (pairIn_centre hc hS.1 hS.2).mpr hcS⟩
  · rintro ⟨hS, hm⟩; exact ⟨hS, (pairIn_centre hc hS.1 hS.2).mp hm⟩

theorem starFrame_rank {c : ℕ} (hc : c < 23) : (starFrame c).rank = 22 := by
  have hok := one_ok hc (M := pairsWithout c) (by simp [subB])
  rw [starFrame, starSet_eq hc, ← suppFrame, suppFrame_rank hok (relP_one c _) (star_ok c hc).1]
  exact (star_ok c hc).2

/-- **The star and the centre line** are complementary. -/
theorem starFrame_add_centreLine {c : ℕ} (hc : c < 23) : starFrame c + centreLine c = 1 := by
  have h₁ := basis_gram_isUnit (starSet_mem hc)
  have h₂ := wcol_gram_isUnit hc
  have h0 := cross_wcol (starSet_mem hc)
  have hE := fromCols_gram_isUnit h₁ h₂ h0
  have hsum := proj_fromCols h₁ h₂ h0
  set E := proj formG (fromCols (basisMat (starSet c)) (wcol c))
  have hidem : E * E = E := proj_idem hE
  have hrank : E.rank = 23 := by
    rw [proj_rank hE, Fintype.card_sum, Fintype.card_unit, Fintype.card_coe,
      ← frameOf_rank (starSet_mem hc), ← starFrame, starFrame_rank hc]
  have h := Exchange.rank_sub_add E 1 hidem (Matrix.one_mul 1) (Matrix.mul_one E) (Matrix.one_mul E)
  rw [hrank, rank_one, Fintype.card_fin] at h
  have h1 := eq_zero_of_rank (show (1 - E).rank = 0 by omega)
  rw [starFrame, frameOf, centreLine, ← hsum]
  exact (sub_eq_zero.mp h1).symm

/-! ### Heights for entries up to `8` -/

section Height
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem cramer_le8 {A : ℕ} (hA : A = 23 ! * 270848 ^ 23) :
    23 * (23 * (23 * (8 * A) * 8) * 8) ≤ 10 ^ 200 := by
  rw [hA]
  norm_num [Nat.factorial]

/-- **Heights.** `frame_height_le` for integer columns with entries in `[-8, 8]`. -/
theorem frame_height_le8 {Bz : Matrix (Fin 23) κ ℤ} (hB8 : ∀ i a, |Bz i a| ≤ 8)
    (hB : IsUnit ((castQ Bz)ᵀ * formG * castQ Bz).det) (i j : Fin 23) :
    Height.ht (proj formG (castQ Bz) i j) ≤ 10 ^ 200 := by
  have hk := card_le_of_isUnit hB
  set k := Fintype.card κ with hkdef
  have hd := det_gramZ_ne hB
  have hBt : ∀ a i, |Bzᵀ a i| ≤ 8 := fun a i => by rw [transpose_apply]; exact hB8 i a
  have hM : ∀ a b, |gramZ Bz a b| ≤ 270848 := by
    intro a b
    have h1 : ∀ a l, |(Bzᵀ * gram9) a l| ≤ 23 * (8 * 8) := fun a l => by
      have := abs_mul_apply_le (X := Bzᵀ) hBt abs_gram9 a l
      rwa [Fintype.card_fin] at this
    have := abs_mul_apply_le h1 hB8 a b
    rw [Fintype.card_fin] at this
    exact this.trans (by norm_num)
  obtain ⟨A, hAeq⟩ : ∃ A : ℕ, A = 23 ! * 270848 ^ 23 := ⟨_, rfl⟩
  have hA : ((k ! : ℕ) : ℤ) * 270848 ^ k ≤ (A : ℤ) := by
    rw [hAeq, Nat.cast_mul, Nat.cast_pow]
    exact mul_le_mul (by exact_mod_cast Nat.factorial_le hk)
      (pow_le_pow_right₀ (by norm_num) hk) (by positivity) (by positivity)
  have hdet : |(gramZ Bz).det| ≤ A := (abs_det_le hM).trans hA
  have hadj : ∀ a b, |(gramZ Bz).adjugate a b| ≤ A := fun a b =>
    (abs_adjugate_le (by norm_num) hM a b).trans hA
  have hk' : (k : ℤ) ≤ 23 := by exact_mod_cast hk
  have hA0 : (0 : ℤ) ≤ A := by positivity
  have hZ : ∀ a b, |(Bz * (gramZ Bz).adjugate * Bzᵀ * gram9) a b| ≤
      ((23 * (23 * (23 * (8 * A) * 8) * 8) : ℕ) : ℤ) := by
    intro a b
    have h1 : ∀ a b, |(Bz * (gramZ Bz).adjugate) a b| ≤ 23 * (8 * (A : ℤ)) := fun a b =>
      (abs_mul_apply_le hB8 hadj a b).trans (mul_le_mul_of_nonneg_right hk' (by positivity))
    have h2 : ∀ a b, |(Bz * (gramZ Bz).adjugate * Bzᵀ) a b| ≤ 23 * (23 * (8 * (A : ℤ)) * 8) :=
      fun a b => (abs_mul_apply_le h1 hBt a b).trans
        (mul_le_mul_of_nonneg_right hk' (by positivity))
    have h3 := abs_mul_apply_le h2 abs_gram9 a b
    rw [Fintype.card_fin] at h3
    refine h3.trans (le_of_eq ?_)
    push_cast
    ring
  have hdetB : |(gramZ Bz).det| ≤ ((23 * (23 * (23 * (8 * A) * 8) * 8) : ℕ) : ℤ) :=
    hdet.trans (by push_cast; nlinarith [hA0])
  have hentry : proj formG (castQ Bz) i j =
      ((Bz * (gramZ Bz).adjugate * Bzᵀ * gram9) i j : ℚ) / ((gramZ Bz).det : ℚ) := by
    rw [proj_int hB, Matrix.smul_apply, smul_eq_mul, castQ, map_apply, eq_intCast, div_eq_inv_mul]
  have hht := ht_int_div ((Bz * (gramZ Bz).adjugate * Bzᵀ * gram9) i j) _ hd
  rw [← hentry] at hht
  have hnat : max ((Bz * (gramZ Bz).adjugate * Bzᵀ * gram9) i j).natAbs (gramZ Bz).det.natAbs ≤
      23 * (23 * (23 * (8 * A) * 8) * 8) := by
    refine max_le ?_ ?_
    · have := hZ i j
      rw [← Int.natCast_natAbs] at this
      exact_mod_cast this
    · rw [← Int.natCast_natAbs] at hdetB
      exact_mod_cast hdetB
  exact (hht.trans hnat).trans (cramer_le8 hAeq)

theorem frame_compl_bounded8 {Bz : Matrix (Fin 23) κ ℤ} (hB8 : ∀ i a, |Bz i a| ≤ 8)
    (hB : IsUnit ((castQ Bz)ᵀ * formG * castQ Bz).det) :
    Height.Bounded (1 - proj formG (castQ Bz)) (2 * 10 ^ 200) := fun i j => by
  rw [Matrix.sub_apply]
  have h1 : Height.ht ((1 : Matrix (Fin 23) (Fin 23) ℚ) i j) = 1 := by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  refine (Height.ht_sub _ _).trans ?_
  rw [h1, mul_one]
  exact Nat.mul_le_mul_left 2 (frame_height_le8 hB8 hB i j)

end Height

/-! ### Nested differences -/

theorem Nested.trans {A B C : Matrix (Fin 23) (Fin 23) ℚ} (h : Nested A B) (h' : Nested B C) :
    Nested A C :=
  ⟨by rw [← h.1, ← Matrix.mul_assoc, h'.1], by rw [← h.2, Matrix.mul_assoc, h'.2]⟩

/-- `E − A` grows as `E` grows and `A` shrinks. -/
theorem nested_sub {A A' E E' : Matrix (Fin 23) (Fin 23) ℚ} (hA : Nested A' A) (hAE : Nested A E)
    (hE : Nested E E') : Nested (E - A) (E' - A') := by
  have hAE' := hAE.trans hE
  have hA'E := hA.trans hAE
  constructor
  · simp only [Matrix.mul_sub, Matrix.sub_mul, hE.1, hAE'.1, hA'E.2, hA.2]; abel
  · simp only [Matrix.mul_sub, Matrix.sub_mul, hE.2, hA'E.1, hAE'.2, hA.1]; abel

/-- `E − A` lies in the complement of a part of `A`. -/
theorem nested_compl {A E L : Matrix (Fin 23) (Fin 23) ℚ} (hL : Nested L A) (hAE : Nested A E) :
    Nested (E - A) (1 - L) := by
  have hLE := hL.trans hAE
  constructor
  · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, hLE.2, hL.2]; abel
  · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hLE.1, hL.1]; abel

theorem nested_sub_self {A E : Matrix (Fin 23) (Fin 23) ℚ} (hAE : Nested A E) (hE : E * E = E) :
    Nested (E - A) E :=
  ⟨by rw [Matrix.mul_sub, hE, hAE.1], by rw [Matrix.sub_mul, hE, hAE.2]⟩

/-- A frame in `E` that `A` annihilates lies in `E − A`. -/
theorem nested_of_orth {A E F : Matrix (Fin 23) (Fin 23) ℚ} (hF : Nested F E) (h1 : A * F = 0)
    (h2 : F * A = 0) : Nested F (E - A) :=
  ⟨by rw [Matrix.sub_mul, hF.1, h1, sub_zero], by rw [Matrix.mul_sub, hF.2, h2, sub_zero]⟩

theorem nested_one {A : Matrix (Fin 23) (Fin 23) ℚ} : Nested A 1 :=
  ⟨Matrix.one_mul A, Matrix.mul_one A⟩

/-! ### Frames of one centre -/

/-- The output triples `{c, u, w}` of a pair mask. -/
abbrev liftSet (c M : ℕ) : Finset (Finset ℕ) := suppSet (.one c M)

/-- **The root-complement frame** of the outputs of `M` at `c`, and of the centre when `r`. -/
def liftFrame (c M : ℕ) (r : Bool) : Matrix (Fin 23) (Fin 23) ℚ :=
  (if r then starFrame c else 1) - frameOf (liftSet c M)

variable {c M : ℕ} (hc : c < 23) (hM : subB M (pairsWithout c) = true)
include hc hM

theorem liftSet_star : InStar (liftSet c M) c := instar (one_ok hc hM)

theorem lift_le_star : Nested (frameOf (liftSet c M)) (starFrame c) :=
  frameOf_nest (starSet_mem hc) (Submodule.span_le.mpr fun w hw =>
    Submodule.subset_span (by
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hw
      have h := (liftSet_star hc hM).2 S hS
      exact Finset.mem_image.mpr ⟨S, by simpa [starSet, mem_allTriples] using h, rfl⟩))

theorem liftFrame_idem (r : Bool) : liftFrame c M r * liftFrame c M r = liftFrame c M r := by
  have hA := frameOf_idem (liftSet_star hc hM)
  obtain ⟨h1, h2⟩ := lift_le_star hc hM
  cases r
  · simp only [liftFrame, Bool.false_eq_true, ite_false]
    exact Exchange.sub_idempotent _ _ hA (Matrix.one_mul 1) (Matrix.mul_one _) (Matrix.one_mul _)
  · simp only [liftFrame, ↓reduceIte]
    exact Exchange.sub_idempotent _ _ hA (frameOf_idem (starSet_mem hc)) h2 h1

/-- With the centre, the frame is the complement of the outputs and `w_c`. -/
theorem liftFrame_true :
    liftFrame c M true = 1 - proj formG (fromCols (basisMat (liftSet c M)) (wcol c)) := by
  have h := liftSet_star hc hM
  simp only [liftFrame, ↓reduceIte]
  rw [proj_fromCols (basis_gram_isUnit h) (wcol_gram_isUnit hc) (cross_wcol h), ← frameOf,
    ← centreLine, ← starFrame_add_centreLine hc]
  abel

theorem liftFrame_rank (hok : okC c M = true) (r : Bool) :
    (liftFrame c M r).rank = (if r then 22 else 23) - dimC c M := by
  have hA := frameOf_idem (liftSet_star hc hM)
  have hrA : (frameOf (liftSet c M)).rank = dimC c M :=
    suppFrame_rank (one_ok hc hM) (relP_one c M) hok
  obtain ⟨h1, h2⟩ := lift_le_star hc hM
  cases r
  · have h := Exchange.rank_sub_add _ 1 hA (Matrix.one_mul 1) (Matrix.mul_one _) (Matrix.one_mul _)
    rw [rank_one, Fintype.card_fin, hrA] at h
    simp only [liftFrame, Bool.false_eq_true, ite_false]
    omega
  · have h : (starFrame c - frameOf (liftSet c M)).rank + (frameOf (liftSet c M)).rank =
        (starFrame c).rank := Exchange.rank_sub_add _ _ hA (frameOf_idem (starSet_mem hc)) h2 h1
    rw [starFrame_rank hc, hrA] at h
    simp only [liftFrame, ↓reduceIte]
    omega

theorem liftFrame_mem {S : Finset ℕ} (hS : S ∈ liftSet c M) :
    ∃ u w, u < w ∧ w < 23 ∧ u ≠ c ∧ w ≠ c ∧ S = {c, u, w} ∧ M.testBit (pb u w) = true :=
  (mem_suppSet (one_ok hc hM)).mp hS

theorem mem_liftSet {u w : ℕ} (hu : u < 23) (hw : w < 23) (huc : u ≠ c) (hwc : w ≠ c)
    (huw : u ≠ w) (hbit : M.testBit (pb u w) = true) : ({c, u, w} : Finset ℕ) ∈ liftSet c M :=
  (mem_suppSet (one_ok hc hM)).mpr (pairIn_pair hu hw huc hwc huw hbit)

theorem lineFrame_le_lift {u w : ℕ} (hu : u < 23) (hw : w < 23) (huc : u ≠ c) (hwc : w ≠ c)
    (huw : u ≠ w) (hbit : M.testBit (pb u w) = true) :
    Nested (lineFrame {c, u, w}) (frameOf (liftSet c M)) :=
  frameOf_nest (liftSet_star hc hM) (Submodule.span_le.mpr fun v hv => Submodule.subset_span (by
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hv
    rw [Finset.mem_singleton.mp hS]
    exact Finset.mem_image.mpr ⟨_, mem_liftSet hc hM hu hw huc hwc huw hbit, rfl⟩))

theorem top_nested (r : Bool) :
    Nested (frameOf (liftSet c M)) (if r then starFrame c else 1) := by
  cases r
  · exact nested_one
  · exact lift_le_star hc hM

/-- **Hyperplanes.** The frame lies in the hyperplane of every output it reaches. -/
theorem liftFrame_hyper {u w : ℕ} (hu : u < 23) (hw : w < 23) (huc : u ≠ c) (hwc : w ≠ c)
    (huw : u ≠ w) (hbit : M.testBit (pb u w) = true) (r : Bool) :
    Nested (liftFrame c M r) (hyperFrame {c, u, w}) :=
  nested_compl (lineFrame_le_lift hc hM hu hw huc hwc huw hbit) (top_nested hc hM r)

/-- **The star.** With the centre, the frame lies in the star. -/
theorem liftFrame_star : Nested (liftFrame c M true) (starFrame c) := by
  simp only [liftFrame, ↓reduceIte]
  exact nested_sub_self (lift_le_star hc hM) (frameOf_idem (starSet_mem hc))

/-- **Triples orthogonal to the outputs.** Triples through `c` that meet every output of `M` in
one point span a space inside the frame. -/
theorem frameOf_lift {𝒮 : Finset (Finset ℕ)} (h𝒮 : ∀ S ∈ 𝒮, IsTriple S ∧ c ∈ S)
    (hmeet : ∀ S ∈ 𝒮, ∀ T ∈ liftSet c M, (S ∩ T).card = 1) (r : Bool) :
    Nested (frameOf 𝒮) (liftFrame c M r) := by
  have horth : ∀ S ∈ 𝒮, ∀ T ∈ liftSet c M, gform (tvec S) (tvec T) = 0 := by
    intro S hS T hT
    rw [gform_tvec (h𝒮 S hS).1 ((liftSet_star hc hM).2 T hT).1, hmeet S hS T hT]
    norm_num
  obtain ⟨h1, h2⟩ := frameOf_orth horth
  refine nested_of_orth ?_ h1 h2
  cases r
  · exact nested_one
  · exact frameOf_nest (starSet_mem hc) (Submodule.span_le.mpr fun v hv =>
      Submodule.subset_span (by
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hv
        exact Finset.mem_image.mpr ⟨S, by simpa [starSet, mem_allTriples] using h𝒮 S hS, rfl⟩))

/-- **Heights.** -/
theorem liftFrame_bounded (r : Bool) : Height.Bounded (liftFrame c M r) (2 * 10 ^ 200) := by
  have h := liftSet_star hc hM
  cases r
  · simp only [liftFrame, Bool.false_eq_true, ↓reduceIte, frameOf]
    rw [← basisMat_int]
    exact frame_compl_bounded (fun i a => by simp only [basisInt]; split_ifs <;> norm_num)
      (by rw [basisMat_int]; exact basis_gram_isUnit h)
  · have hcast : castQ (fromCols (basisInt (liftSet c M)) (wcolZ c)) =
        fromCols (basisMat (liftSet c M)) (wcol c) := by
      rw [castQ, fromCols_map, ← castQ, ← castQ, basisMat_int, wcolZ_cast]
    rw [liftFrame_true hc hM, ← hcast]
    refine frame_compl_bounded8 (fun i a => ?_) ?_
    · cases a with
      | inl a => simp only [fromCols_apply_inl, basisInt]; split_ifs <;> norm_num
      | inr a => simp only [fromCols_apply_inr, wcolZ]; split_ifs <;> norm_num
    · rw [hcast]
      exact fromCols_gram_isUnit (basis_gram_isUnit h) (wcol_gram_isUnit hc) (cross_wcol h)

/-- **Nesting.** A frame with fewer outputs, and no centre unless both reach it, is larger. -/
theorem liftFrame_nest {M' : ℕ} (hsub : subB M' M = true) {r r' : Bool} (hr : r' = true → r = true) :
    Nested (liftFrame c M r) (liftFrame c M' r') := by
  have hM' : subB M' (pairsWithout c) = true := by
    unfold subB at hsub hM ⊢
    rw [beq_iff] at hsub hM ⊢
    apply Nat.eq_of_testBit_eq
    intro i
    have e1 := congrArg (fun x => Nat.testBit x i) hsub
    have e2 := congrArg (fun x => Nat.testBit x i) hM
    simp only [show ∀ a b : ℕ, Nat.land a b = a &&& b from fun _ _ => rfl, Nat.testBit_land] at e1 e2 ⊢
    cases h1 : M'.testBit i <;> cases h2 : M.testBit i <;> simp_all
  have hA : Nested (frameOf (liftSet c M')) (frameOf (liftSet c M)) :=
    frameOf_nest (liftSet_star hc hM) (Submodule.span_le.mpr fun v hv => Submodule.subset_span (by
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨u, w, huw, hw, huc, hwc, rfl, hb⟩ := liftFrame_mem hc hM' hS
      exact Finset.mem_image.mpr ⟨_, mem_liftSet hc hM (by omega) hw huc hwc (by omega)
        (subB_spec hsub _ hb), rfl⟩))
  refine nested_sub hA (top_nested hc hM r) ?_
  cases r <;> cases r'
  · exact nested_one
  · exact absurd (hr rfl) (by simp)
  · exact nested_one
  · exact ⟨frameOf_idem (starSet_mem hc), frameOf_idem (starSet_mem hc)⟩

end

end IntegerMultBounds.MathlibTM2.M8.Frames
