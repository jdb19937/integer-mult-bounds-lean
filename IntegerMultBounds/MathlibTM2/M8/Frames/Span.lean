module

public import IntegerMultBounds.MathlibTM2.M8.Frames.ProjectorHeight
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Span frames

A triple `S` of points below `23` is the vector `tvec S ∈ ℚ²³`. The form `G = 1 − J/9` gives
`gform (tvec S) (tvec S') = |S ∩ S'| − 1` for triples. On the star of a point `c`, the span of
the triples through `c`, the form is `Σ_{i ≠ c} v_i²` (`gform_self_star`), so it is positive
definite there (`gform_pos_star`).

`frameOf 𝒮` is the `G`-orthogonal projector onto the span of the triples of `𝒮`, computed from a
basis chosen among them (`basisMat`). For `𝒮` inside a star the Gram matrix of the basis is
invertible (`basis_gram_isUnit`), so:
* `frameOf 𝒮` is idempotent, and nested spans give nested frames (`frameOf_nest`);
* frames of `G`-orthogonal sets annihilate each other (`frameOf_orth`);
* its entries have height at most `10 ^ 200` (`frameOf_bounded`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Frames

open Matrix Finset

noncomputable section

/-- The vector of a set of points: `1` on the points below `23`. -/
def tvec (S : Finset ℕ) : Fin 23 → ℚ := fun i => if i.val ∈ S then 1 else 0

/-- The form `G(v, w) = vᵀ G w`. -/
def gform (v w : Fin 23 → ℚ) : ℚ := v ⬝ᵥ (formG *ᵥ w)

theorem formG_apply (i j : Fin 23) : formG i j = if i = j then 8 / 9 else -1 / 9 := by
  rw [formG, Matrix.smul_apply, castQ, Matrix.map_apply]
  unfold gram9
  split_ifs <;> simp <;> norm_num

theorem formG_mulVec (w : Fin 23 → ℚ) (i : Fin 23) :
    (formG *ᵥ w) i = w i - (∑ j, w j) / 9 := by
  simp only [mulVec, dotProduct, formG_apply]
  have h : ∀ j, (if i = j then (8 / 9 : ℚ) else -1 / 9) * w j =
      (if i = j then w j else 0) - w j / 9 := fun j => by split_ifs <;> ring
  rw [Finset.sum_congr rfl fun j _ => h j]
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul]

theorem gform_eq (v w : Fin 23 → ℚ) :
    gform v w = v ⬝ᵥ w - (∑ i, v i) * (∑ i, w i) / 9 := by
  simp only [gform, dotProduct, formG_mulVec, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

theorem gform_comm (v w : Fin 23 → ℚ) : gform v w = gform w v := by
  rw [gform_eq, gform_eq, dotProduct_comm, mul_comm (∑ i, v i)]

theorem formG_transpose : formGᵀ = formG := by
  ext i j
  rw [transpose_apply, formG_apply, formG_apply]
  by_cases h : i = j <;> simp [h, eq_comm]

/-- The Gram entries are form values of the columns. -/
theorem gram_apply {κ κ' : Type*} [Fintype κ] (B1 : Matrix (Fin 23) κ ℚ) (B2 : Matrix (Fin 23) κ' ℚ)
    (b : κ) (a : κ') : (B1ᵀ * formG * B2) b a = gform (fun i => B1 i b) (fun i => B2 i a) := by
  simp only [mul_apply, transpose_apply, gform, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

/-! ### Triples and stars -/

/-- A triple of points below `23`. -/
def IsTriple (S : Finset ℕ) : Prop := S.card = 3 ∧ ∀ z ∈ S, z < 23

theorem sum_tvec {S : Finset ℕ} (hS : ∀ z ∈ S, z < 23) : ∑ i, tvec S i = S.card := by
  simp only [tvec]
  rw [Finset.sum_boole]
  congr 1
  rw [← Finset.card_map ⟨Fin.val, Fin.val_injective⟩]
  congr 1
  ext z
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact hi
  · intro hz; exact ⟨⟨z, hS z hz⟩, hz, rfl⟩

/-- The star of `c`: the span of the triples through `c`. -/
def starSpace (c : ℕ) : Submodule ℚ (Fin 23 → ℚ) :=
  Submodule.span ℚ (tvec '' {S | IsTriple S ∧ c ∈ S})

/-- On the star of `c`, the coordinate sum is three times the coordinate at `c`. -/
theorem sum_eq_of_mem_star {c : ℕ} (hc : c < 23) {v : Fin 23 → ℚ} (hv : v ∈ starSpace c) :
    ∑ i, v i = 3 * v ⟨c, hc⟩ := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨S, ⟨⟨h3, h23⟩, hcS⟩, rfl⟩ := hx
    rw [sum_tvec h23, h3]
    simp [tvec, hcS]
  | zero => simp
  | add x y _ _ hx hy => simp only [Pi.add_apply, Finset.sum_add_distrib, hx, hy]; ring
  | smul a x _ hx => simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hx]; ring

theorem gform_self_star {c : ℕ} (hc : c < 23) {v : Fin 23 → ℚ} (hv : v ∈ starSpace c) :
    gform v v = ∑ i ∈ Finset.univ.erase ⟨c, hc⟩, v i ^ 2 := by
  rw [gform_eq, sum_eq_of_mem_star hc hv, dotProduct, ← Finset.add_sum_erase _ _
    (Finset.mem_univ ⟨c, hc⟩)]
  simp only [sq]
  ring

theorem gform_pos_star {c : ℕ} (hc : c < 23) {v : Fin 23 → ℚ} (hv : v ∈ starSpace c)
    (hne : v ≠ 0) : 0 < gform v v := by
  rw [gform_self_star hc hv]
  apply lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _)
  intro h0
  apply hne
  have hz : ∀ i ∈ Finset.univ.erase (⟨c, hc⟩ : Fin 23), v i = 0 := by
    intro i hi
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (v i)).mp h0.symm i hi
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have hsum := sum_eq_of_mem_star hc hv
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨c, hc⟩), Finset.sum_eq_zero hz,
    add_zero] at hsum
  have hvc : v ⟨c, hc⟩ = 0 := by linarith
  funext i
  by_cases hi : i = ⟨c, hc⟩
  · rw [hi, hvc]; rfl
  · exact hz i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩)

/-- Columns in a star with independent columns have an invertible Gram matrix. -/
theorem gram_isUnit {κ : Type*} [Fintype κ] [DecidableEq κ] {c : ℕ} (hc : c < 23)
    {B : Matrix (Fin 23) κ ℚ} (hcol : ∀ a, (fun i => B i a) ∈ starSpace c)
    (hind : LinearIndependent ℚ fun a => fun i => B i a) : IsUnit (Bᵀ * formG * B).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨a, ha, hBa⟩ := exists_mulVec_eq_zero_iff.mpr h0
  have hmem : B *ᵥ a ∈ starSpace c := by
    have : B *ᵥ a = ∑ k, a k • fun i => B i k := by
      funext i; simp [mulVec, dotProduct, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hcol k)
  have hzero : gform (B *ᵥ a) (B *ᵥ a) = 0 := by
    have key : a ⬝ᵥ ((Bᵀ * formG * B) *ᵥ a) = gform (B *ᵥ a) (B *ᵥ a) := by
      rw [gform, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    rw [← key, hBa, dotProduct_zero]
  by_cases hB : B *ᵥ a = 0
  · apply ha
    have : ∑ k, a k • (fun i => B i k) = 0 := by
      rw [← hB]; funext i; simp [mulVec, dotProduct, mul_comm]
    exact funext fun k => (Fintype.linearIndependent_iff.mp hind) a this k
  · exact absurd hzero (gform_pos_star hc hmem hB).ne'

/-! ### The frame of a set of triples -/

/-- The vectors of the triples of `𝒮`. -/
def vecs (𝒮 : Finset (Finset ℕ)) : Finset (Fin 23 → ℚ) := 𝒮.image tvec

theorem exists_basis (𝒮 : Finset (Finset ℕ)) :
    ∃ b : Finset (Fin 23 → ℚ), b ⊆ vecs 𝒮 ∧
      Submodule.span ℚ (b : Set (Fin 23 → ℚ)) = Submodule.span ℚ (vecs 𝒮 : Set (Fin 23 → ℚ)) ∧
      LinearIndependent ℚ ((↑) : b → Fin 23 → ℚ) := by
  obtain ⟨b, hb, hspan, hind⟩ := exists_linearIndependent ℚ (vecs 𝒮 : Set (Fin 23 → ℚ))
  have hfin : b.Finite := (vecs 𝒮).finite_toSet.subset hb
  refine ⟨hfin.toFinset, by simpa using hb, by simpa using hspan, ?_⟩
  have := hind.comp _ (Equiv.subtypeEquivRight (p := fun x => x ∈ hfin.toFinset)
    (q := fun x => x ∈ b) (fun x => by simp)).injective
  exact this

/-- A basis of the span, chosen among the triples. -/
def basisOf (𝒮 : Finset (Finset ℕ)) : Finset (Fin 23 → ℚ) := Classical.choose (exists_basis 𝒮)

theorem basisOf_sub (𝒮 : Finset (Finset ℕ)) : basisOf 𝒮 ⊆ vecs 𝒮 :=
  (Classical.choose_spec (exists_basis 𝒮)).1

theorem basisOf_span (𝒮 : Finset (Finset ℕ)) :
    Submodule.span ℚ (basisOf 𝒮 : Set (Fin 23 → ℚ)) = Submodule.span ℚ (vecs 𝒮 : Set _) :=
  (Classical.choose_spec (exists_basis 𝒮)).2.1

theorem basisOf_ind (𝒮 : Finset (Finset ℕ)) :
    LinearIndependent ℚ ((↑) : basisOf 𝒮 → Fin 23 → ℚ) :=
  (Classical.choose_spec (exists_basis 𝒮)).2.2

/-- The basis as the columns of a matrix. -/
def basisMat (𝒮 : Finset (Finset ℕ)) : Matrix (Fin 23) (basisOf 𝒮) ℚ := fun i a => a.1 i

/-- The `G`-orthogonal projector onto the span of the triples of `𝒮`. -/
def frameOf (𝒮 : Finset (Finset ℕ)) : Matrix (Fin 23) (Fin 23) ℚ := proj formG (basisMat 𝒮)

/-- All triples of `𝒮` pass through `c`. -/
def InStar (𝒮 : Finset (Finset ℕ)) (c : ℕ) : Prop := c < 23 ∧ ∀ S ∈ 𝒮, IsTriple S ∧ c ∈ S

theorem vecs_star {𝒮 : Finset (Finset ℕ)} {c : ℕ} (h : InStar 𝒮 c) :
    ∀ w ∈ vecs 𝒮, w ∈ starSpace c := by
  intro w hw
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hw
  exact Submodule.subset_span ⟨S, h.2 S hS, rfl⟩

theorem basis_gram_isUnit {𝒮 : Finset (Finset ℕ)} {c : ℕ} (h : InStar 𝒮 c) :
    IsUnit ((basisMat 𝒮)ᵀ * formG * basisMat 𝒮).det :=
  gram_isUnit h.1 (fun a => vecs_star h a.1 (basisOf_sub 𝒮 a.2)) (basisOf_ind 𝒮)

theorem frameOf_idem {𝒮 : Finset (Finset ℕ)} {c : ℕ} (h : InStar 𝒮 c) :
    frameOf 𝒮 * frameOf 𝒮 = frameOf 𝒮 :=
  proj_idem (basis_gram_isUnit h)

theorem frameOf_rank {𝒮 : Finset (Finset ℕ)} {c : ℕ} (h : InStar 𝒮 c) :
    (frameOf 𝒮).rank = (basisOf 𝒮).card := by
  rw [frameOf, proj_rank (basis_gram_isUnit h), Fintype.card_coe]

/-- A vector in a span is a combination of the basis columns. -/
theorem col_mem_span {𝒮 : Finset (Finset ℕ)} {w : Fin 23 → ℚ}
    (hw : w ∈ Submodule.span ℚ (vecs 𝒮 : Set (Fin 23 → ℚ))) :
    ∃ a : basisOf 𝒮 → ℚ, w = basisMat 𝒮 *ᵥ a := by
  rw [← basisOf_span, show ((basisOf 𝒮 : Finset (Fin 23 → ℚ)) : Set (Fin 23 → ℚ)) =
    Set.range ((↑) : basisOf 𝒮 → Fin 23 → ℚ) by simp] at hw
  obtain ⟨a, ha⟩ := Submodule.mem_span_range_iff_exists_fun ℚ |>.mp hw
  refine ⟨a, ?_⟩
  rw [← ha]
  funext i
  simp [basisMat, mulVec, dotProduct, Finset.sum_apply, mul_comm]

/-- The basis of a smaller span factors through the basis of a larger one. -/
theorem basisMat_factor {𝒮 𝒯 : Finset (Finset ℕ)}
    (hle : Submodule.span ℚ (vecs 𝒮 : Set (Fin 23 → ℚ)) ≤
      Submodule.span ℚ (vecs 𝒯 : Set (Fin 23 → ℚ))) :
    ∃ C : Matrix (basisOf 𝒯) (basisOf 𝒮) ℚ, basisMat 𝒮 = basisMat 𝒯 * C := by
  have hcol : ∀ b : basisOf 𝒮, ∃ a : basisOf 𝒯 → ℚ, b.1 = basisMat 𝒯 *ᵥ a := fun b =>
    col_mem_span (hle (Submodule.subset_span (basisOf_sub 𝒮 b.2)))
  choose a ha using hcol
  refine ⟨fun k b => a b k, ?_⟩
  ext i b
  have := congrFun (ha b) i
  simp only [basisMat, mulVec, dotProduct] at this
  simp only [basisMat]
  exact this

/-- **Nesting.** A span inside another gives a frame inside the other's. -/
theorem frameOf_nest {𝒮 𝒯 : Finset (Finset ℕ)} {d : ℕ} (hT : InStar 𝒯 d)
    (hle : Submodule.span ℚ (vecs 𝒮 : Set (Fin 23 → ℚ)) ≤
      Submodule.span ℚ (vecs 𝒯 : Set (Fin 23 → ℚ))) :
    frameOf 𝒯 * frameOf 𝒮 = frameOf 𝒮 ∧ frameOf 𝒮 * frameOf 𝒯 = frameOf 𝒮 := by
  obtain ⟨C, hC⟩ := basisMat_factor hle
  exact ⟨proj_nest_left (basis_gram_isUnit hT) hC, proj_nest_right (basis_gram_isUnit hT) hC⟩

theorem frameOf_eq {𝒮 𝒯 : Finset (Finset ℕ)} {c d : ℕ} (hS : InStar 𝒮 c) (hT : InStar 𝒯 d)
    (heq : Submodule.span ℚ (vecs 𝒮 : Set (Fin 23 → ℚ)) =
      Submodule.span ℚ (vecs 𝒯 : Set (Fin 23 → ℚ))) : frameOf 𝒮 = frameOf 𝒯 := by
  have h1 := frameOf_nest hT heq.le
  have h2 := frameOf_nest hS heq.ge
  rw [← h1.2, h2.1]

/-- **Orthogonal frames.** Frames of `G`-orthogonal triples annihilate each other. -/
theorem frameOf_orth {𝒮 𝒯 : Finset (Finset ℕ)}
    (horth : ∀ S ∈ 𝒮, ∀ T ∈ 𝒯, gform (tvec S) (tvec T) = 0) :
    frameOf 𝒯 * frameOf 𝒮 = 0 ∧ frameOf 𝒮 * frameOf 𝒯 = 0 := by
  have hcross : ∀ (a : basisOf 𝒮) (b : basisOf 𝒯), gform a.1 b.1 = 0 := by
    intro a b
    obtain ⟨S, hS, ha⟩ := Finset.mem_image.mp (basisOf_sub 𝒮 a.2)
    obtain ⟨T, hT, hb⟩ := Finset.mem_image.mp (basisOf_sub 𝒯 b.2)
    rw [← ha, ← hb]
    exact horth S hS T hT
  have hz : (basisMat 𝒯)ᵀ * formG * basisMat 𝒮 = 0 := by
    ext b a
    rw [gram_apply, Matrix.zero_apply, gform_comm]
    exact hcross a b
  have hz' : (basisMat 𝒮)ᵀ * formG * basisMat 𝒯 = 0 := by
    have := congrArg Matrix.transpose hz
    rwa [transpose_mul, transpose_mul, transpose_transpose, formG_transpose, transpose_zero,
      ← Matrix.mul_assoc] at this
  constructor
  · rw [frameOf, frameOf, proj, proj]
    rw [show basisMat 𝒯 * ((basisMat 𝒯)ᵀ * formG * basisMat 𝒯)⁻¹ * (basisMat 𝒯)ᵀ * formG *
        (basisMat 𝒮 * ((basisMat 𝒮)ᵀ * formG * basisMat 𝒮)⁻¹ * (basisMat 𝒮)ᵀ * formG) =
        basisMat 𝒯 * ((basisMat 𝒯)ᵀ * formG * basisMat 𝒯)⁻¹ *
          ((basisMat 𝒯)ᵀ * formG * basisMat 𝒮) *
          (((basisMat 𝒮)ᵀ * formG * basisMat 𝒮)⁻¹ * (basisMat 𝒮)ᵀ * formG) by
      simp only [Matrix.mul_assoc], hz, Matrix.mul_zero, Matrix.zero_mul]
  · rw [frameOf, frameOf, proj, proj]
    rw [show basisMat 𝒮 * ((basisMat 𝒮)ᵀ * formG * basisMat 𝒮)⁻¹ * (basisMat 𝒮)ᵀ * formG *
        (basisMat 𝒯 * ((basisMat 𝒯)ᵀ * formG * basisMat 𝒯)⁻¹ * (basisMat 𝒯)ᵀ * formG) =
        basisMat 𝒮 * ((basisMat 𝒮)ᵀ * formG * basisMat 𝒮)⁻¹ *
          ((basisMat 𝒮)ᵀ * formG * basisMat 𝒯) *
          (((basisMat 𝒯)ᵀ * formG * basisMat 𝒯)⁻¹ * (basisMat 𝒯)ᵀ * formG) by
      simp only [Matrix.mul_assoc], hz', Matrix.mul_zero, Matrix.zero_mul]

/-! ### Heights -/

/-- The basis as an integer `0/1` matrix. -/
def basisInt (𝒮 : Finset (Finset ℕ)) : Matrix (Fin 23) (basisOf 𝒮) ℤ :=
  fun i a => if a.1 i = 1 then 1 else 0

theorem basisMat_int (𝒮 : Finset (Finset ℕ)) : castQ (basisInt 𝒮) = basisMat 𝒮 := by
  ext i a
  obtain ⟨S, -, ha⟩ := Finset.mem_image.mp (basisOf_sub 𝒮 a.2)
  simp only [castQ, basisInt, basisMat, map_apply]
  rw [← ha]
  by_cases h : i.val ∈ S <;> simp [tvec, h]

theorem frameOf_bounded {𝒮 : Finset (Finset ℕ)} {c : ℕ} (h : InStar 𝒮 c) :
    Height.Bounded (frameOf 𝒮) (10 ^ 200) := by
  have hB := basis_gram_isUnit h
  rw [← basisMat_int] at hB
  rw [frameOf, ← basisMat_int]
  exact frame_bounded (fun i a => by simp only [basisInt]; split_ifs <;> norm_num) hB

end

end IntegerMultBounds.MathlibTM2.M8.Frames
