module

public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Combinatorics.Nullstellensatz
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# A common generic basis with bounded entries

Stage 2 needs one rational basis in which every residual projector `P_j` of rank `r_j` has
nonzero leading principal minors of sizes `1, …, r_j`. A basis chosen by `Classical.choose` would
have no height bound, so the prime could not be chosen to avoid its numerators and denominators.
`exists_generic_basis` gives a basis with natural entries at most `degreeBound m r`, which depends
only on the size `m` and the ranks.

For a matrix of variables `X`, the leading minors of `X P adj(X)` and `det X` are polynomials in
the entries of `X` of total degree at most `i (m + 1)` and `m` (`totalDegree_minorPoly`,
`totalDegree_det_X`). Each minor polynomial is nonzero when some basis makes that projector
generic (`minorPoly_ne_zero`), since `g P adj(g) = det g • g P g⁻¹` (`minor_adjugate`). The
combinatorial Nullstellensatz (`combinatorial_nullstellensatz_exists_eval_nonzero`) then gives a
point with natural coordinates at most the total degree of their product where none of them
vanishes.

Every idempotent `P` is generic up to its rank in a basis adapted to its range and kernel
(`exists_generic_of_idempotent`), so one bounded basis serves any finite family of idempotents
(`exists_generic_basis_of_idempotent`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.GenericBasis

noncomputable section
open MvPolynomial Matrix

variable {m : ℕ}

/-- The leading principal minor of size `i`. -/
def minor {R : Type*} [CommRing R] (A : Matrix (Fin m) (Fin m) R) (i : Fin (m + 1)) : R :=
  (A.submatrix (Fin.castLE (Nat.lt_succ_iff.mp i.isLt)) (Fin.castLE (Nat.lt_succ_iff.mp i.isLt))).det

/-- The sizes `1, …, r` of the leading minors that must not vanish. -/
def sizes (r : ℕ) : Finset (Fin (m + 1)) := Finset.univ.filter fun i => 1 ≤ i.val ∧ i.val ≤ r

/-- Every leading principal minor of sizes `1, …, r` is nonzero. -/
def Generic (A : Matrix (Fin m) (Fin m) ℚ) (r : ℕ) : Prop := ∀ i ∈ sizes (m := m) r, minor A i ≠ 0

theorem minor_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A : Matrix (Fin m) (Fin m) R) (i : Fin (m + 1)) : f (minor A i) = minor (f.mapMatrix A) i := by
  rw [minor, RingHom.map_det]
  rfl

theorem minor_smul (c : ℚ) (A : Matrix (Fin m) (Fin m) ℚ) (i : Fin (m + 1)) :
    minor (c • A) i = c ^ i.val * minor A i := by
  have h : (c • A).submatrix (Fin.castLE (Nat.lt_succ_iff.mp i.isLt)) (Fin.castLE (Nat.lt_succ_iff.mp i.isLt)) =
      c • A.submatrix (Fin.castLE (Nat.lt_succ_iff.mp i.isLt)) (Fin.castLE (Nat.lt_succ_iff.mp i.isLt)) := by
    ext
    simp
  rw [minor, h, det_smul, Fintype.card_fin]
  rfl

/-- With an invertible basis, `g P adj(g)` is `det g • g P g⁻¹`. -/
theorem minor_adjugate (g P : Matrix (Fin m) (Fin m) ℚ) (hg : g.det ≠ 0) (i : Fin (m + 1)) :
    minor (g * P * adjugate g) i = g.det ^ i.val * minor (g * P * g⁻¹) i := by
  have hadj : adjugate g = g.det • g⁻¹ := by
    rw [inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hg, one_smul]
  rw [hadj, Matrix.mul_smul, minor_smul]

/-! ### Polynomials in the entries of the basis -/

/-- The variables: one per entry of the basis. -/
abbrev Var (m : ℕ) := Fin m × Fin m

/-- The matrix of variables. -/
abbrev X : Matrix (Fin m) (Fin m) (MvPolynomial (Var m) ℚ) := mvPolynomialX (Fin m) (Fin m) ℚ

/-- `X P adj(X)`, the conjugate of `P` up to the scalar `det X`. -/
def conj (P : Matrix (Fin m) (Fin m) ℚ) : Matrix (Fin m) (Fin m) (MvPolynomial (Var m) ℚ) :=
  X * P.map C * adjugate X

/-- The leading minor of `X P adj(X)` of size `i`. -/
def minorPoly (P : Matrix (Fin m) (Fin m) ℚ) (i : Fin (m + 1)) : MvPolynomial (Var m) ℚ :=
  minor (conj P) i

/-- The point of a basis. -/
def point (g : Matrix (Fin m) (Fin m) ℚ) : Var m → ℚ := fun p => g p.1 p.2

theorem mapMatrix_X (g : Matrix (Fin m) (Fin m) ℚ) : (eval (point g)).mapMatrix X = g :=
  mvPolynomialX_mapMatrix_eval g

theorem eval_conj (P g : Matrix (Fin m) (Fin m) ℚ) :
    (eval (point g)).mapMatrix (conj P) = g * P * adjugate g := by
  have hP : (eval (point g)).mapMatrix (P.map C) = P := by
    ext a b
    simp
  rw [conj, map_mul, map_mul, RingHom.map_adjugate, mapMatrix_X, hP]

theorem eval_minorPoly (P g : Matrix (Fin m) (Fin m) ℚ) (i : Fin (m + 1)) :
    eval (point g) (minorPoly P i) = minor (g * P * adjugate g) i := by
  rw [minorPoly, minor_map, eval_conj]

theorem eval_det_X (g : Matrix (Fin m) (Fin m) ℚ) : eval (point g) (X (m := m)).det = g.det := by
  rw [RingHom.map_det, mapMatrix_X]

/-- A minor polynomial is nonzero when some basis makes the projector generic. -/
theorem minorPoly_ne_zero {P g : Matrix (Fin m) (Fin m) ℚ} {r : ℕ} (hg : g.det ≠ 0)
    (hgen : Generic (g * P * g⁻¹) r) {i : Fin (m + 1)} (hi : i ∈ sizes r) : minorPoly P i ≠ 0 := by
  intro h
  have he := eval_minorPoly P g i
  rw [h, map_zero, minor_adjugate g P hg] at he
  exact mul_ne_zero (pow_ne_zero _ hg) (hgen i hi) he.symm

/-! ### Degrees -/

theorem totalDegree_det_le {n : ℕ} (M : Matrix (Fin n) (Fin n) (MvPolynomial (Var m) ℚ)) (d : ℕ)
    (h : ∀ a b, (M a b).totalDegree ≤ d) : M.det.totalDegree ≤ n * d := by
  rw [det_apply]
  apply totalDegree_finsetSum_le
  intro σ _
  refine (totalDegree_smul_le _ _).trans ?_
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i, (M (σ i) i).totalDegree ≤ ∑ _i : Fin n, d := Finset.sum_le_sum fun i _ => h _ _
    _ = n * d := by simp

theorem totalDegree_X_entry (a b : Fin m) : ((X (m := m)) a b).totalDegree ≤ 1 := by
  show ((mvPolynomialX (Fin m) (Fin m) ℚ) a b).totalDegree ≤ 1
  rw [mvPolynomialX_apply, MvPolynomial.totalDegree_X]

theorem totalDegree_det_X : (X (m := m)).det.totalDegree ≤ m := by
  simpa using totalDegree_det_le (X (m := m)) 1 totalDegree_X_entry

theorem totalDegree_adjugate (a b : Fin m) : (adjugate (X (m := m)) a b).totalDegree ≤ m := by
  rw [adjugate_apply]
  have h := totalDegree_det_le ((X (m := m)).updateRow b (Pi.single a 1)) 1 (by
    intro c e
    by_cases hc : c = b
    · subst hc
      rw [updateRow_self]
      by_cases he : e = a
      · subst he
        simp
      · simp [he]
    · rw [updateRow_ne hc]
      exact totalDegree_X_entry c e)
  simpa using h

theorem totalDegree_conj (P : Matrix (Fin m) (Fin m) ℚ) (a b : Fin m) :
    (conj P a b).totalDegree ≤ m + 1 := by
  rw [conj, mul_apply]
  apply totalDegree_finsetSum_le
  intro l _
  refine (totalDegree_mul _ _).trans ?_
  have h1 : ((X (m := m) * P.map C : Matrix (Fin m) (Fin m) (MvPolynomial (Var m) ℚ)) a l).totalDegree ≤ 1 := by
    rw [mul_apply]
    apply totalDegree_finsetSum_le
    intro k _
    refine (totalDegree_mul _ _).trans ?_
    simp [totalDegree_C]
  have h2 := totalDegree_adjugate l b
  omega

theorem totalDegree_minorPoly (P : Matrix (Fin m) (Fin m) ℚ) (i : Fin (m + 1)) :
    (minorPoly P i).totalDegree ≤ i.val * (m + 1) :=
  totalDegree_det_le _ _ fun _ _ => totalDegree_conj P _ _

/-! ### The common basis -/

/-- The bound of the entries of the common basis. -/
def degreeBound {J : ℕ} (m : ℕ) (r : Fin J → ℕ) : ℕ :=
  m + ∑ j, ∑ i ∈ sizes (m := m) (r j), i.val * (m + 1)

/-- The product of `det X` and every minor polynomial. -/
def poly {J : ℕ} (P : Fin J → Matrix (Fin m) (Fin m) ℚ) (r : Fin J → ℕ) : MvPolynomial (Var m) ℚ :=
  (X (m := m)).det * ∏ j, ∏ i ∈ sizes (r j), minorPoly (P j) i

theorem totalDegree_poly {J : ℕ} (P : Fin J → Matrix (Fin m) (Fin m) ℚ) (r : Fin J → ℕ) :
    (poly P r).totalDegree ≤ degreeBound m r := by
  rw [poly, degreeBound]
  refine (totalDegree_mul _ _).trans (Nat.add_le_add totalDegree_det_X ?_)
  refine (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact totalDegree_minorPoly (P j) i

/-- One basis with natural entries at most `degreeBound m r` makes every projector generic. -/
theorem exists_generic_basis {J : ℕ} (P : Fin J → Matrix (Fin m) (Fin m) ℚ) (r : Fin J → ℕ)
    (hw : ∀ j, ∃ g : Matrix (Fin m) (Fin m) ℚ, g.det ≠ 0 ∧ Generic (g * P j * g⁻¹) (r j)) :
    ∃ g : Matrix (Fin m) (Fin m) ℕ, (∀ a b, g a b ≤ degreeBound m r) ∧
      (g.map (Nat.cast : ℕ → ℚ)).det ≠ 0 ∧
      ∀ j, Generic (g.map (Nat.cast : ℕ → ℚ) * P j * (g.map (Nat.cast : ℕ → ℚ))⁻¹) (r j) := by
  classical
  have hF : poly P r ≠ 0 := by
    refine mul_ne_zero (det_mvPolynomialX_ne_zero (Fin m) ℚ) ?_
    refine Finset.prod_ne_zero_iff.mpr fun j _ => Finset.prod_ne_zero_iff.mpr fun i hi => ?_
    obtain ⟨g, hg, hgen⟩ := hw j
    exact minorPoly_ne_zero hg hgen hi
  obtain ⟨t, ht, hdeg⟩ := Finset.exists_mem_eq_sup (poly P r).support
    (Finset.nonempty_of_ne_empty (by simpa using hF)) fun s => s.sum fun _ e => e
  have htd : (poly P r).totalDegree = t.degree := hdeg
  let S : Var m → Finset ℚ := fun p => (Finset.range (t p + 1)).image (Nat.cast : ℕ → ℚ)
  have hS : ∀ p, t p < (S p).card := by
    intro p
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
    omega
  obtain ⟨s, hs, hne⟩ := combinatorial_nullstellensatz_exists_eval_nonzero (poly P r) t
    (mem_support_iff.mp ht) htd S hS
  have hk : ∀ p, ∃ k : ℕ, k ≤ t p ∧ (k : ℚ) = s p := by
    intro p
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp (hs p)
    exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), he⟩
  choose k hkt hks using hk
  refine ⟨Matrix.of fun a b => k (a, b), ?_, ?_⟩
  · intro a b
    have h1 : t (a, b) ≤ t.degree := by
      rw [Finsupp.degree_eq_sum]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    have h2 := totalDegree_poly P r
    have h3 := hkt (a, b)
    simp only [of_apply]
    omega
  · set G := (Matrix.of fun a b => k (a, b)).map (Nat.cast : ℕ → ℚ) with hG
    have hpt : point G = s := by
      funext p
      simp [point, hG, hks]
    rw [← hpt, poly, map_mul, eval_det_X, map_prod] at hne
    have hdet : G.det ≠ 0 := left_ne_zero_of_mul hne
    refine ⟨hdet, fun j i hi => ?_⟩
    have hj := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hne) j (Finset.mem_univ _)
    rw [map_prod] at hj
    have hm := Finset.prod_ne_zero_iff.mp hj i hi
    rw [eval_minorPoly, minor_adjugate G (P j) hdet] at hm
    exact right_ne_zero_of_mul hm

/-! ### Idempotents -/

/-- The leading block of `1` up to size `r` has all its leading minors equal to `1`. -/
theorem minor_eq_one {A : Matrix (Fin m) (Fin m) ℚ} {r : ℕ}
    (hA : ∀ a b : Fin m, b.val < r → A a b = if a = b then 1 else 0) {i : Fin (m + 1)}
    (hi : i.val ≤ r) : minor A i = 1 := by
  have h : A.submatrix (Fin.castLE (Nat.lt_succ_iff.mp i.isLt)) (Fin.castLE (Nat.lt_succ_iff.mp i.isLt)) = 1 := by
    ext a b
    rw [submatrix_apply, hA _ _ (lt_of_lt_of_le (by simp) hi), one_apply]
    simp only [Fin.castLE_inj]
  rw [minor, h, det_one]

/-- An idempotent is generic up to its rank in a basis adapted to its range and kernel. -/
theorem exists_generic_of_idempotent (P : Matrix (Fin m) (Fin m) ℚ) (hP : IsIdempotentElem P) :
    ∃ g : Matrix (Fin m) (Fin m) ℚ, g.det ≠ 0 ∧ Generic (g * P * g⁻¹) P.rank := by
  classical
  set f := Matrix.toLin' P with hfdef
  have hf : IsIdempotentElem f := by
    change (Matrix.toLin' P).comp (Matrix.toLin' P) = Matrix.toLin' P
    rw [← Matrix.toLin'_mul, hP.eq]
  have h := LinearMap.IsIdempotentElem.isCompl hf
  let br := Module.finBasis ℚ (LinearMap.range f)
  let bk := Module.finBasis ℚ (LinearMap.ker f)
  have hcard : Module.finrank ℚ (LinearMap.range f) + Module.finrank ℚ (LinearMap.ker f) = m := by
    simpa using Submodule.finrank_add_eq_of_isCompl h
  let b : Module.Basis (Fin m) ℚ (Fin m → ℚ) :=
    ((br.prod bk).map (Submodule.prodEquivOfIsCompl _ _ h)).reindex
      (finSumFinEquiv.trans (finCongr hcard))
  have hrank : P.rank = Module.finrank ℚ (LinearMap.range f) := rfl
  have hrange : ∀ y : Fin m, y.val < Module.finrank ℚ (LinearMap.range f) → f (b y) = b y := by
    intro y hy
    have hy' : (finSumFinEquiv.trans (finCongr hcard)).symm y = Sum.inl ⟨y.val, hy⟩ := by
      apply (finSumFinEquiv.trans (finCongr hcard)).injective
      simp only [Equiv.apply_symm_apply, Equiv.trans_apply, finSumFinEquiv_apply_left]
      ext
      simp
    have hb : b y = (br ⟨y.val, hy⟩ : Fin m → ℚ) := by
      simp only [b, Module.Basis.reindex_apply, hy', Module.Basis.map_apply, Module.Basis.prod_apply,
        Sum.elim_inl, Function.comp_apply, LinearMap.coe_inl]
      simp [Submodule.coe_prodEquivOfIsCompl']
    rw [hb]
    exact (LinearMap.IsIdempotentElem.mem_range_iff hf).mp (br ⟨y.val, hy⟩).2
  let e := Pi.basisFun ℚ (Fin m)
  have hP' : LinearMap.toMatrix e e f = P := by
    rw [LinearMap.toMatrix_eq_toMatrix', hfdef, LinearMap.toMatrix'_toLin']
  have hN : b.toMatrix e * P * e.toMatrix b = LinearMap.toMatrix b b f := by
    rw [← hP']
    exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b e b e f
  have hinv : (b.toMatrix e)⁻¹ = e.toMatrix b :=
    Matrix.inv_eq_right_inv (Module.Basis.toMatrix_mul_toMatrix_flip b e)
  have hdet : (b.toMatrix e).det ≠ 0 := by
    intro h0
    have h1 := congrArg det (Module.Basis.toMatrix_mul_toMatrix_flip b e)
    rw [det_mul, h0, zero_mul, det_one] at h1
    exact zero_ne_one h1
  refine ⟨b.toMatrix e, hdet, ?_⟩
  rw [hinv, hN, hrank]
  intro i hi
  have hi' := (Finset.mem_filter.mp hi).2
  rw [minor_eq_one _ hi'.2]
  · exact one_ne_zero
  · intro a y hy
    rw [LinearMap.toMatrix_apply, hrange y hy, Module.Basis.repr_self, Finsupp.single_apply]
    simp only [eq_comm]

/-- One basis with natural entries at most `degreeBound m (rank ∘ P)` makes every idempotent of
a finite family generic up to its rank. -/
theorem exists_generic_basis_of_idempotent {J : ℕ} (P : Fin J → Matrix (Fin m) (Fin m) ℚ)
    (hP : ∀ j, IsIdempotentElem (P j)) :
    ∃ g : Matrix (Fin m) (Fin m) ℕ, (∀ a b, g a b ≤ degreeBound m fun j => (P j).rank) ∧
      (g.map (Nat.cast : ℕ → ℚ)).det ≠ 0 ∧
      ∀ j, Generic (g.map (Nat.cast : ℕ → ℚ) * P j * (g.map (Nat.cast : ℕ → ℚ))⁻¹) (P j).rank :=
  exists_generic_basis P (fun j => (P j).rank) fun j => exists_generic_of_idempotent (P j) (hP j)

end
end IntegerMultBounds.MathlibTM2.M8.GenericBasis
