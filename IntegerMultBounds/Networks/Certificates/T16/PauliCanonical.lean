module

public import IntegerMultBounds.Networks.Certificates.T16.PauliInverse
public import IntegerMultBounds.Networks.Certificates.T16.TableauNative

/-! The source's canonical Clifford word `K C_r K⁻¹`, assembled from the proved C, P and D
realizations. Its binary projection is exactly `canonical`, its three-branch form is exactly
`sourceCanonical`, and at every selected frame it is exactly `nativeTableau`. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Pauli
open Geometry BinaryPhase BinaryWalsh

/-- A word's binary projection applies its letters left to right. -/
theorem realizeWord_binary (gs : List Realization) (p : PhaseAddress) :
    (realizeWord gs).binary p = gs.foldl (fun acc g => g.binary acc) p := by
  induction gs generalizing p with
  | nil => rfl
  | cons g gs ih =>
    change (realizeWord gs).binary (g.binary p) = _
    rw [ih]
    rfl

/-! ### The partial-C word -/

/-- The source C gates on axes `0, …, r-1`, in increasing order. -/
noncomputable def cWord : ℕ → List Realization
  | 0 => []
  | k + 1 => cWord k ++ if h : k < 9 then [cRealization (Pi.single ⟨k, h⟩ 1)] else []

theorem dot_single (i : Fin 9) (z : Geometry.Address) : Tableau.dot (Pi.single i 1) z = z i := by
  simp [Tableau.dot, Labels.binary, Labels.form_apply, Pi.single_apply]

theorem cut_succ (k : ℕ) (z : Geometry.Address) :
    Tableau.cut (k + 1) z = Tableau.cut k z +
      if h : k < 9 then z ⟨k, h⟩ • Pi.single ⟨k, h⟩ 1 else 0 := by
  ext j
  have e : ∀ r, Tableau.cut r z j = if j.val < r then z j else 0 := fun _ => rfl
  rw [Pi.add_apply, e, e]
  by_cases h : k < 9
  · simp only [h, ↓reduceDIte]
    by_cases hj : j = ⟨k, h⟩
    · subst hj
      simp
    · have hjk : j.val ≠ k := fun e => hj (Fin.ext e)
      simp only [Pi.smul_apply, Pi.single_apply, hj, ite_false, smul_zero, add_zero]
      by_cases hjl : j.val < k
      · simp [hjl, show j.val < k + 1 by omega]
      · simp [hjl, show ¬ j.val < k + 1 by omega]
  · simp only [h, ↓reduceDIte]
    have hj : j.val < k := by omega
    simp [hj, show j.val < k + 1 by omega]

theorem cWord_binary (r : ℕ) (p : PhaseAddress) :
    (cWord r).foldl (fun acc g => g.binary acc) p = Tableau.partialC r p := by
  induction r with
  | zero =>
    change p = (p.1 + Tableau.cut 0 p.2, p.2)
    rw [Tableau.cut_zero, add_zero]
  | succ k ih =>
    rw [cWord, List.foldl_append, ih]
    change _ = (p.1 + Tableau.cut (k + 1) p.2, p.2)
    rw [cut_succ]
    split_ifs with h
    · change (p.1 + Tableau.cut k p.2 + Tableau.dot (Pi.single ⟨k, h⟩ 1) p.2 • Pi.single ⟨k, h⟩ 1,
        p.2) = _
      rw [dot_single, add_assoc]
    · change (p.1 + Tableau.cut k p.2, p.2) = _
      rw [add_zero]

/-- The partial-C word as one realization. -/
noncomputable def partialCRealization (r : ℕ) : Realization := realizeWord (cWord r)

theorem partialCRealization_binary (r : ℕ) :
    (partialCRealization r).binary = Tableau.partialC r := by
  apply LinearEquiv.ext
  intro p
  rw [partialCRealization, realizeWord_binary, cWord_binary]

/-! ### The conjugator `K = D_Q P_G` -/

theorem dot_transpose_symm (G : Geometry.Address ≃ₗ[F] Geometry.Address) (u y : Geometry.Address) :
    Tableau.dot ((Tableau.transpose G).symm u) y = Tableau.dot u (G.symm y) := by
  have h := Tableau.transpose_dot G ((Tableau.transpose G).symm u) (G.symm y)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- `Q = I + G⁻ᵀ G⁻¹` is symmetric for the binary dot product. -/
theorem quadratic_dot (G : Geometry.Address ≃ₗ[F] Geometry.Address) (x y : Geometry.Address) :
    Tableau.dot (Tableau.quadratic G x) y = Tableau.dot x (Tableau.quadratic G y) := by
  simp only [Tableau.quadratic, LinearMap.add_apply, LinearMap.id_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, map_add, LinearMap.add_apply]
  rw [dot_transpose_symm, Tableau.dot_symm x ((Tableau.transpose G).symm (G.symm y)),
    dot_transpose_symm, Tableau.dot_symm (G.symm x)]

/-- The exact quadratic matrix of the conjugator. -/
noncomputable def quadraticMatrix (G : Geometry.Address ≃ₗ[F] Geometry.Address) : BinaryMatrix :=
  LinearMap.toMatrix' (Tableau.quadratic G)

theorem quadraticMatrix_mulVecLin (G : Geometry.Address ≃ₗ[F] Geometry.Address) :
    (quadraticMatrix G).mulVecLin = Tableau.quadratic G := by
  rw [quadraticMatrix, ← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']

theorem quadraticMatrix_entry (G : Geometry.Address ≃ₗ[F] Geometry.Address) (i j : Fin 9) :
    quadraticMatrix G i j = Tableau.dot (Pi.single i 1) (Tableau.quadratic G (Pi.single j 1)) := by
  rw [dot_single, quadraticMatrix, LinearMap.toMatrix'_apply]

theorem quadraticMatrix_symm (G : Geometry.Address ≃ₗ[F] Geometry.Address) (i j : Fin 9) :
    quadraticMatrix G i j = quadraticMatrix G j i := by
  rw [quadraticMatrix_entry, quadraticMatrix_entry, ← quadratic_dot, Tableau.dot_symm]

/-- The diagonal gate of the conjugator, with the source's default alpha. -/
noncomputable def conjugatorDiagonal (G : Geometry.Address ≃ₗ[F] Geometry.Address) : Realization :=
  diagonalRealization (quadraticMatrix G) (defaultAlpha (quadraticMatrix G))
    (quadraticMatrix_symm G) (defaultAlpha_compatible _)

noncomputable def conjugatorDiagonalInverse (G : Geometry.Address ≃ₗ[F] Geometry.Address) :
    Realization :=
  diagonalInverseRealization (quadraticMatrix G) (defaultAlpha (quadraticMatrix G))
    (quadraticMatrix_symm G) (defaultAlpha_compatible _)

theorem diagonal_symm (Q : Geometry.Address →ₗ[F] Geometry.Address) :
    (Tableau.diagonal Q).symm = Tableau.diagonal Q := by
  apply LinearEquiv.ext
  intro p
  change (p.1, p.2 - Q p.1) = (p.1, p.2 + Q p.1)
  congr 1
  ext i
  change p.2 i - Q p.1 i = p.2 i + Q p.1 i
  rw [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

/-- `K⁻¹`, `C_r` and `K`, in the source's application order. -/
noncomputable def canonicalWord (G : Geometry.Address ≃ₗ[F] Geometry.Address) (r : ℕ) :
    List Realization :=
  [conjugatorDiagonalInverse G, permutationInverseRealization G] ++ cWord r ++
    [permutationRealization G, conjugatorDiagonal G]

noncomputable def canonicalRealization (G : Geometry.Address ≃ₗ[F] Geometry.Address) (r : ℕ) :
    Realization :=
  realizeWord (canonicalWord G r)

theorem canonicalRealization_binary (G : Geometry.Address ≃ₗ[F] Geometry.Address) (r : ℕ) :
    (canonicalRealization G r).binary = Tableau.canonical G r := by
  apply LinearEquiv.ext
  intro p
  rw [canonicalRealization, realizeWord_binary, canonicalWord, List.foldl_append,
    List.foldl_append, cWord_binary]
  change Tableau.diagonal (quadraticMatrix G).mulVecLin (Tableau.perm G
      (Tableau.partialC r ((Tableau.perm G).symm
        (Tableau.diagonal (quadraticMatrix G).mulVecLin p)))) = _
  rw [quadraticMatrix_mulVecLin]
  change _ = Tableau.diagonal (Tableau.quadratic G) (Tableau.perm G
      (Tableau.partialC r ((Tableau.perm G).symm
        ((Tableau.diagonal (Tableau.quadratic G)).symm p))))
  rw [diagonal_symm]

/-! ### The source branches and the selected native tableaus -/

/-- All three branches of the source `canonical_frame`, as complex realizations. -/
noncomputable def sourceCanonicalRealization (G : Geometry.Address ≃ₗ[F] Geometry.Address)
    (r : ℕ) : Realization :=
  if r = 0 then Realization.identity
  else if r = 9 then partialCRealization 9 else canonicalRealization G r

theorem sourceCanonicalRealization_binary (G : Geometry.Address ≃ₗ[F] Geometry.Address)
    (r : ℕ) : (sourceCanonicalRealization G r).binary = Tableau.sourceCanonical G r := by
  unfold sourceCanonicalRealization Tableau.sourceCanonical
  split_ifs
  · rfl
  · exact partialCRealization_binary 9
  · exact canonicalRealization_binary G r

/-- The complex realization of selected frame `i`. -/
noncomputable def nativeRealization (i : ℕ) : Realization :=
  sourceCanonicalRealization (Tableau.catalogExtension i).matrix (catalog i).data.rank

theorem nativeRealization_binary (i : ℕ) :
    (nativeRealization i).binary = Tableau.nativeTableau i :=
  sourceCanonicalRealization_binary _ _

end IntegerMultBounds.Networks.Certificates.T16.Pauli
