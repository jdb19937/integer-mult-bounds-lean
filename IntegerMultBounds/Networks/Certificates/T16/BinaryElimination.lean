module

public import IntegerMultBounds.Networks.Certificates.T16.PauliCorrection

/-! Binary Clifford elimination. Every symplectic map on the doubled nine-bit address space
factors as a monomial, a coordinate Hadamard on as many axes as the rank of its X block,
and another monomial. Monomials are address permutations followed by quadratic diagonals; the
coordinate Hadamard is the source's `S C_r S`. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Tableau
open Geometry

/-! ### Symplectic maps -/

theorem symplecticPair_eq (p q : PhaseAddress) :
    symplecticPair p q = dot p.1 q.2 + dot p.2 q.1 := rfl

theorem dot_apply (a b : Address) : dot a b = ∑ i, a i * b i := by
  simp [dot, Labels.binary, Labels.form_apply]

theorem cut_apply (r : ℕ) (x : Address) (i : Fin 9) :
    cut r x i = if i.val < r then x i else 0 := rfl

/-- Preservation of the doubled pairing. -/
def IsSymplectic (M : PhaseAddress ≃ₗ[F] PhaseAddress) : Prop :=
  ∀ v w, symplecticPair (M v) (M w) = symplecticPair v w

theorem IsSymplectic.trans {M N : PhaseAddress ≃ₗ[F] PhaseAddress} (hM : IsSymplectic M)
    (hN : IsSymplectic N) : IsSymplectic (M.trans N) :=
  fun v w => (hN (M v) (M w)).trans (hM v w)

theorem IsSymplectic.symm {M : PhaseAddress ≃ₗ[F] PhaseAddress} (hM : IsSymplectic M) :
    IsSymplectic M.symm := fun v w => by
  rw [← hM, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem dot_eq_zero_of_forall {x : Address} (h : ∀ y, dot x y = 0) : x = 0 :=
  Labels.binary_nondegenerate.1 x h

theorem dot_ext {a b : Address} (h : ∀ y, dot a y = dot b y) : a = b := by
  have := dot_eq_zero_of_forall (x := a - b) (fun y => by
    rw [map_sub, LinearMap.sub_apply, h, sub_self])
  exact sub_eq_zero.mp this

theorem eq_of_add_eq_zero {a b : F} (h : a + b = 0) : a = b := by
  rw [← sub_eq_zero, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  exact h

/-- Symmetry for the binary dot product. -/
def DotSymmetric (S : Address →ₗ[F] Address) : Prop := ∀ x y, dot (S x) y = dot x (S y)

theorem perm_symplectic (G : Address ≃ₗ[F] Address) : IsSymplectic (perm G) := by
  intro v w
  change dot (G v.1) ((transpose G).symm w.2) + dot ((transpose G).symm v.2) (G w.1) = _
  rw [dot_symm (G v.1), Pauli.dot_transpose_symm, Pauli.dot_transpose_symm,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, dot_symm w.2]
  rfl

theorem diagonal_symplectic {S : Address →ₗ[F] Address} (hS : DotSymmetric S) :
    IsSymplectic (diagonal S) := by
  intro v w
  change dot v.1 (w.2 + S w.1) + dot (v.2 + S v.1) w.1 = dot v.1 w.2 + dot v.2 w.1
  rw [map_add, map_add, LinearMap.add_apply, hS]
  generalize dot v.1 w.2 = a
  generalize dot v.2 w.1 = b
  generalize dot v.1 (S w.1) = t
  revert a b t
  decide

theorem cut_symmetric (r : ℕ) : DotSymmetric (cut r) := cut_dot r

theorem partialC_symplectic (r : ℕ) : IsSymplectic (partialC r) := by
  intro v w
  change dot (v.1 + cut r v.2) w.2 + dot v.2 (w.1 + cut r w.2) = dot v.1 w.2 + dot v.2 w.1
  rw [map_add, map_add, LinearMap.add_apply, cut_dot]
  generalize dot v.1 w.2 = a
  generalize dot v.2 w.1 = b
  generalize dot v.2 (cut r w.2) = t
  revert a b t
  decide

/-- The coordinate Hadamard on the first `r` axes, `S C_r S` with `S = diag(cut r)`. -/
def hadamard (r : ℕ) : PhaseAddress ≃ₗ[F] PhaseAddress :=
  (diagonal (cut r)).trans ((partialC r).trans (diagonal (cut r)))

theorem hadamard_Z (r : ℕ) (z : Address) : hadamard r (0, z) = (cut r z, z + cut r z) := by
  simp [hadamard, diagonal, partialC, cut_idem]

theorem hadamard_symplectic (r : ℕ) : IsSymplectic (hadamard r) :=
  (diagonal_symplectic (cut_symmetric r)).trans
    ((partialC_symplectic r).trans (diagonal_symplectic (cut_symmetric r)))

/-! ### Z-preserving symplectic maps are monomial -/

theorem monomial_of_preserves (M : PhaseAddress ≃ₗ[F] PhaseAddress) (hM : IsSymplectic M)
    (hZ : ∀ z, (M (0, z)).1 = 0) :
    ∃ (A : Address ≃ₗ[F] Address) (S : Address →ₗ[F] Address), DotSymmetric S ∧
      M = (perm A).trans (diagonal S) := by
  let fA : Address →ₗ[F] Address :=
    (LinearMap.fst F Address Address).comp (M.toLinearMap.comp (LinearMap.inl F Address Address))
  let C : Address →ₗ[F] Address :=
    (LinearMap.snd F Address Address).comp (M.toLinearMap.comp (LinearMap.inl F Address Address))
  let D : Address →ₗ[F] Address :=
    (LinearMap.snd F Address Address).comp (M.toLinearMap.comp (LinearMap.inr F Address Address))
  have hpair : ∀ x z, dot (fA x) (D z) = dot x z := by
    intro x z
    have h := hM (x, 0) (0, z)
    rw [symplecticPair_eq, symplecticPair_eq, hZ z] at h
    exact (by simpa using h : dot (M (x, 0)).1 (M (0, z)).2 = dot x z)
  have hinj : Function.Injective fA := by
    intro x x' h
    rw [← sub_eq_zero]
    apply dot_eq_zero_of_forall
    intro z
    rw [← hpair, map_sub, h, sub_self, map_zero, LinearMap.zero_apply]
  let A := LinearEquiv.ofInjectiveEndo fA hinj
  have hA : ∀ x, A x = fA x := fun _ => rfl
  have hD : ∀ z, D z = (transpose A).symm z := by
    intro z
    apply (transpose A).injective
    rw [LinearEquiv.apply_symm_apply]
    apply dot_ext
    intro y
    rw [transpose_dot, dot_symm, hA, hpair, dot_symm]
  let S : Address →ₗ[F] Address := C.comp A.symm.toLinearMap
  have hS : DotSymmetric S := by
    intro x y
    have h := hM (A.symm x, 0) (A.symm y, 0)
    rw [symplecticPair_eq, symplecticPair_eq] at h
    simp only [map_zero, LinearMap.zero_apply, add_zero] at h
    change dot (fA (A.symm x)) (C (A.symm y)) + dot (C (A.symm x)) (fA (A.symm y)) = 0 at h
    rw [← hA, ← hA, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    exact (eq_of_add_eq_zero h).symm
  refine ⟨A, S, hS, ?_⟩
  apply LinearEquiv.ext
  rintro ⟨x, z⟩
  have hsplit : M (x, z) = M (x, 0) + M (0, z) := by rw [← map_add]; simp
  rw [hsplit]
  change (fA x + (M (0, z)).1, C x + D z) = ((perm A).trans (diagonal S)) (x, z)
  rw [hZ, hD]
  change (fA x + 0, C x + (transpose A).symm z) = (A x, (transpose A).symm z + C (A.symm (A x)))
  rw [add_zero, LinearEquiv.symm_apply_apply, add_comm, hA]

/-! ### Basis extension -/

theorem frameSpace_eq_span {r : ℕ} (hr : r ≤ 9) (G : Address ≃ₗ[F] Address)
    (v : Fin r → Address) (hv : ∀ i, G (Pi.single (Fin.castLE hr i) 1) = v i) :
    frameSpace G r = Submodule.span F (Set.range v) := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    change G (cut r a) ∈ _
    rw [← (Pi.basisFun F (Fin 9)).sum_repr a]
    simp only [map_sum, map_smul]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    rw [Pi.basisFun_apply, cut_single]
    split_ifs with hi
    · have hc := hv ⟨i.val, hi⟩
      have he : Fin.castLE hr ⟨i.val, hi⟩ = i := Fin.ext rfl
      rw [he] at hc
      rw [hc]
      exact Submodule.subset_span ⟨⟨i.val, hi⟩, rfl⟩
    · simp
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single (Fin.castLE hr i) 1, ?_⟩
    change G (cut r (Pi.single (Fin.castLE hr i) 1)) = _
    simpa [cut_single, i.isLt] using hv i

theorem finrank_address : Module.finrank F Address = 9 := by simp [Address]

/-- Every subspace is the frame space of some invertible address matrix. -/
theorem exists_frameSpace_eq (U : Submodule F Address) :
    ∃ G : Address ≃ₗ[F] Address, frameSpace G (Module.finrank F U) = U := by
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl U
  set r := Module.finrank F U
  let bU : Module.Basis (Fin r) F U := Module.finBasisOfFinrankEq F U rfl
  let bW : Module.Basis (Fin (Module.finrank F W)) F W := Module.finBasis F W
  have hdim : r + Module.finrank F W = 9 := by
    rw [Submodule.finrank_add_eq_of_isCompl hW, finrank_address]
  let b : Module.Basis (Fin r ⊕ Fin (Module.finrank F W)) F Address :=
    (bU.prod bW).map (Submodule.prodEquivOfIsCompl U W hW)
  let b' : Module.Basis (Fin 9) F Address :=
    b.reindex (finSumFinEquiv.trans (finCongr hdim))
  have hr : r ≤ 9 := by omega
  have hb' : ∀ i : Fin r, b' (Fin.castLE hr i) = bU i := by
    intro i
    have e : (finSumFinEquiv.trans (finCongr hdim)).symm (Fin.castLE hr i) = Sum.inl i := by
      apply (finSumFinEquiv.trans (finCongr hdim)).injective
      rw [Equiv.apply_symm_apply]
      ext
      simp
    simp only [b', Module.Basis.reindex_apply, e, b, Module.Basis.map_apply]
    simp [Submodule.coe_prodEquivOfIsCompl']
  let G := (Pi.basisFun F (Fin 9)).equiv b' (Equiv.refl _)
  refine ⟨G, ?_⟩
  rw [frameSpace_eq_span hr G (fun i => (bU i : Address))]
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (bU i).property
    · intro u hu
      have := bU.sum_repr ⟨u, hu⟩
      have hu' : u = ∑ i, bU.repr ⟨u, hu⟩ i • (bU i : Address) := by
        have h2 := congrArg Subtype.val this
        rw [Submodule.coe_sum] at h2
        simp only [Submodule.coe_smul] at h2
        exact h2.symm
      rw [hu']
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro i
    rw [← hb' i]
    have := (Pi.basisFun F (Fin 9)).equiv_apply (b' := b') (Fin.castLE hr i) (Equiv.refl _)
    simpa [Pi.basisFun_apply] using this

/-! ### Elimination -/

/-- The X-projection of the image of the standard Z generators. -/
def xRange (B : PhaseAddress ≃ₗ[F] PhaseAddress) : Submodule F Address :=
  LinearMap.range ((LinearMap.fst F Address Address).comp (B.toLinearMap.comp zEmbed))

/-- **Binary elimination.** A symplectic map is a monomial, then the coordinate Hadamard on
`dim xRange` axes, then another monomial (the source's `then` order, left applied first). -/
theorem elimination (B : PhaseAddress ≃ₗ[F] PhaseAddress) (hB : IsSymplectic B) :
    ∃ (G A₂ : Address ≃ₗ[F] Address) (S S₂ : Address →ₗ[F] Address),
      DotSymmetric S ∧ DotSymmetric S₂ ∧
      B = ((perm A₂).trans (diagonal S₂)).trans
        ((hadamard (Module.finrank F (xRange B))).trans ((diagonal S).trans (perm G))) := by
  set r := Module.finrank F (xRange B)
  obtain ⟨G, hG⟩ := exists_frameSpace_eq (xRange B)
  let X : Address →ₗ[F] Address := G.symm.toLinearMap.comp
    ((LinearMap.fst F Address Address).comp (B.toLinearMap.comp zEmbed))
  let W : Address →ₗ[F] Address := (transpose G).toLinearMap.comp
    ((LinearMap.snd F Address Address).comp (B.toLinearMap.comp zEmbed))
  have hXW : ∀ z, (perm G).symm (B (0, z)) = (X z, W z) := fun _ => rfl
  have hXcut : ∀ z, cut r (X z) = X z := by
    intro z
    have hm : (B (0, z)).1 ∈ frameSpace G r := by rw [hG]; exact ⟨z, rfl⟩
    exact (mem_frameSpace G r _).mp hm
  have hsurj : ∀ j : Fin 9, ∃ z, j.val < r → X z = Pi.single j 1 := by
    intro j
    by_cases hj : j.val < r
    · have hm : G (Pi.single j 1) ∈ xRange B := by
        rw [← hG]
        refine ⟨Pi.single j 1, ?_⟩
        change G (cut r (Pi.single j 1)) = _
        rw [cut_single]
        simp [hj]
      obtain ⟨z, hz⟩ := hm
      refine ⟨z, fun _ => ?_⟩
      change G.symm (B (0, z)).1 = _
      change (B (0, z)).1 = _ at hz
      rw [hz, LinearEquiv.symm_apply_apply]
    · exact ⟨0, fun h => absurd h hj⟩
  choose zj hzj using hsurj
  let w : Fin 9 → Address := fun j => W (zj j)
  have hC : IsSymplectic (B.trans (perm G).symm) := hB.trans (perm_symplectic G).symm
  have hiso : ∀ z z', dot (X z) (W z') + dot (W z) (X z') = 0 := by
    intro z z'
    have h := hC (0, z) (0, z')
    change symplecticPair ((perm G).symm (B (0, z))) ((perm G).symm (B (0, z'))) = _ at h
    rw [hXW, hXW, symplecticPair_eq, symplecticPair_eq] at h
    simpa using h
  have hw : ∀ i j : Fin 9, i.val < r → j.val < r → w j i = w i j := by
    intro i j hi hj
    have h := hiso (zj i) (zj j)
    rw [hzj i hi, hzj j hj, Pauli.dot_single, dot_symm, Pauli.dot_single] at h
    exact eq_of_add_eq_zero h
  -- the symmetric correction
  let S : Address →ₗ[F] Address :=
    ∑ j, ((LinearMap.proj j).comp (cut r)).smulRight (cut r (w j))
  have hSapp : ∀ x, S x = ∑ j, cut r x j • cut r (w j) := by
    intro x
    simp [S, LinearMap.sum_apply]
  have hSsymm : DotSymmetric S := by
    intro x y
    rw [dot_apply, dot_apply]
    simp only [hSapp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [cut_apply]
    by_cases hi : i.val < r <;> by_cases hj : j.val < r <;> simp [hi, hj]
    rw [hw j i hj hi]
    ring
  -- every Z image is reached from the standard Hadamard Lagrangian
  have hkey : ∀ z, ∃ z', diagonal S (hadamard r (0, z')) = (X z, W z) := by
    intro z
    set x := X z
    let zs := ∑ j, x j • zj j
    have hxc : cut r x = x := hXcut z
    have hXzs : X zs = x := by
      simp only [zs, map_sum, map_smul]
      calc ∑ j, x j • X (zj j) = ∑ j, x j • (Pi.single j 1 : Address) := by
            apply Finset.sum_congr rfl
            intro j _
            by_cases hj : j.val < r
            · rw [hzj j hj]
            · have hx0 : x j = 0 := by
                have := congrFun hxc j
                simp only [cut_apply, hj] at this
                exact this.symm
              rw [hx0, zero_smul, zero_smul]
        _ = x := by
            ext i
            simp [Finset.sum_apply, Pi.single_apply]
    have hWzs : W zs = ∑ j, x j • w j := by simp [zs, w, map_sum, map_smul]
    set y := W (z + zs)
    have hX0 : X (z + zs) = 0 := by rw [map_add, hXzs, Tableau.address_add_self]
    have hy : cut r y = 0 := by
      ext i
      rw [cut_apply]
      split_ifs with hi
      · have h := hiso (z + zs) (zj i)
        rw [hX0, map_zero, LinearMap.zero_apply, zero_add, hzj i hi, dot_symm,
          Pauli.dot_single] at h
        change (W (z + zs)) i = 0
        simpa [map_add] using h
      · rfl
    have hSx : S x = ∑ j, x j • cut r (w j) := by
      rw [hSapp, hxc]
    have hcut : cut r (W z + S x) = 0 := by
      have e : W z + S x = y + ∑ j, x j • (w j + cut r (w j)) := by
        simp only [y, map_add, hWzs, hSx, smul_add, Finset.sum_add_distrib]
        rw [add_assoc, ← add_assoc (∑ j, x j • w j), Tableau.address_add_self, zero_add]
      rw [e, map_add, hy, zero_add, map_sum]
      apply Finset.sum_eq_zero
      intro j _
      rw [map_smul, map_add, cut_idem, Tableau.address_add_self, smul_zero]
    refine ⟨x + (W z + S x), ?_⟩
    have hc : cut r (x + (W z + S x)) = x := by rw [map_add, hcut, add_zero, hxc]
    rw [hadamard_Z, hc]
    change (x, x + (W z + S x) + x + S x) = (x, W z)
    congr 1
    funext i
    simp only [Pi.add_apply]
    generalize x i = a
    generalize W z i = b
    generalize S x i = c
    revert a b c
    decide
  -- the remaining map preserves the Z generators
  obtain ⟨N, hNdef⟩ : ∃ N, N = (hadamard r).trans ((diagonal S).trans (perm G)) := ⟨_, rfl⟩
  have hN : IsSymplectic N := hNdef ▸
    (hadamard_symplectic r).trans ((diagonal_symplectic hSsymm).trans (perm_symplectic G))
  have hM2 : ∀ z, ((B.trans N.symm) (0, z)).1 = 0 := by
    intro z
    obtain ⟨z', hz'⟩ := hkey z
    have hNz : N (0, z') = B (0, z) := by
      rw [hNdef]
      change perm G (diagonal S (hadamard r (0, z'))) = _
      rw [hz', ← hXW, LinearEquiv.apply_symm_apply]
    change (N.symm (B (0, z))).1 = 0
    rw [← hNz, LinearEquiv.symm_apply_apply]
  obtain ⟨A₂, S₂, hS₂, hM⟩ := monomial_of_preserves _ (hB.trans hN.symm) hM2
  refine ⟨G, A₂, S, S₂, hSsymm, hS₂, ?_⟩
  have hBN : B = (B.trans N.symm).trans N := by
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [hBN, hM, hNdef]

end IntegerMultBounds.Networks.Certificates.T16.Tableau
