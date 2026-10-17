module

public import IntegerMultBounds.Networks.Certificates.T16.BinaryElimination

/-! Exact lowering of a T16 frame transition to one coordinate `C^{⊗r}` child. Every exact
realization is, up to a global scalar, a monomial word, the source C gates on its first `r`
axes, another monomial word and a Pauli operator, where `r` is the rank of the X block of its
tableau. For the selected frame transitions `r` is the certified event rank. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Pauli
open Geometry BinaryPhase BinaryWalsh

/-! ### Realization tableaus are symplectic -/

/-- Shift a label's phase. -/
def Label.shift (p : Label) (k : ZMod 4) : Label := ⟨p.x, p.z, p.phase + k⟩

theorem operator_shift (p : Label) (k : ZMod 4) (f : State) :
    operator (p.shift k) f = BinaryPhase.phase k • operator p f := by
  funext y
  simp only [operator_apply, Label.shift, phase_add, Pi.smul_apply, smul_eq_mul]
  ring

theorem Realization.label_shift (A : Realization) (p : Label) (k : ZMod 4) :
    A.label (p.shift k) = (A.label p).shift k := by
  apply operator_injective
  apply LinearMap.ext
  intro f
  rw [← A.conjugates, operator_shift, map_smul, A.conjugates, operator_shift]

theorem doubleLift_add_self (a : F) : doubleLift a + doubleLift a = 0 := by
  rw [← map_add, CharTwo.add_self_eq_zero, map_zero]

theorem multiply_comm_shift (p q : Label) :
    multiply q p = (multiply p q).shift (doubleLift (symplecticPair p.binary q.binary)) := by
  apply Label.ext'
  · exact add_comm _ _
  · exact add_comm _ _
  · simp only [multiply, Label.shift, Label.binary, Tableau.symplecticPair_eq, map_add]
    rw [Tableau.dot_symm q.z p.x]
    have h := doubleLift_add_self (Tableau.dot p.z q.x)
    have e : q.phase + p.phase + doubleLift (Tableau.dot p.x q.z) =
        p.phase + q.phase + doubleLift (Tableau.dot p.z q.x) +
          (doubleLift (Tableau.dot p.x q.z) + doubleLift (Tableau.dot p.z q.x)) := by
      rw [add_comm (doubleLift (Tableau.dot p.x q.z)), ← add_assoc,
        add_assoc (p.phase + q.phase), h, add_zero, add_comm q.phase]
    exact e

theorem doubleLift_injective : Function.Injective (doubleLift : F → ZMod 4) := by
  decide

/-- The binary tableau of a realization preserves the doubled pairing. -/
theorem Realization.binary_symplectic (A : Realization) : Tableau.IsSymplectic A.binary := by
  intro v w
  let p : Label := ⟨v.1, v.2, 0⟩
  let q : Label := ⟨w.1, w.2, 0⟩
  have h := A.label_multiply q p
  rw [multiply_comm_shift p q, A.label_shift, A.label_multiply,
    multiply_comm_shift (A.label p) (A.label q)] at h
  have hph := congrArg Label.phase h
  simp only [Label.shift] at hph
  have hd := doubleLift_injective (add_left_cancel hph)
  rw [A.projects, A.projects] at hd
  exact hd.symm

/-! ### Inverse realizations -/

/-- A label whose image is `p`. -/
noncomputable def Realization.preLabel (A : Realization) (p : Label) : Label :=
  let v := A.binary.symm p.binary
  let q₀ : Label := ⟨v.1, v.2, 0⟩
  q₀.shift (p.phase - (A.label q₀).phase)

theorem Realization.label_preLabel (A : Realization) (p : Label) :
    A.label (A.preLabel p) = p := by
  unfold Realization.preLabel
  rw [A.label_shift]
  set q₀ : Label := ⟨(A.binary.symm p.binary).1, (A.binary.symm p.binary).2, 0⟩
  have hb : (A.label q₀).binary = p.binary := by
    rw [A.projects]
    exact A.binary.apply_symm_apply _
  apply Label.ext'
  · exact congrArg Prod.fst hb
  · exact congrArg Prod.snd hb
  · simp [Label.shift]

/-- The inverse of an exact realization. -/
noncomputable def Realization.symm (A : Realization) : Realization where
  scalar := A.scalar.symm
  label := A.preLabel
  binary := A.binary.symm
  projects p := rfl
  conjugates p f := by
    have h := A.conjugates (A.preLabel p) (A.scalar f)
    rw [LinearEquiv.symm_apply_apply, A.label_preLabel] at h
    rw [LinearEquiv.symm_symm, ← h, LinearEquiv.symm_apply_apply]

/-! ### Monomial gates from symmetric shears -/

/-- The exact matrix of a dot-symmetric shear. -/
noncomputable def shearMatrix (S : Geometry.Address →ₗ[F] Geometry.Address) : BinaryMatrix :=
  LinearMap.toMatrix' S

theorem shearMatrix_mulVecLin (S : Geometry.Address →ₗ[F] Geometry.Address) :
    (shearMatrix S).mulVecLin = S := by
  rw [shearMatrix, ← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']

theorem shearMatrix_symm {S : Geometry.Address →ₗ[F] Geometry.Address}
    (hS : Tableau.DotSymmetric S) (i j : Fin 9) : shearMatrix S i j = shearMatrix S j i := by
  have e : ∀ a b, shearMatrix S a b = Tableau.dot (Pi.single a 1) (S (Pi.single b 1)) := by
    intro a b
    rw [dot_single, shearMatrix, LinearMap.toMatrix'_apply]
  rw [e, e, ← hS, Tableau.dot_symm]

/-- The source diagonal gate of a symmetric shear, with default alpha. -/
noncomputable def shearRealization (S : Geometry.Address →ₗ[F] Geometry.Address)
    (hS : Tableau.DotSymmetric S) : Realization :=
  diagonalRealization (shearMatrix S) (defaultAlpha (shearMatrix S)) (shearMatrix_symm hS)
    (defaultAlpha_compatible _)

theorem shearRealization_binary (S : Geometry.Address →ₗ[F] Geometry.Address)
    (hS : Tableau.DotSymmetric S) : (shearRealization S hS).binary = Tableau.diagonal S := by
  change Tableau.diagonal (shearMatrix S).mulVecLin = _
  rw [shearMatrix_mulVecLin]

/-- A monomial: an address permutation followed by a quadratic diagonal. -/
noncomputable def monomialRealization (G : Geometry.Address ≃ₗ[F] Geometry.Address)
    (S : Geometry.Address →ₗ[F] Geometry.Address) (hS : Tableau.DotSymmetric S) : Realization :=
  (permutationRealization G).then (shearRealization S hS)

/-- The coordinate Hadamard word `S C_r S`. -/
noncomputable def hadamardRealization (r : ℕ) : Realization :=
  (shearRealization (Tableau.cut r) (Tableau.cut_symmetric r)).then
    ((partialCRealization r).then (shearRealization (Tableau.cut r) (Tableau.cut_symmetric r)))

theorem hadamardRealization_binary (r : ℕ) :
    (hadamardRealization r).binary = Tableau.hadamard r := by
  apply LinearEquiv.ext
  intro p
  change (shearRealization (Tableau.cut r) (Tableau.cut_symmetric r)).binary
    ((partialCRealization r).binary
      ((shearRealization (Tableau.cut r) (Tableau.cut_symmetric r)).binary p)) = _
  rw [shearRealization_binary, partialCRealization_binary]
  rfl

/-! ### Lowering -/

/-- **Lowering.** Every exact realization equals, up to a global scalar, a monomial, the source
C gates on its first `r` axes, a monomial and a Pauli operator, with `r = dim xRange`. -/
theorem Realization.lowering (K : Realization) :
    ∃ (A₂ G : Geometry.Address ≃ₗ[F] Geometry.Address)
      (S₂ S : Geometry.Address →ₗ[F] Geometry.Address)
      (hS₂ : Tableau.DotSymmetric S₂) (hS : Tableau.DotSymmetric S) (c : Label) (κ : ℂ),
      ∀ f, K.scalar f = κ • operator c
        (((monomialRealization A₂ S₂ hS₂).then
          ((hadamardRealization (Module.finrank F (Tableau.xRange K.binary))).then
            ((shearRealization S hS).then (permutationRealization G)))).scalar f) := by
  obtain ⟨G, A₂, S, S₂, hS, hS₂, hB⟩ := Tableau.elimination K.binary K.binary_symplectic
  set W := (monomialRealization A₂ S₂ hS₂).then
    ((hadamardRealization (Module.finrank F (Tableau.xRange K.binary))).then
      ((shearRealization S hS).then (permutationRealization G)))
  have hW : ∀ p, K.binary p = W.binary p := by
    intro p
    rw [hB]
    change _ = (permutationRealization G).binary ((shearRealization S hS).binary
      ((hadamardRealization _).binary ((shearRealization S₂ hS₂).binary
        ((permutationRealization A₂).binary p))))
    rw [shearRealization_binary, shearRealization_binary, hadamardRealization_binary]
    rfl
  obtain ⟨c, κ, h⟩ := K.eq_pauli_smul W hW
  exact ⟨A₂, G, S₂, S, hS₂, hS, c, κ, h⟩

/-! ### The selected frame transitions -/

/-- The exact physical transition from selected frame `a` to selected frame `b`. -/
noncomputable def edgeRealization (a b : ℕ) : Realization :=
  (nativeRealization a).symm.then (nativeRealization b)

theorem edgeRealization_binary (a b : ℕ) :
    (edgeRealization a b).binary = Tableau.relative (Tableau.nativeTableau a)
      (Tableau.nativeTableau b) := by
  apply LinearEquiv.ext
  intro p
  change (nativeRealization b).binary ((nativeRealization a).binary.symm p) = _
  rw [nativeRealization_binary, nativeRealization_binary]
  rfl

/-- The lowering width of a selected transition is the actual relative X-block rank. -/
theorem edgeRealization_width (a b : ℕ) :
    Module.finrank F (Tableau.xRange (edgeRealization a b).binary) =
      Module.finrank F (LinearMap.range
        (Tableau.bBlock (Tableau.nativeTableau a) (Tableau.nativeTableau b))) := by
  rw [edgeRealization_binary]
  rfl

/-- **Every selected frame transition is one `C^{⊗r}` child between monomials.** With `r` the
relative X-block rank, which `Tableau.native_forward_climb` and its companions identify with the
certified event rank, the exact transition from frame `a` to frame `b` is, up to a global scalar,
a monomial, the source coordinate Hadamard `S C_r S`, a monomial and a Pauli operator. -/
theorem edge_lowering {a b r : ℕ}
    (hr : Module.finrank F (LinearMap.range
      (Tableau.bBlock (Tableau.nativeTableau a) (Tableau.nativeTableau b))) = r) :
    ∃ (A₂ G : Geometry.Address ≃ₗ[F] Geometry.Address)
      (S₂ S : Geometry.Address →ₗ[F] Geometry.Address)
      (hS₂ : Tableau.DotSymmetric S₂) (hS : Tableau.DotSymmetric S) (c : Label) (κ : ℂ),
      ∀ f, (edgeRealization a b).scalar f = κ • operator c
        (((monomialRealization A₂ S₂ hS₂).then
          ((hadamardRealization r).then
            ((shearRealization S hS).then (permutationRealization G)))).scalar f) := by
  have h := (edgeRealization a b).lowering
  rw [edgeRealization_width, hr] at h
  exact h

end IntegerMultBounds.Networks.Certificates.T16.Pauli
