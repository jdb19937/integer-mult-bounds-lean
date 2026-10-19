module

public import IntegerMultBounds.Networks.Certificates.T16.TableauCertificate
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Invertible extensions of the selected frames, completed from their certified independence.
Only the retained columns are specified; the other basis vectors are an arbitrary completion,
which the inverse-Z and relative-rank theorems never inspect. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Tableau
open Geometry

theorem sumExtend_inl {r : ℕ} {v : Fin r → Address} (hv : LinearIndependent F v) (i : Fin r) :
    Module.Basis.sumExtend hv (Sum.inl i) = v i := by
  unfold Module.Basis.sumExtend
  rw [Module.Basis.reindex_apply, Module.Basis.coe_extend]
  rfl

theorem frameRank_le (f : CertifiedFrame) : f.data.rank ≤ 9 := by
  simpa using f.independent.fintype_card_le_finrank

/-- The basis indices of a frame completion, placing the retained columns first. -/
noncomputable def completionIndex (f : CertifiedFrame) :
    Fin f.data.rank ⊕ Module.Basis.sumExtendIndex f.independent ≃ Fin 9 :=
  haveI := Fintype.ofFinite (Module.Basis.sumExtendIndex f.independent)
  have hcard : Fintype.card (Module.Basis.sumExtendIndex f.independent) = 9 - f.data.rank := by
    have h := Module.finrank_eq_card_basis (Module.Basis.sumExtend f.independent)
    rw [Fintype.card_sum, Fintype.card_fin, Module.finrank_fin_fun] at h
    omega
  (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFinOfCardEq hcard)).trans
    (finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' (frameRank_le f))))

theorem completionIndex_symm (f : CertifiedFrame) (i : Fin f.data.rank) :
    (completionIndex f).symm (Fin.castLE (frameRank_le f) i) = Sum.inl i :=
  (completionIndex f).symm_apply_eq.mpr (Fin.ext rfl)

/-- The address map sending the standard basis to the completed frame basis. -/
noncomputable def frameExtension (f : CertifiedFrame) : FrameExtension f.data where
  rank_le := frameRank_le f
  matrix := (Pi.basisFun F (Fin 9)).equiv
    ((Module.Basis.sumExtend f.independent).reindex (completionIndex f)) (Equiv.refl _)
  columns i := by
    rw [← Pi.basisFun_apply F (Fin 9), Module.Basis.equiv_apply, Equiv.refl_apply,
      Module.Basis.reindex_apply, completionIndex_symm f, sumExtend_inl]

noncomputable def catalogExtension (i : ℕ) : FrameExtension (catalog i).data :=
  frameExtension (catalog i)

noncomputable def nativeTableau (i : ℕ) : PhaseAddress ≃ₗ[F] PhaseAddress :=
  sourceCanonical (catalogExtension i).matrix (catalog i).data.rank

end IntegerMultBounds.Networks.Certificates.T16.Tableau
