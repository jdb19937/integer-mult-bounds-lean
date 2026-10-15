module

public import IntegerMultBounds.Networks.Certificates.T16.TableauRank

/-! The source's zero/full-rank branches, alongside its conjugated partial-C
recipe. These definitions concern binary tableaus only. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Tableau
open Geometry

theorem transpose_refl : transpose (LinearEquiv.refl F Address) = LinearEquiv.refl F Address := by
  apply LinearEquiv.ext
  intro x
  simp [transpose]

theorem canonical_refl (r : ℕ) : canonical (LinearEquiv.refl F Address) r = partialC r := by
  apply LinearEquiv.ext
  intro p
  simp [canonical, conjugator, perm, diagonal, quadratic, transpose_refl]

theorem cut_zero (x : Address) : cut 0 x = 0 := by ext i; simp [cut]
theorem cut_nine (x : Address) : cut 9 x = x := by ext i; simp [cut]

theorem canonical_zero (G : Address ≃ₗ[F] Address) :
    canonical G 0 = LinearEquiv.refl F PhaseAddress := by
  have hc : partialC 0 = LinearEquiv.refl F PhaseAddress := by
    ext p i <;> simp [partialC, cut_zero]
  apply LinearEquiv.ext
  intro p
  simp [canonical, hc]

theorem frameSpace_nine (G : Address ≃ₗ[F] Address) : frameSpace G 9 = ⊤ := by
  apply top_unique
  intro u _
  exact ⟨G.symm u, by simp [cut_nine]⟩

/-- Matches all three branches of `canonical_frame`, omitting Pauli phases. -/
noncomputable def sourceCanonical (G : Address ≃ₗ[F] Address) (r : ℕ) :
    PhaseAddress ≃ₗ[F] PhaseAddress :=
  if r = 0 then LinearEquiv.refl F PhaseAddress
  else if r = 9 then partialC 9 else canonical G r

theorem sourceCanonical_inverse_Z (G : Address ≃ₗ[F] Address) (r : ℕ) :
    inverseZ (sourceCanonical G r) = frameLagrangian (frameSpace G r) := by
  unfold sourceCanonical
  split_ifs with h0 h9
  · subst r
    rw [← canonical_zero G]
    exact canonical_inverse_Z G 0
  · subst r
    rw [← canonical_refl 9]
    change zSpace.map (canonical (LinearEquiv.refl F Address) 9).symm.toLinearMap = _
    rw [canonical_inverse_Z, frameSpace_nine, frameSpace_nine]
  · exact canonical_inverse_Z G r

theorem sourceCanonical_relative_rank (G H : Address ≃ₗ[F] Address) (r s : ℕ)
    (h : frameSpace G r ≤ frameSpace H s) :
    Module.finrank F
      (LinearMap.range (bBlock (sourceCanonical G r) (sourceCanonical H s))) =
      Module.finrank F (frameSpace H s) - Module.finrank F (frameSpace G r) := by
  rw [bBlock_rank, sourceCanonical_inverse_Z, sourceCanonical_inverse_Z,
    frameLagrangian_inf_deficit h]

end IntegerMultBounds.Networks.Certificates.T16.Tableau
