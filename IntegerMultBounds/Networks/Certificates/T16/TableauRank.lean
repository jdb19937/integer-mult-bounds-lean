module

public import IntegerMultBounds.Networks.Certificates.T16.Tableau
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Actual X-block ranks of relative binary tableaus. No Pauli phases or complex
operator equality are asserted by these binary linear-algebra theorems. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Tableau
open Geometry

def inverseZ (A : PhaseAddress ≃ₗ[F] PhaseAddress) : Submodule F PhaseAddress :=
  zSpace.map A.symm.toLinearMap

theorem mem_inverseZ (A : PhaseAddress ≃ₗ[F] PhaseAddress) (p : PhaseAddress) :
    p ∈ inverseZ A ↔ (A p).1 = 0 := by
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    simp [zEmbed]
  · intro h
    refine ⟨(0,(A p).2), ⟨(A p).2, rfl⟩, ?_⟩
    change A.symm (0,(A p).2) = p
    apply A.injective
    simp only [LinearEquiv.apply_symm_apply]
    exact Prod.ext h.symm rfl

/-- Relative tableau `B A⁻¹`, in the source's application order. -/
def relative (A B : PhaseAddress ≃ₗ[F] PhaseAddress) : PhaseAddress ≃ₗ[F] PhaseAddress :=
  A.symm.trans B

/-- The actual X block of the images of the standard Z generators. -/
def bBlock (A B : PhaseAddress ≃ₗ[F] PhaseAddress) : Address →ₗ[F] Address :=
  (LinearMap.fst F Address Address).comp ((relative A B).toLinearMap.comp zEmbed)

def kernelLift (A B : PhaseAddress ≃ₗ[F] PhaseAddress) :
    LinearMap.ker (bBlock A B) →ₗ[F] PhaseAddress :=
  A.symm.toLinearMap.comp (zEmbed.comp (LinearMap.ker (bBlock A B)).subtype)

theorem kernelLift_injective (A B : PhaseAddress ≃ₗ[F] PhaseAddress) :
    Function.Injective (kernelLift A B) := by
  intro z w h
  apply Subtype.ext
  have h' := congrArg (fun p => (A p).2) h
  simpa [kernelLift, zEmbed] using h'

theorem kernelLift_range (A B : PhaseAddress ≃ₗ[F] PhaseAddress) :
    LinearMap.range (kernelLift A B) = inverseZ A ⊓ inverseZ B := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    constructor
    · apply (mem_inverseZ A _).mpr
      simp [kernelLift, zEmbed]
    · apply (mem_inverseZ B _).mpr
      exact z.property
  · rintro ⟨ha,hb⟩
    have ha' := (mem_inverseZ A p).mp ha
    have hb' := (mem_inverseZ B p).mp hb
    have hAp : (0,(A p).2) = A p := Prod.ext ha'.symm rfl
    have hker : (A p).2 ∈ LinearMap.ker (bBlock A B) := by
      change (B (A.symm (0,(A p).2))).1 = 0
      rw [hAp, LinearEquiv.symm_apply_apply]
      exact hb'
    refine ⟨⟨(A p).2, hker⟩, ?_⟩
    change A.symm (0,(A p).2) = p
    rw [hAp, LinearEquiv.symm_apply_apply]

theorem bBlock_kernel_finrank (A B : PhaseAddress ≃ₗ[F] PhaseAddress) :
    Module.finrank F (LinearMap.ker (bBlock A B)) =
      Module.finrank F (inverseZ A ⊓ inverseZ B : Submodule F PhaseAddress) := by
  rw [← kernelLift_range]
  exact (LinearMap.finrank_range_of_inj (kernelLift_injective A B)).symm

theorem bBlock_rank (A B : PhaseAddress ≃ₗ[F] PhaseAddress) :
    Module.finrank F (LinearMap.range (bBlock A B)) =
      9 - Module.finrank F (inverseZ A ⊓ inverseZ B : Submodule F PhaseAddress) := by
  have h := (bBlock A B).finrank_range_add_finrank_ker
  rw [bBlock_kernel_finrank] at h
  have hd : Module.finrank F Address = 9 := by simp [Address]
  rw [hd] at h
  omega

/-- B-block width of the actual canonical recipes on nested frame spaces. -/
theorem canonical_relative_rank (G H : Address ≃ₗ[F] Address) (r s : ℕ)
    (h : frameSpace G r ≤ frameSpace H s) :
    Module.finrank F (LinearMap.range (bBlock (canonical G r) (canonical H s))) =
      Module.finrank F (frameSpace H s) - Module.finrank F (frameSpace G r) := by
  rw [bBlock_rank]
  change 9 - Module.finrank F
    (zSpace.map (canonical G r).symm.toLinearMap ⊓
      zSpace.map (canonical H s).symm.toLinearMap : Submodule F PhaseAddress) = _
  rw [canonical_inverse_Z, canonical_inverse_Z, frameLagrangian_inf_deficit h]

end IntegerMultBounds.Networks.Certificates.T16.Tableau
