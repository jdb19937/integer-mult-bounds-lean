module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Model
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Source-specific doubled binary geometry. These are subspace statements;
no Clifford tableau or complex operator correspondence is assumed. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

abbrev PhaseAddress := Address × Address

/-- The invertible shear taking `(u,v)` to `(u,u+v)`. -/
def phaseShear : PhaseAddress ≃ₗ[F] PhaseAddress where
  toFun p := (p.1, p.1 + p.2)
  invFun p := (p.1, p.2 - p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_add' p q := by ext <;> simp [add_comm, add_left_comm, add_assoc]
  map_smul' c p := by ext <;> simp [smul_add]

/-- The ordinary binary orthogonal complement; the ambient form is nondegenerate. -/
def binaryOrthogonal (U : Submodule F Address) : Submodule F Address :=
  (Labels.binary 9).orthogonal U

/-- The supplier's inverse-Z subspace, without assuming an operator realizes it. -/
def frameLagrangian (U : Submodule F Address) : Submodule F PhaseAddress :=
  (U.prod (binaryOrthogonal U)).map phaseShear.toLinearMap

theorem mem_frameLagrangian (U : Submodule F Address) (p : PhaseAddress) :
    p ∈ frameLagrangian U ↔ ∃ u ∈ U, ∃ v ∈ binaryOrthogonal U, p = (u,u+v) := by
  constructor
  · rintro ⟨⟨u,v⟩, huv, hp⟩
    exact ⟨u, huv.1, v, huv.2, hp.symm⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨(u,v), ⟨hu,hv⟩, rfl⟩

theorem binaryOrthogonal_finrank (U : Submodule F Address) :
    Module.finrank F (binaryOrthogonal U) = 9 - Module.finrank F U := by
  unfold binaryOrthogonal
  rw [LinearMap.BilinForm.finrank_orthogonal (Labels.binary_nondegenerate (h := 9))]
  have h : Module.finrank F Address = 9 := by simp [Address]
  rw [h]

theorem shear_product_finrank (U V : Submodule F Address) :
    Module.finrank F ((U.prod V).map phaseShear.toLinearMap) =
      Module.finrank F U + Module.finrank F V := by
  rw [phaseShear.finrank_map_eq, (U.prodEquiv V).finrank_eq, Module.finrank_prod]

theorem frameLagrangian_finrank (U : Submodule F Address) :
    Module.finrank F (frameLagrangian U) = 9 := by
  rw [frameLagrangian, shear_product_finrank, binaryOrthogonal_finrank]
  have h : Module.finrank F U ≤ 9 := by
    simpa [Address, F] using Submodule.finrank_le U
  omega

/-- Inclusion gives an exact intersection formula, including degenerate subspaces. -/
theorem frameLagrangian_inf {U V : Submodule F Address} (h : U ≤ V) :
    frameLagrangian U ⊓ frameLagrangian V =
      (U.prod (binaryOrthogonal V)).map phaseShear.toLinearMap := by
  have horth : binaryOrthogonal V ≤ binaryOrthogonal U :=
    LinearMap.BilinForm.orthogonal_le h
  rw [frameLagrangian, frameLagrangian, ← Submodule.map_inf _ phaseShear.injective,
    Submodule.prod_inf_prod, inf_eq_left.mpr h,
    inf_eq_right.mpr horth]

theorem frameLagrangian_inf_finrank {U V : Submodule F Address} (h : U ≤ V) :
    Module.finrank F (frameLagrangian U ⊓ frameLagrangian V : Submodule F PhaseAddress) =
      Module.finrank F U + (9 - Module.finrank F V) := by
  rw [frameLagrangian_inf h, shear_product_finrank, binaryOrthogonal_finrank]

/-- The alternating pairing on the doubled binary address space. -/
def symplecticPair (p q : PhaseAddress) : F :=
  Labels.binary 9 p.1 q.2 + Labels.binary 9 p.2 q.1

/-- Every source-specific frame subspace is isotropic for the doubled pairing. -/
theorem frameLagrangian_isotropic (U : Submodule F Address)
    {p q : PhaseAddress} (hp : p ∈ frameLagrangian U)
    (hq : q ∈ frameLagrangian U) : symplecticPair p q = 0 := by
  obtain ⟨u, hu, v, hv, rfl⟩ := (mem_frameLagrangian U p).mp hp
  obtain ⟨w, hw, z, hz, rfl⟩ := (mem_frameLagrangian U q).mp hq
  have huz : Labels.binary 9 u z = 0 := hz u hu
  have hwv : Labels.binary 9 w v = 0 := hv w hw
  have hvw : Labels.binary 9 v w = 0 := by
    rw [Labels.binary, Labels.form_symm]
    exact hwv
  simp only [symplecticPair, map_add, LinearMap.add_apply, huz, hvw, add_zero]
  exact CharTwo.add_self_eq_zero _

/-- The dimension deficit later needed for a separate symplectic B-block theorem. -/
theorem frameLagrangian_inf_deficit {U V : Submodule F Address} (h : U ≤ V) :
    9 - Module.finrank F (frameLagrangian U ⊓ frameLagrangian V : Submodule F PhaseAddress) =
      Module.finrank F V - Module.finrank F U := by
  rw [frameLagrangian_inf_finrank h]
  have hV : Module.finrank F V ≤ 9 := by
    simpa [Address, F] using Submodule.finrank_le V
  omega

end IntegerMultBounds.Networks.Certificates.T16.Geometry
