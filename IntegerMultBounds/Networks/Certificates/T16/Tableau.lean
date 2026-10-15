module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Lagrangian
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Binary tableaus for the source's canonical Clifford recipe. Phases are
explicitly omitted; these are actual linear equivalences on doubled addresses. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Tableau
open Geometry

abbrev dot := Labels.binary 9

@[simp] theorem address_add_self (x : Address) : x + x = 0 := by
  ext i
  exact CharTwo.add_self_eq_zero (x i)

theorem dot_symm (x y : Address) : dot x y = dot y x := Labels.form_symm 0 x y

noncomputable def transpose (G : Address ≃ₗ[F] Address) : Address ≃ₗ[F] Address :=
  ((dot.toDual Labels.binary_nondegenerate).trans G.dualMap).trans
    (dot.toDual Labels.binary_nondegenerate).symm

theorem transpose_dot (G : Address ≃ₗ[F] Address) (x y : Address) :
    dot (transpose G x) y = dot x (G y) := by
  simp [transpose, LinearMap.BilinForm.apply_toDual_symm_apply,
    LinearMap.BilinForm.toDual_def]

/-- Projection onto the first `r` source coordinates. -/
def cut (r : ℕ) : Address →ₗ[F] Address where
  toFun x i := if i.val < r then x i else 0
  map_add' x y := by ext i; by_cases h : i.val < r <;> simp [h]
  map_smul' c x := by ext i; by_cases h : i.val < r <;> simp [h]

theorem cut_idem (r : ℕ) (x : Address) : cut r (cut r x) = cut r x := by
  ext i; by_cases h : i.val < r <;> simp [cut, h]

theorem cut_dot (r : ℕ) (x y : Address) : dot (cut r x) y = dot x (cut r y) := by
  simp only [dot, Labels.binary, Labels.form_apply, zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i.val < r <;> simp [cut, h]

/-- Span of the first `r` columns of `G`, expressed as an actual range. -/
def frameSpace (G : Address ≃ₗ[F] Address) (r : ℕ) : Submodule F Address :=
  LinearMap.range (G.toLinearMap.comp (cut r))

theorem orthogonal_frameSpace (G : Address ≃ₗ[F] Address) (r : ℕ) (v : Address) :
    v ∈ binaryOrthogonal (frameSpace G r) ↔ cut r (transpose G v) = 0 := by
  constructor
  · intro h
    apply Labels.binary_nondegenerate.1
    intro a
    rw [cut_dot, transpose_dot, dot_symm]
    exact h _ ⟨a, rfl⟩
  · intro h w hw
    obtain ⟨a, rfl⟩ := hw
    change dot (G (cut r a)) v = 0
    rw [dot_symm, ← transpose_dot, ← cut_dot, h, map_zero]
    rfl

/-- Address permutation tableau, with inverse transpose on the Z coordinates. -/
noncomputable def perm (G : Address ≃ₗ[F] Address) : PhaseAddress ≃ₗ[F] PhaseAddress :=
  G.prodCongr (transpose G).symm

/-- A diagonal quadratic gate acts as a lower shear. -/
def diagonal (Q : Address →ₗ[F] Address) : PhaseAddress ≃ₗ[F] PhaseAddress where
  toFun p := (p.1, p.2 + Q p.1)
  invFun p := (p.1, p.2 - Q p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_add' p q := by ext <;> simp [add_comm, add_left_comm, add_assoc]
  map_smul' c p := by ext <;> simp [smul_add]

/-- Product of the source C gates on the first `r` axes. -/
def partialC (r : ℕ) : PhaseAddress ≃ₗ[F] PhaseAddress where
  toFun p := (p.1 + cut r p.2, p.2)
  invFun p := (p.1 - cut r p.2, p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_add' p q := by ext <;> simp [add_comm, add_left_comm, add_assoc]
  map_smul' c p := by ext <;> simp [smul_add]

/-- `Q = I + G⁻ᵀ G⁻¹`. -/
noncomputable def quadratic (G : Address ≃ₗ[F] Address) : Address →ₗ[F] Address :=
  LinearMap.id + (transpose G).symm.toLinearMap.comp G.symm.toLinearMap

/-- `K = D_Q P_G`: `trans` applies its left argument first. -/
noncomputable def conjugator (G : Address ≃ₗ[F] Address) :
    PhaseAddress ≃ₗ[F] PhaseAddress :=
  (perm G).trans (diagonal (quadratic G))

/-- Actual binary canonical recipe `K C_r K⁻¹`. -/
noncomputable def canonical (G : Address ≃ₗ[F] Address) (r : ℕ) :
    PhaseAddress ≃ₗ[F] PhaseAddress :=
  ((conjugator G).symm.trans (partialC r)).trans (conjugator G)

theorem canonical_Z (G : Address ≃ₗ[F] Address) (r : ℕ) (z : Address) :
    canonical G r (0,z) =
      (G (cut r (transpose G z)),
       G (cut r (transpose G z)) +
         (z + (transpose G).symm (cut r (transpose G z)))) := by
  simp [canonical, conjugator, perm, diagonal, partialC, quadratic,
    add_comm, add_left_comm]

theorem mem_frameSpace (G : Address ≃ₗ[F] Address) (r : ℕ) (u : Address) :
    u ∈ frameSpace G r ↔ cut r (G.symm u) = G.symm u := by
  constructor
  · rintro ⟨a, rfl⟩
    simp [cut_idem]
  · intro h
    exact ⟨G.symm u, by simpa using congrArg G h⟩

theorem partialC_symm (r : ℕ) : (partialC r).symm = partialC r := by
  ext p i <;> simp [partialC, sub_eq_add_neg, CharTwo.neg_eq]

theorem canonical_symm (G : Address ≃ₗ[F] Address) (r : ℕ) :
    (canonical G r).symm = canonical G r := by
  apply LinearEquiv.ext
  intro p
  change conjugator G ((partialC r).symm ((conjugator G).symm p)) =
    conjugator G (partialC r ((conjugator G).symm p))
  rw [partialC_symm]

/-- The standard Z-generator subspace. -/
def zEmbed : Address →ₗ[F] PhaseAddress := LinearMap.inr F Address Address

def zSpace : Submodule F PhaseAddress := LinearMap.range zEmbed

theorem canonical_image_Z (G : Address ≃ₗ[F] Address) (r : ℕ) :
    zSpace.map (canonical G r).toLinearMap = frameLagrangian (frameSpace G r) := by
  ext p
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    rw [mem_frameLagrangian]
    let a := cut r (transpose G z)
    refine ⟨G a, ⟨transpose G z, rfl⟩, z + (transpose G).symm a, ?_, ?_⟩
    · rw [orthogonal_frameSpace]
      simp [a, cut_idem]
    · exact canonical_Z G r z
  · intro hp
    obtain ⟨u, hu, v, hv, rfl⟩ := (mem_frameLagrangian _ p).mp hp
    have hu' := (mem_frameSpace G r u).mp hu
    have hv' := (orthogonal_frameSpace G r v).mp hv
    let z := (transpose G).symm (G.symm u) + v
    have hz : cut r (transpose G z) = G.symm u := by
      simp [z, hu', hv']
    refine ⟨(0,z), ⟨z, rfl⟩, ?_⟩
    change canonical G r (0,z) = _
    rw [canonical_Z, hz]
    simp [z, add_comm, add_left_comm]

/-- Exact inverse-Z identity for the explicit canonical binary recipe. -/
theorem canonical_inverse_Z (G : Address ≃ₗ[F] Address) (r : ℕ) :
    zSpace.map (canonical G r).symm.toLinearMap = frameLagrangian (frameSpace G r) := by
  rw [canonical_symm, canonical_image_Z]

end IntegerMultBounds.Networks.Certificates.T16.Tableau
