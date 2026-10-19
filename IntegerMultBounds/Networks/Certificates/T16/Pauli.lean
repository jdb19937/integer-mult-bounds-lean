module

public import IntegerMultBounds.Networks.Certificates.T16.Tableau
public import IntegerMultBounds.Networks.BinaryWalsh

/-! Actual complex Pauli operators in the source convention `i^p X^x Z^z`.
These definitions retain the phase; no tableau completeness is assumed. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Pauli
open Geometry BinaryPhase BinaryWalsh

abbrev State := Geometry.Address → ℂ

/-- Source Pauli label, including its exponent modulo four. -/
structure Label where
  x : Geometry.Address
  z : Geometry.Address
  phase : ZMod 4

def Label.binary (p : Label) : PhaseAddress := (p.x,p.z)

/-- `X` acts after `Z`, exactly as in the source multiplication convention. -/
noncomputable def operator (p : Label) : State →ₗ[ℂ] State :=
  BinaryPhase.phase p.phase • (translation p.x).comp (characterMultiply p.z)

theorem operator_apply (p : Label) (f : State) (x : Geometry.Address) :
    operator p f x = BinaryPhase.phase p.phase * chi p.z (x + p.x) * f (x + p.x) := by
  change BinaryPhase.phase p.phase * (chi p.z (x + p.x) * f (x + p.x)) = _
  ring

/-- The source's exact ordered Pauli multiplication, including the cross phase. -/
def multiply (p q : Label) : Label :=
  ⟨p.x + q.x, p.z + q.z,
    p.phase + q.phase + doubleLift (Tableau.dot p.z q.x)⟩

theorem phase_doubleLift (b : ZMod 2) : BinaryPhase.phase (doubleLift b) = sign b := by
  fin_cases b
  · rfl
  · change Complex.I ^ 2 = -1
    exact Complex.I_sq

/-- A coordinate kernel as a genuine equivalence with its phase-negated inverse. -/
noncomputable def kernelEquiv (s : ZMod 4) (q : Geometry.Address) : State ≃ₗ[ℂ] State :=
  { kernel s q with
    invFun := kernel (-s) q
    left_inv := kernel_inverse s q
    right_inv := by
      intro f
      simpa using kernel_inverse (-s) q f }

noncomputable def cGate (q : Geometry.Address) : State ≃ₗ[ℂ] State := kernelEquiv 1 q

theorem cGate_apply (q : Geometry.Address) (f : State) (x : Geometry.Address) :
    cGate q f x = ((1 + Complex.I) / 2) * f x +
      ((1 - Complex.I) / 2) * f (x + q) := kernel_forward q f x

/-- Actual permutation on state amplitudes: a basis ket at x moves to Gx. -/
noncomputable def permutation (G : Geometry.Address ≃ₗ[F] Geometry.Address) :
    State ≃ₗ[ℂ] State where
  toFun f x := f (G.symm x)
  invFun f x := f (G x)
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Source P gate has zero added Pauli phase. -/
noncomputable def permuteLabel (G : Geometry.Address ≃ₗ[F] Geometry.Address) (p : Label) : Label :=
  ⟨G p.x, (Tableau.transpose G).symm p.z, p.phase⟩

theorem chi_permutation (G : Geometry.Address ≃ₗ[F] Geometry.Address)
    (b y : Geometry.Address) : chi ((Tableau.transpose G).symm b) (G y) = chi b y := by
  unfold chi
  rw [← Tableau.transpose_dot, LinearEquiv.apply_symm_apply]

theorem permutation_intertwines (G : Geometry.Address ≃ₗ[F] Geometry.Address)
    (p : Label) (f : State) : permutation G (operator p f) =
      operator (permuteLabel G p) (permutation G f) := by
  ext x
  change operator p f (G.symm x) = operator (permuteLabel G p) (permutation G f) x
  rw [operator_apply, operator_apply]
  change _ = BinaryPhase.phase p.phase * chi ((Tableau.transpose G).symm p.z) (x + G p.x) *
    f (G.symm (x + G p.x))
  have hx : x + G p.x = G (G.symm x + p.x) := by simp
  rw [hx, chi_permutation, LinearEquiv.symm_apply_apply]

theorem permutation_conjugates (G : Geometry.Address ≃ₗ[F] Geometry.Address)
    (p : Label) (f : State) : permutation G (operator p ((permutation G).symm f)) =
      operator (permuteLabel G p) f := by
  rw [permutation_intertwines, LinearEquiv.apply_symm_apply]

/-- The binary projection agrees with the already-certified permutation tableau. -/
theorem permuteLabel_binary (G : Geometry.Address ≃ₗ[F] Geometry.Address) (p : Label) :
    (permuteLabel G p).binary = Tableau.perm G p.binary := rfl

end IntegerMultBounds.Networks.Certificates.T16.Pauli
