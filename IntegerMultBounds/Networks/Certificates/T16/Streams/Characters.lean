module

public import IntegerMultBounds.Networks.Certificates.T16.Streams.Kernels

/-! Walsh characters diagonalize the T16 operators. A translation kernel multiplies the
character `χ_u` by `i^{q [u·v]}`, so `basisOp B c` multiplies it by `i^{Σ_k c_k [u·B_k]}`, and two
operators that agree on every character are equal. Identities between products of kernels
therefore reduce to identities between their phase functions. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Streams

open BinaryWalsh BinaryPhase Multiplicative

variable {h : ℕ}

/-- The Walsh character of frequency `u`. -/
noncomputable def charVec (u : Address h) : Arrays h := fun x => chi u x

theorem kernel_char (q : ZMod 4) (v u : Address h) :
    kernel q v (charVec u) = phase (q * bitLift (Labels.binary h u v)) • charVec u := by
  funext x
  simp only [kernel_apply, charVec, Pi.smul_apply, smul_eq_mul, chi_add, phase_bit]
  have hs : chi u v = if Labels.binary h u v = 0 then 1 else -1 := rfl
  rw [hs]
  ring

/-- Every array is a combination of characters. -/
theorem sum_chars (f : Arrays h) :
    f = ∑ u, ((volume h)⁻¹ * walsh h f u) • charVec u := by
  funext x
  have hw := walsh_square f x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, charVec]
  have e : ∑ u, (volume h)⁻¹ * walsh h f u * chi u x =
      (volume h)⁻¹ * walsh h (walsh h f) x := by
    rw [walsh_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [chi_symm u x]
    ring
  rw [e, hw, ← mul_assoc, inv_mul_cancel₀ (volume_ne_zero h), one_mul]

/-- Operators agreeing on all characters are equal. -/
theorem eq_of_chars {A B : Arrays h →ₗ[ℂ] Arrays h} (hAB : ∀ u, A (charVec u) = B (charVec u)) :
    A = B := by
  apply LinearMap.ext
  intro f
  rw [sum_chars f, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [map_smul, map_smul, hAB]

/-- The phase function of a coefficient vector over a basis. -/
def phaseExp (B : Fin 73 → Address 73) (c : Fin 73 → ZMod 4) (u : Address 73) : ZMod 4 :=
  ∑ k, c k * bitLift (Labels.binary 73 u (B k))

theorem basisOp_char (B : Fin 73 → Address 73) (c : Fin 73 → ZMod 4) (u : Address 73) :
    basisOp B (ofAdd c) (charVec u) = phase (phaseExp B c u) • charVec u := by
  have key : ∀ S : Finset (Fin 73),
      basisOp B (ofAdd (∑ k ∈ S, Pi.single k (c k))) (charVec u) =
        phase (∑ k ∈ S, c k * bitLift (Labels.binary 73 u (B k))) • charVec u := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ofAdd_add, map_mul, Module.End.mul_apply,
        ih, map_smul, basisOp_single, kernel_char, smul_smul, phase_add, mul_comm]
  have hc : ∑ k ∈ Finset.univ, Pi.single k (c k) = c := Finset.univ_sum_single c
  simpa [hc, phaseExp] using key Finset.univ

/-- Coefficient vectors with equal phase functions give equal operators. -/
theorem basisOp_eq_of_phase {B B' : Fin 73 → Address 73} {c c' : Fin 73 → ZMod 4}
    (h : ∀ u, phaseExp B c u = phaseExp B' c' u) :
    basisOp B (ofAdd c) = basisOp B' (ofAdd c') := by
  apply eq_of_chars
  intro u
  rw [basisOp_char, basisOp_char, h]

end IntegerMultBounds.Networks.Certificates.T16.Streams
