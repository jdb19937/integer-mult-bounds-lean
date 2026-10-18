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

/-- Additive, homogeneous functions agreeing on all characters are equal. Composites of
operators are compared through this form, so the kernel never unfolds a packaged composite. -/
theorem eq_of_chars_fun {A B : Arrays h → Arrays h}
    (hA0 : A 0 = 0) (hAadd : ∀ x y, A (x + y) = A x + A y) (hAsmul : ∀ (z : ℂ) x, A (z • x) = z • A x)
    (hB0 : B 0 = 0) (hBadd : ∀ x y, B (x + y) = B x + B y) (hBsmul : ∀ (z : ℂ) x, B (z • x) = z • B x)
    (hAB : ∀ u, A (charVec u) = B (charVec u)) (f : Arrays h) : A f = B f := by
  have key : ∀ (C : Arrays h → Arrays h), C 0 = 0 → (∀ x y, C (x + y) = C x + C y) →
      (∀ (z : ℂ) x, C (z • x) = z • C x) → ∀ s : Finset (Address h),
        C (∑ u ∈ s, ((volume h)⁻¹ * walsh h f u) • charVec u) =
          ∑ u ∈ s, ((volume h)⁻¹ * walsh h f u) • C (charVec u) := by
    intro C h0 hadd hsmul s
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, hsmul, ih]
  rw [sum_chars f, key A hA0 hAadd hAsmul, key B hB0 hBadd hBsmul]
  simp only [hAB]

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
