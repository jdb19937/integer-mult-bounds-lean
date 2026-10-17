module

public import IntegerMultBounds.Networks.Certificates.T16.PauliCanonical

/-! Soundness of the source's equality test for Clifford operators. A linear map commuting
with every Pauli generator is a scalar, so two exact realizations whose labels agree on the
eighteen generators differ by a global scalar, and agreement on the zero state makes them equal.
This justifies `compiled.tab == op.tab and compiled.zero_state() == op.zero_state()`. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Pauli
open Geometry BinaryPhase BinaryWalsh

/-- The pure X label of an address. -/
def xLabel (v : Geometry.Address) : Label := ⟨v, 0, 0⟩

/-- The basis state at an address. -/
noncomputable def basisState (a : Geometry.Address) : State := Pi.single a 1

theorem operator_xLabel_apply (v : Geometry.Address) (f : State) (y : Geometry.Address) :
    operator (xLabel v) f y = f (y + v) := by
  rw [operator_apply]
  simp [xLabel]

theorem operator_zGenerator_apply (i : Fin 9) (f : State) (y : Geometry.Address) :
    operator (zGenerator i) f y = sign (y i) * f y := by
  rw [operator_apply]
  simp only [zGenerator, phase_zero, one_mul, add_zero]
  rw [chi, show Labels.binary 9 = Tableau.dot from rfl, dot_single]

/-- `M` commutes with the Pauli operator of `p`. -/
def Commutes (M : State →ₗ[ℂ] State) (p : Label) : Prop :=
  ∀ f, M (operator p f) = operator p (M f)

theorem Commutes.multiply {M : State →ₗ[ℂ] State} {p q : Label} (hp : Commutes M p)
    (hq : Commutes M q) : Commutes M (multiply p q) := by
  intro f
  rw [← operator_multiply, hp, hq, operator_multiply]

theorem multiply_xLabel (v w : Geometry.Address) :
    multiply (xLabel v) (xLabel w) = xLabel (v + w) := by
  simp [multiply, xLabel, doubleLift]

theorem commutes_xLabel_zero (M : State →ₗ[ℂ] State) : Commutes M (xLabel 0) := by
  intro f
  have h : ∀ g : State, operator (xLabel 0) g = g := fun g => by
    funext y
    rw [operator_xLabel_apply, add_zero]
  rw [h, h]

/-- Commuting with the nine X generators gives commuting with every X label. -/
theorem commutes_xLabel {M : State →ₗ[ℂ] State} (hx : ∀ i, Commutes M (xGenerator i))
    (v : Geometry.Address) : Commutes M (xLabel v) := by
  have hs : ∀ i (b : F), Commutes M (xLabel (Pi.single i b)) := by
    intro i b
    rcases (show b = 0 ∨ b = 1 by revert b; decide) with rfl | rfl
    · rw [Pi.single_zero]
      exact commutes_xLabel_zero M
    · exact hx i
  have hsum : ∀ s : Finset (Fin 9), Commutes M (xLabel (∑ i ∈ s, Pi.single i (v i))) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using commutes_xLabel_zero M
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, ← multiply_xLabel]
      exact (hs i (v i)).multiply ih
  simpa [Finset.univ_sum_single] using hsum Finset.univ

theorem sign_injective (a b : F) (h : sign a = sign b) : a = b := by
  have h2 : ∀ c : F, c = 0 ∨ c = 1 := by decide
  rcases h2 a with rfl | rfl <;> rcases h2 b with rfl | rfl
  · rfl
  · norm_num at h
  · norm_num at h
  · rfl

/-- **Pauli irreducibility.** A linear map commuting with every X label and every Z generator is
the scalar `M |0⟩ (0)`. -/
theorem eq_smul_of_commutes {M : State →ₗ[ℂ] State} (hx : ∀ v, Commutes M (xLabel v))
    (hz : ∀ i, Commutes M (zGenerator i)) :
    M = (M (basisState 0) 0) • LinearMap.id := by
  set c := M (basisState 0) 0
  -- `M |a⟩` vanishes away from `a`
  have hoff : ∀ a y, y ≠ a → M (basisState a) y = 0 := by
    intro a y hya
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hya
    have hop : operator (zGenerator i) (basisState a) = sign (a i) • basisState a := by
      funext y
      rw [operator_zGenerator_apply]
      by_cases h : y = a
      · subst h; rfl
      · simp [basisState, h]
    have h := congrFun (hz i (basisState a)) y
    rw [hop, map_smul, operator_zGenerator_apply] at h
    change sign (a i) * M (basisState a) y = sign (y i) * M (basisState a) y at h
    have hs : sign (a i) - sign (y i) ≠ 0 := by
      intro h0
      exact hi (sign_injective _ _ (sub_eq_zero.mp h0)).symm
    have : (sign (a i) - sign (y i)) * M (basisState a) y = 0 := by rw [sub_mul, h, sub_self]
    exact (mul_eq_zero.mp this).resolve_left hs
  -- the diagonal entry does not depend on `a`
  have hdiag : ∀ a, M (basisState a) a = c := by
    intro a
    have hop : operator (xLabel a) (basisState 0) = basisState a := by
      funext y
      rw [operator_xLabel_apply]
      simp only [basisState, Pi.single_apply]
      congr 1
      apply propext
      constructor
      · intro h
        calc y = y + a + a := by rw [add_assoc, Tableau.address_add_self, add_zero]
          _ = a := by rw [h, zero_add]
      · intro h
        rw [h, Tableau.address_add_self]
    have h := congrFun (hx a (basisState 0)) a
    rw [hop, operator_xLabel_apply, Tableau.address_add_self] at h
    exact h
  apply (Pi.basisFun ℂ Geometry.Address).ext
  intro a
  rw [Pi.basisFun_apply]
  funext y
  change M (basisState a) y = c * basisState a y
  by_cases h : y = a
  · subst h
    rw [hdiag]
    simp [basisState]
  · rw [hoff a y h]
    simp [basisState, h]

/-- The comparison map of two realizations commutes with every label they agree on. -/
theorem Realization.commutes_of_label {A B : Realization} {p : Label}
    (h : A.label p = B.label p) :
    Commutes (B.scalar.symm.toLinearMap ∘ₗ A.scalar.toLinearMap) p := by
  intro g
  change B.scalar.symm (A.scalar (operator p g)) = operator p (B.scalar.symm (A.scalar g))
  have hA := A.conjugates p (A.scalar g)
  rw [LinearEquiv.symm_apply_apply] at hA
  have hB := B.conjugates p (A.scalar g)
  rw [hA, h, ← hB, LinearEquiv.symm_apply_apply]

/-- Realizations whose labels agree on all eighteen generators differ by a global scalar. -/
theorem Realization.scalar_eq_smul {A B : Realization}
    (hx : ∀ i, A.label (xGenerator i) = B.label (xGenerator i))
    (hz : ∀ i, A.label (zGenerator i) = B.label (zGenerator i)) :
    ∃ c : ℂ, ∀ f, A.scalar f = c • B.scalar f := by
  set M := B.scalar.symm.toLinearMap ∘ₗ A.scalar.toLinearMap
  have hM := eq_smul_of_commutes (M := M)
    (commutes_xLabel fun i => Realization.commutes_of_label (hx i))
    (fun i => Realization.commutes_of_label (hz i))
  refine ⟨M (basisState 0) 0, fun f => ?_⟩
  have h := LinearMap.congr_fun hM f
  change B.scalar.symm (A.scalar f) = _ at h
  rw [LinearMap.smul_apply, LinearMap.id_apply] at h
  calc A.scalar f = B.scalar (B.scalar.symm (A.scalar f)) := (LinearEquiv.apply_symm_apply _ _).symm
    _ = _ := by rw [h, map_smul]

/-- **The source equality test is sound.** Equal phase-bearing images of the eighteen
generators and equal images of the zero state give equal scalar operators. -/
theorem Realization.scalar_eq {A B : Realization}
    (hx : ∀ i, A.label (xGenerator i) = B.label (xGenerator i))
    (hz : ∀ i, A.label (zGenerator i) = B.label (zGenerator i))
    (h0 : A.scalar (basisState 0) = B.scalar (basisState 0)) :
    A.scalar = B.scalar := by
  obtain ⟨c, hc⟩ := Realization.scalar_eq_smul hx hz
  have hne : B.scalar (basisState 0) ≠ 0 := by
    intro h
    have := B.scalar.injective (h.trans (map_zero _).symm)
    have h1 := congrFun this 0
    simp [basisState] at h1
  have hc1 : c = 1 := by
    have h := (hc (basisState 0)).symm.trans h0
    by_contra hc1
    apply hne
    have : (c - 1) • B.scalar (basisState 0) = 0 := by rw [sub_smul, h, one_smul, sub_self]
    exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hc1)
  apply LinearEquiv.ext
  intro f
  rw [hc, hc1, one_smul]

end IntegerMultBounds.Networks.Certificates.T16.Pauli
