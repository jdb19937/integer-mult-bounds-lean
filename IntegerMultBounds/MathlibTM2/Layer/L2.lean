module

public import IntegerMultBounds.MathlibTM2.Layer.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The `ℓ²` norm of an array

`l2 f = √(Σ ‖f x‖²)` for a complex function on a finite type, with the norm facts of a Euclidean
space (`l2_eq_norm`): the triangle inequality, homogeneity, invariance under a permutation of the
entries, conjugation and multiplication by unit scalars, and the comparisons with the entries.
The kernels `kBit 1 i` are isometries (`l2_kBit`): each pair `(f p, f (flip p))` is mapped by the
unitary matrix `[[1+i, 1-i], [1-i, 1+i]]/2`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Layer

open IntegerMultBounds.Networks

section Basic

variable {X : Type*} [Fintype X]

/-- The `ℓ²` norm of a complex function on a finite type. -/
noncomputable def l2 (f : X → ℂ) : ℝ := √(∑ x, ‖f x‖ ^ 2)

lemma l2_eq_norm (f : X → ℂ) : l2 f = ‖(WithLp.toLp 2 f : EuclideanSpace ℂ X)‖ := by
  rw [EuclideanSpace.norm_eq]; rfl

lemma l2_nonneg (f : X → ℂ) : 0 ≤ l2 f := Real.sqrt_nonneg _

lemma l2_add_le (f g : X → ℂ) : l2 (f + g) ≤ l2 f + l2 g := by
  simp only [l2_eq_norm, WithLp.toLp_add]; exact norm_add_le _ _

lemma l2_smul (c : ℂ) (f : X → ℂ) : l2 (c • f) = ‖c‖ * l2 f := by
  simp only [l2_eq_norm, WithLp.toLp_smul]; exact norm_smul _ _

lemma l2_comp_equiv (σ : X ≃ X) (f : X → ℂ) : l2 (f ∘ σ) = l2 f := by
  unfold l2; congr 1; exact Equiv.sum_comp σ (fun x => ‖f x‖ ^ 2)

lemma l2_star (f : X → ℂ) : l2 (fun x => star (f x)) = l2 f := by
  unfold l2; simp

lemma norm_le_l2 (f : X → ℂ) (x : X) : ‖f x‖ ≤ l2 f := by
  unfold l2
  rw [Real.le_sqrt (norm_nonneg _) (Finset.sum_nonneg fun _ _ => by positivity)]
  exact Finset.single_le_sum (f := fun x => ‖f x‖ ^ 2) (fun _ _ => by positivity)
    (Finset.mem_univ x)

lemma l2_le_of_norm_le {c : ℝ} (hc : 0 ≤ c) (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ c) :
    l2 f ≤ √(Fintype.card X) * c := by
  unfold l2
  rw [← Real.sqrt_sq hc, ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  calc ∑ x, ‖f x‖ ^ 2 ≤ ∑ _x : X, c ^ 2 :=
        Finset.sum_le_sum fun x _ => pow_le_pow_left₀ (norm_nonneg _) (hf x) 2
    _ = (Fintype.card X : ℝ) * c ^ 2 := by simp

end Basic

/-! ### The kernels -/

section Kernel

variable {Y : Type} [Fintype Y] {n : ℕ}

lemma kBit_norm_sq (a b : ℂ) :
    ‖(1 + Complex.I) / 2 * a + (1 - Complex.I) / 2 * b‖ ^ 2 +
      ‖(1 + Complex.I) / 2 * b + (1 - Complex.I) / 2 * a‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.div_re,
    Complex.div_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, Complex.sub_re,
    Complex.sub_im, Complex.normSq_ofNat, Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- The kernel with phase one on an active bit preserves the `ℓ²` norm. -/
lemma l2_kBit (i : Fin n) (f : Arr Y n) : l2 (kBit 1 i f) = l2 f := by
  have hph : BinaryPhase.phase 1 = Complex.I := by
    rw [BinaryPhase.phase, show (1 : ZMod 4).val = 1 from rfl, pow_one]
  -- pair each entry with its flip
  let σ : Y × (Fin n → ZMod 2) ≃ Y × (Fin n → ZMod 2) :=
    ⟨fun p => (p.1, flip i p.2), fun p => (p.1, flip i p.2), fun p => by simp,
      fun p => by simp⟩
  have key : ∑ p, ‖kBit 1 i f p‖ ^ 2 = ∑ p, ‖f p‖ ^ 2 := by
    have h2 : ∀ g : Y × (Fin n → ZMod 2) → ℝ, ∑ p, g p = (∑ p, (g p + g (σ p))) / 2 := by
      intro g
      rw [Finset.sum_add_distrib, Equiv.sum_comp σ g]; ring
    rw [h2 (fun p => ‖kBit 1 i f p‖ ^ 2), h2 (fun p => ‖f p‖ ^ 2)]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [kBit_apply, hph, σ, Equiv.coe_fn_mk, flip_flip]
    exact kBit_norm_sq (f p) (f (p.1, flip i p.2))
  unfold l2; rw [key]

/-- A product of phase-one kernels preserves the `ℓ²` norm. -/
lemma l2_prod_kBit (l : List (Fin n)) (f : Arr Y n) :
    l2 ((l.map fun i => kBit (X := Y) 1 i).prod f) = l2 f := by
  induction l generalizing f with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [l2_kBit, ih]

end Kernel

end IntegerMultBounds.MathlibTM2.Layer
