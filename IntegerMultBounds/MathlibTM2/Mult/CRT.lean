module

public import Mathlib.Data.ZMod.QuotientRing
public import IntegerMultBounds.NLogN.ResamplingPermutedNumeric
public import IntegerMultBounds.ExactRecovery
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# The CRT layout `Φ` and the normalized permutation cancellation

Paper §8, "An explicit cyclic-convolution layout", and §7, Lemma
`lem:chirp-permutation`, identity `source-permutation-cancel`.

## The map `Φ`

For pairwise coprime positive lengths `s : Fin d → ℕ` with `S = ∏ i, s i`, put
`P i = ∏_{j < i} s j` (`prefixProd`) and `μ i = (P i)⁻¹ mod s i` (`crtMu`, a unit of
`ZMod (s i)`). The paper's map `Φ : k ↦ (μ i · k mod s i)_i` is `crtPhi s hs`, an additive
equivalence `ZMod S ≃+ ((i : Fin d) → ZMod (s i))`: Mathlib's ring isomorphism
`ZMod.prodEquivPi` followed by coordinatewise multiplication by the units `μ i`.

* `crtPhi_apply`, `crtPhi_natCast`, `crtPhi_one`: `Φ k i = μ i · (k mod s i)`, so
  `Φ 1 = μ` is the exponent vector of the image `∏ x_i^{μ_i}` of `x`.
* `crtPhi_mixedRadix` (eq. `triangular-crt`): for every `a : Fin d → ℕ`,
  `Φ (∑ j, a j P j) i = a i + μ i ∑_{j < i} a j P j (mod s i)`. The digit bounds
  `a j < s j` of the paper are not needed for the identity.
* `convG_crtPhi`: `convG (u ∘ Φ⁻¹) (v ∘ Φ⁻¹) = cconv u v ∘ Φ⁻¹`
  (from `NLogN.convG_comp_symm`).

## Cancellation

The box transforms follow the vendored conventions: `NLogN.dftDCLM N` is the paper's
`F_N`, `(F_N u)_k = (∏ N i)⁻¹ ∑_j e^{-2πi ∑ k_i j_i / N_i} u_j`, and
`NLogN.permRCLM s t` is `R = ⊗ P_{s_i}`, `(R z)_k = z (t_i k_i)_i`. The positive-sign
transform `F_N⁺` with the same normalization `(∏ N i)⁻¹` is `dftDPlusCLM N`; it equals
`conj ∘ F_N ∘ conj` (`dftDPlusCLM_eq_conj`) and is a contraction.

* `permR_cancel`: `R F⁺ [(R F u) · (R F v)] = (u ∗ v) / (∏ N i)²` on the box, for any
  coordinatewise units.
* `crtSourceCLM s t hs = R F_s ∘ (· ∘ Φ⁻¹)` and `crtOppositeCLM s t hs = (· ∘ Φ) ∘ R F_s⁺`
  have operator norm at most one, and `crt_hconv` is the hypothesis `hconv` of
  `ExactRecovery.exact_product` for them, given `gcd (s i, t i) = 1`.
* `exact_product_crt` is `ExactRecovery.exact_product` with these two maps inserted.
-/

@[expose] public section


open IntegerMultBounds IntegerMultBounds.NLogN
open scoped Function

namespace IntegerMultBounds.MathlibTM2.Mult

/-! ### The map `Φ` -/

section Phi

variable {d : ℕ} (s : Fin d → ℕ)

/-- The prefix product `P i = ∏_{j < i} s j`. -/
def prefixProd (i : Fin d) : ℕ := ∏ j ∈ Finset.Iio i, s j

variable {s}

theorem coprime_prefixProd (hs : Pairwise (Nat.Coprime on s)) (i : Fin d) :
    Nat.Coprime (prefixProd s i) (s i) :=
  Nat.Coprime.prod_left fun _ hj => hs (ne_of_lt (Finset.mem_Iio.1 hj))

theorem dvd_prefixProd {i j : Fin d} (hij : i < j) : s i ∣ prefixProd s j :=
  Finset.dvd_prod_of_mem s (Finset.mem_Iio.2 hij)

variable (s) in
/-- `μ i = (P i)⁻¹` modulo `s i`. -/
def crtMu (hs : Pairwise (Nat.Coprime on s)) (i : Fin d) : (ZMod (s i))ˣ :=
  (ZMod.unitOfCoprime (prefixProd s i) (coprime_prefixProd hs i))⁻¹

theorem crtMu_mul_prefixProd (hs : Pairwise (Nat.Coprime on s)) (i : Fin d) :
    (crtMu s hs i : ZMod (s i)) * (prefixProd s i : ZMod (s i)) = 1 := by
  rw [crtMu, ← ZMod.coe_unitOfCoprime _ (coprime_prefixProd hs i), Units.inv_mul]

variable (s) in
/-- The layout map `Φ : k ↦ (μ i · k mod s i)_i`: the Chinese remainder ring isomorphism
followed by multiplication by the units `μ i`. -/
noncomputable def crtPhi (hs : Pairwise (Nat.Coprime on s)) :
    ZMod (∏ i, s i) ≃+ ((i : Fin d) → ZMod (s i)) where
  toFun k i := (crtMu s hs i : ZMod (s i)) * ZMod.prodEquivPi s hs k i
  invFun x := (ZMod.prodEquivPi s hs).symm fun i => ((crtMu s hs i)⁻¹ : (ZMod (s i))ˣ) * x i
  left_inv k := by
    simp only [← mul_assoc, Units.inv_mul, one_mul]
    exact (ZMod.prodEquivPi s hs).symm_apply_apply k
  right_inv x := by
    funext i
    simp only [RingEquiv.apply_symm_apply, ← mul_assoc, Units.mul_inv, one_mul]
  map_add' a b := by
    funext i
    simp only [map_add, Pi.add_apply, mul_add]

theorem crtPhi_apply (hs : Pairwise (Nat.Coprime on s)) (k : ZMod (∏ i, s i)) (i : Fin d) :
    crtPhi s hs k i = (crtMu s hs i : ZMod (s i)) * ZMod.cast k := by
  simp [crtPhi, ZMod.prodEquivPi_apply, ZMod.castHom_apply]

theorem crtPhi_natCast (hs : Pairwise (Nat.Coprime on s)) (n : ℕ) (i : Fin d) :
    crtPhi s hs (n : ZMod (∏ i, s i)) i = (crtMu s hs i : ZMod (s i)) * (n : ZMod (s i)) := by
  rw [crtPhi_apply, ZMod.cast_natCast (Finset.dvd_prod_of_mem s (Finset.mem_univ i))]

/-- `Φ 1 = μ`: the generator `x` goes to `∏ x_i^{μ_i}`. -/
theorem crtPhi_one (hs : Pairwise (Nat.Coprime on s)) (i : Fin d) :
    crtPhi s hs 1 i = (crtMu s hs i : ZMod (s i)) := by
  simpa using crtPhi_natCast hs 1 i

/-- The triangular formula (eq. `triangular-crt`): for `k = ∑ j, a j P j`,
`Φ k i = a i + μ i ∑_{j < i} a j P j (mod s i)`. -/
theorem crtPhi_mixedRadix (hs : Pairwise (Nat.Coprime on s)) (a : Fin d → ℕ) (i : Fin d) :
    crtPhi s hs ((∑ j, a j * prefixProd s j : ℕ) : ZMod (∏ i, s i)) i =
      (a i : ZMod (s i)) + (crtMu s hs i : ZMod (s i)) *
        ((∑ j ∈ Finset.Iio i, a j * prefixProd s j : ℕ) : ZMod (s i)) := by
  rw [crtPhi_natCast, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· < i)]
  have h1 : Finset.univ.filter (· < i) = Finset.Iio i := by ext j; simp
  have h2 : ∑ j ∈ Finset.univ.filter (fun j => ¬ j < i), a j * prefixProd s j ≡
      a i * prefixProd s i [MOD s i] := by
    rw [← Finset.add_sum_erase _ _ (by simp : i ∈ Finset.univ.filter (fun j => ¬ j < i))]
    have : ∑ j ∈ (Finset.univ.filter (fun j => ¬ j < i)).erase i, a j * prefixProd s j ≡
        0 [MOD s i] := by
      rw [Nat.modEq_zero_iff_dvd]
      refine Finset.dvd_sum fun j hj => ?_
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
      exact Dvd.dvd.mul_left (dvd_prefixProd (lt_of_le_of_ne hj.2 (Ne.symm hj.1))) _
    simpa using Nat.ModEq.add_left (a i * prefixProd s i) this
  rw [h1, Nat.cast_add, (ZMod.natCast_eq_natCast_iff _ _ _).2 h2, mul_add, add_comm]
  congr 1
  push_cast
  rw [mul_left_comm, crtMu_mul_prefixProd, mul_one]

end Phi

/-- A product of nonzero lengths is nonzero. -/
instance prodNeZero {d : ℕ} (s : Fin d → ℕ) [∀ i, NeZero (s i)] : NeZero (∏ i, s i) :=
  ⟨Finset.prod_ne_zero_iff.2 fun i _ => NeZero.ne (s i)⟩

section Conv

variable {d : ℕ} {s : Fin d → ℕ} [∀ i, NeZero (s i)] {R : Type*} [CommRing R]

/-- Cyclic convolution of length `S` is convolution on the box, transported by `Φ`. -/
theorem convG_crtPhi (hs : Pairwise (Nat.Coprime on s)) (u v : ZMod (∏ i, s i) → R) :
    convG (u ∘ (crtPhi s hs).symm) (v ∘ (crtPhi s hs).symm) =
      cconv u v ∘ (crtPhi s hs).symm := by
  rw [cconv_eq_convG]
  exact convG_comp_symm (crtPhi s hs) u v

end Conv

/-! ### Transforms on the box -/

section Transforms

open Real Complex ContinuousLinearMap

/-- Precomposition `u ↦ u ∘ f` as a continuous linear map. -/
noncomputable def compCLM {α β : Type*} (f : α → β) : (β → ℂ) →L[ℂ] (α → ℂ) :=
  ContinuousLinearMap.pi fun a => ContinuousLinearMap.proj (f a)

@[simp] theorem compCLM_apply {α β : Type*} (f : α → β) (u : β → ℂ) : compCLM f u = u ∘ f :=
  rfl

theorem opNorm_compCLM_le {α β : Type*} [Fintype α] [Fintype β] (f : α → β) :
    ‖compCLM f‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun u => by
    rw [one_mul]
    exact norm_comp_le_pi_norm f u

variable {d : ℕ} {N : Fin d → ℕ} [∀ i, NeZero (N i)]

/-- The normalized positive-sign transform
`(F_N⁺ u)_k = (∏ N i)⁻¹ ∑_j e^{2πi ∑ k_i j_i / N_i} u_j`. -/
noncomputable def dftDPlusCLM (N : Fin d → ℕ) [∀ i, NeZero (N i)] :
    (((i : Fin d) → ZMod (N i)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (N i)) → ℂ) :=
  ContinuousLinearMap.pi fun k => ∑ j,
    ((1 / ((∏ i, N i : ℕ) : ℂ)) * ∏ i, chrZ (N i) (k i * j i)) • ContinuousLinearMap.proj j

theorem dftDPlusCLM_apply (u : ((i : Fin d) → ZMod (N i)) → ℂ) :
    dftDPlusCLM N u = fun k => (1 / ((∏ i, N i : ℕ) : ℂ)) *
      dftD (fun i => Complex.exp (2 * π * I / (N i))) u k := by
  funext k
  simp only [dftDPlusCLM, pi_apply, sum_apply, smul_apply, proj_apply, smul_eq_mul]
  unfold dftD
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [chrZ_eq_pow, mul_comm (k i) (j i)]

theorem opNorm_dftDPlusCLM_le : ‖dftDPlusCLM N‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one fun u => ?_
  rw [one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro k
  have hN : (0 : ℝ) < (∏ i, N i : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne _)
  simp only [dftDPlusCLM, pi_apply, sum_apply, smul_apply, proj_apply, smul_eq_mul]
  calc ‖∑ j, (1 / ((∏ i, N i : ℕ) : ℂ) * ∏ i, chrZ (N i) (k i * j i)) * u j‖
      ≤ ∑ j, ‖(1 / ((∏ i, N i : ℕ) : ℂ) * ∏ i, chrZ (N i) (k i * j i)) * u j‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j : (i : Fin d) → ZMod (N i), 1 / ((∏ i, N i : ℕ) : ℝ) * ‖u‖ := by
        gcongr with j
        rw [norm_mul, norm_mul, norm_prod]
        simp only [chrZ, norm_chr, Finset.prod_const_one, mul_one, norm_div, norm_one,
          Complex.norm_natCast]
        gcongr
        exact norm_le_pi_norm u j
    _ = ‖u‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi, nsmul_eq_mul]
        simp only [ZMod.card]
        field_simp

theorem conj_chrZ (n : ℕ) [NeZero n] (m : ZMod n) :
    starRingEnd ℂ (chrZ n m) = chrZ n (-m) := by
  have h1 : ‖chrZ n m‖ = 1 := by rw [chrZ, norm_chr]
  have h2 : Complex.normSq (chrZ n m) = 1 := by
    rw [Complex.normSq_eq_norm_sq, h1, one_pow]
  rw [chrZ_neg', Complex.inv_def, h2, inv_one, Complex.ofReal_one, mul_one]

/-- `F_N⁺ = conj ∘ F_N ∘ conj`. -/
theorem dftDPlusCLM_eq_conj (u : ((i : Fin d) → ZMod (N i)) → ℂ)
    (k : (i : Fin d) → ZMod (N i)) :
    dftDPlusCLM N u k = starRingEnd ℂ (dftDCLM N (fun j => starRingEnd ℂ (u j)) k) := by
  simp only [dftDPlusCLM, dftDCLM, pi_apply, sum_apply, smul_apply, proj_apply, smul_eq_mul,
    map_sum, map_mul, map_prod, Complex.conj_conj, map_div₀, map_one, map_natCast, conj_chrZ,
    neg_neg]

/-- `R = ⊗ P_{s_i}` reads the input at `(t_i k_i)_i`. -/
theorem permRCLM_apply (s t : Fin d → ℕ) [∀ i, NeZero (s i)]
    (z : ((i : Fin d) → ZMod (s i)) → ℂ) (k : (i : Fin d) → ZMod (s i)) :
    permRCLM s t z k = z fun i => (t i : ZMod (s i)) * k i := by
  rw [permRCLM, tensorRCLM_apply]
  have hm : ∀ i (a b : ZMod (s i)), matOf (permSCLM (s := s i) (t i)) a b =
      if (t i : ZMod (s i)) * a = b then 1 else 0 := by
    intro i a b
    simp only [matOf, permSCLM_apply, permS, Pi.single_apply]
  rw [Fintype.sum_eq_single (fun i => (t i : ZMod (s i)) * k i)]
  · rw [Finset.prod_eq_one fun i _ => by rw [hm]; simp, one_mul]
  · intro j hj
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hj
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hm, Ne.symm hi]), zero_mul]

/-- The positive root `exp (2πi/n)` is primitive. -/
theorem isPrimitiveRoot_rootP (n : ℕ) [NeZero n] :
    IsPrimitiveRoot (Complex.exp (2 * π * I / n)) n :=
  Complex.isPrimitiveRoot_exp n (NeZero.ne n)

/-- Inverting the roots reflects the frequency index. -/
theorem dftD_inv_root {ζ : Fin d → ℂ} (hζ : ∀ i, IsPrimitiveRoot (ζ i) (N i))
    (a : ((i : Fin d) → ZMod (N i)) → ℂ) (k : (i : Fin d) → ZMod (N i)) :
    dftD (fun i => (ζ i)⁻¹) a k = dftD ζ a (-k) := by
  unfold dftD
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have h := pow_val_add (hζ i) (j i * -k i) (j i * k i)
  rw [← mul_add, neg_add_cancel, mul_zero, ZMod.val_zero, pow_zero] at h
  rw [Pi.neg_apply, inv_pow, eq_comm]
  exact eq_inv_of_mul_eq_one_left h.symm

/-- Inversion: the transform at `ζ` undoes the transform at `ζ⁻¹` up to the factor `∏ N i`. -/
theorem dftD_dftD_inv {ζ : Fin d → ℂ} (hζ : ∀ i, IsPrimitiveRoot (ζ i) (N i))
    (a : ((i : Fin d) → ZMod (N i)) → ℂ) :
    dftD ζ (dftD (fun i => (ζ i)⁻¹) a) = fun k => (∏ i, (N i : ℂ)) * a k := by
  funext k
  have hζ' : ∀ i, IsPrimitiveRoot ((ζ i)⁻¹) (N i) := fun i => (hζ i).inv
  have e : dftD ζ (dftD (fun i => (ζ i)⁻¹) a) k =
      dftD (fun i => (ζ i)⁻¹) (dftD (fun i => (ζ i)⁻¹) a) (-k) := by
    rw [← dftD_inv_root hζ']
    simp only [inv_inv]
  rw [e, dftD_dftD hζ']
  simp only [neg_neg]

theorem dftD_const_mul (ζ : Fin d → ℂ) (c : ℂ) (a : ((i : Fin d) → ZMod (N i)) → ℂ) :
    dftD ζ (fun k => c * a k) = fun k => c * dftD ζ a k := by
  funext k
  simp only [dftD, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- With both normalizations `(∏ N i)⁻¹`: `F⁺ (F u · F v) = (u ∗ v) / (∏ N i)²`. -/
theorem dftDPlusCLM_mul_dftDCLM (u v : ((i : Fin d) → ZMod (N i)) → ℂ) :
    dftDPlusCLM N (fun k => dftDCLM N u k * dftDCLM N v k) =
      fun k => convG u v k / ((∏ i, N i : ℕ) : ℂ) ^ 2 := by
  have hζ := fun i => isPrimitiveRoot_rootP (N i)
  have hζ' : ∀ i, IsPrimitiveRoot ((Complex.exp (2 * π * I / (N i)))⁻¹) (N i) :=
    fun i => (hζ i).inv
  have hS : ((∏ i, N i : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne _)
  have e : (fun k => dftDCLM N u k * dftDCLM N v k) = fun k =>
      (1 / ((∏ i, N i : ℕ) : ℂ)) ^ 2 *
        dftD (fun i => (Complex.exp (2 * π * I / (N i)))⁻¹) (convG u v) k := by
    rw [dftD_convG hζ', dftDCLM_apply, dftDCLM_apply]
    funext k
    ring
  rw [e, dftDPlusCLM_apply, dftD_const_mul, dftD_dftD_inv hζ]
  funext k
  rw [← Nat.cast_prod]
  field_simp

/-- `F⁺ R_c = R_{c⁻¹} F⁺`. -/
theorem dftDPlusCLM_permR (c : (i : Fin d) → (ZMod (N i))ˣ)
    (z : ((i : Fin d) → ZMod (N i)) → ℂ) :
    dftDPlusCLM N (permR c z) = permR (fun i => (c i)⁻¹) (dftDPlusCLM N z) := by
  rw [dftDPlusCLM_apply, dftD_permR, dftDPlusCLM_apply]
  rfl

/-- Normalized permutation cancellation on the box (eq. `source-permutation-cancel`):
`R F⁺ [(R F u) · (R F v)] = (u ∗ v) / (∏ N i)²` for coordinatewise units `c`. -/
theorem permR_cancel (c : (i : Fin d) → (ZMod (N i))ˣ)
    (u v : ((i : Fin d) → ZMod (N i)) → ℂ) :
    permR c (dftDPlusCLM N fun k => permR c (dftDCLM N u) k * permR c (dftDCLM N v) k) =
      fun k => convG u v k / ((∏ i, N i : ℕ) : ℂ) ^ 2 := by
  rw [permR_mul, dftDPlusCLM_permR, permR_inv, dftDPlusCLM_mul_dftDCLM]

end Transforms

/-! ### The source and opposite maps on `ZMod S` -/

/-- A composite of two contractions is a contraction. -/
theorem opNorm_comp_le_one {E F G : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] [SeminormedAddCommGroup G] [NormedSpace ℂ E] [NormedSpace ℂ F]
    [NormedSpace ℂ G] {f : F →L[ℂ] G} {g : E →L[ℂ] F} (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 1) :
    ‖f.comp g‖ ≤ 1 :=
  calc ‖f.comp g‖ ≤ ‖f‖ * ‖g‖ := f.opNorm_comp_le g
    _ ≤ 1 * 1 := mul_le_mul hf hg (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

section Source

open ContinuousLinearMap

variable {d : ℕ} (s t : Fin d → ℕ) [∀ i, NeZero (s i)] (hs : Pairwise (Nat.Coprime on s))

theorem opNorm_permRCLM_le : ‖permRCLM s t‖ ≤ 1 :=
  opNorm_tensorRCLM_le _ fun _ => opNorm_permSCLM_le

theorem opNorm_dftDCLM_le : ‖dftDCLM s‖ ≤ 1 := by
  rw [dftDCLM_eq_tensor]
  exact opNorm_tensorRCLM_le _ fun _ => opNorm_dftCLM_le

/-- `F = R F_s ∘ Φ`: `u ↦ R F_s (u ∘ Φ⁻¹)`. -/
noncomputable def crtSourceCLM :
    (ZMod (∏ i, s i) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (s i)) → ℂ) :=
  (permRCLM s t ∘L dftDCLM s) ∘L compCLM (crtPhi s hs).symm

/-- `G = Φ⁻¹ ∘ R F_s⁺`: `y ↦ (R F_s⁺ y) ∘ Φ`. -/
noncomputable def crtOppositeCLM :
    (((i : Fin d) → ZMod (s i)) → ℂ) →L[ℂ] (ZMod (∏ i, s i) → ℂ) :=
  compCLM (crtPhi s hs) ∘L (permRCLM s t ∘L dftDPlusCLM s)

theorem opNorm_crtSourceCLM_le : ‖crtSourceCLM s t hs‖ ≤ 1 :=
  opNorm_comp_le_one (opNorm_comp_le_one (opNorm_permRCLM_le s t) (opNorm_dftDCLM_le s))
    (opNorm_compCLM_le _)

theorem opNorm_crtOppositeCLM_le : ‖crtOppositeCLM s t hs‖ ≤ 1 :=
  opNorm_comp_le_one (opNorm_compCLM_le _)
    (opNorm_comp_le_one (opNorm_permRCLM_le s t) opNorm_dftDPlusCLM_le)

/-- The hypothesis `hconv` of `ExactRecovery.exact_product`:
`G (F u · F v) = (u ∗ v) / S²` for `F = R F_s ∘ Φ`, `G = Φ⁻¹ ∘ R F_s⁺`. -/
theorem crt_hconv (hcop : ∀ i, Nat.Coprime (s i) (t i)) (u v : ZMod (∏ i, s i) → ℂ) :
    crtOppositeCLM s t hs (fun j => crtSourceCLM s t hs u j * crtSourceCLM s t hs v j) =
      fun i => cconv u v i / ((∏ i, s i : ℕ) : ℂ) ^ 2 := by
  set c : (i : Fin d) → (ZMod (s i))ˣ := fun i => ZMod.unitOfCoprime (t i) (hcop i).symm
  have hR : ∀ z, permRCLM s t z = permR c z := fun z => by
    funext k
    rw [permRCLM_apply]
    simp only [permR, c, ZMod.coe_unitOfCoprime]
  funext i
  simp only [crtSourceCLM, crtOppositeCLM, comp_apply, compCLM_apply, hR]
  rw [permR_cancel c, convG_crtPhi hs u v]
  simp

/-- `ExactRecovery.exact_product` with `F = R F_s ∘ Φ` and `G = Φ⁻¹ ∘ R F_s⁺`: only the
computed procedures and the size conditions remain as hypotheses. -/
theorem exact_product_crt (hcop : ∀ i, Nat.Coprime (s i) (t i)) {k p : ℕ} {Es : ℝ}
    (F' : (ZMod (∏ i, s i) → ℂ) → (((i : Fin d) → ZMod (s i)) → ℂ))
    (G' : (((i : Fin d) → ZMod (s i)) → ℂ) → (ZMod (∏ i, s i) → ℂ))
    (hk : 0 < k) {x y : List Bool}
    (hS : (digitsOf k x).length + (digitsOf k y).length ≤ (∏ i, s i) + 1)
    (hF' : ∀ u : ZMod (∏ i, s i) → ℂ, ‖u‖ ≤ 1 / 2 →
      2 ^ p * ‖F' u - crtSourceCLM s t hs u‖ ≤ Es)
    (hG' : ∀ y : ((i : Fin d) → ZMod (s i)) → ℂ, ‖y‖ ≤ 1 / 2 →
      2 ^ p * ‖G' y - crtOppositeCLM s t hs y‖ ≤ Es)
    (hEs : Es ≤ 2 ^ p / 100)
    (hfinal : (2 : ℝ) ^ (2 * k + 4) * ((∏ i, s i : ℕ) : ℝ) ^ 2 * (3 * Es + 2) < 2 ^ p / 2) :
    evalBase (2 ^ k) (List.ofFn fun i : Fin (∏ i, s i) =>
      (round (((2 : ℂ) ^ (2 * k) * ((∏ i, s i : ℕ) : ℂ)) *
        ExactRecovery.computedConv (p := p) (k := k) F' G' x y
          (i.val : ZMod (∏ i, s i))).re).toNat) =
      IntegerMultBounds.Machine.binaryValue x * IntegerMultBounds.Machine.binaryValue y :=
  ExactRecovery.exact_product (crtSourceCLM s t hs) F' (crtOppositeCLM s t hs) G' hk hS
    (opNorm_crtSourceCLM_le s t hs) hF' (opNorm_crtOppositeCLM_le s t hs) hG' hEs
    (crt_hconv s t hs hcop) hfinal

end Source

end IntegerMultBounds.MathlibTM2.Mult
