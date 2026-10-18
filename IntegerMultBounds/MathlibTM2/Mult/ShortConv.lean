module

public import IntegerMultBounds.MathlibTM2.Fast.RingProd
public import IntegerMultBounds.NLogN.FixedOps
import IntegerMultBounds.Resampling.WindowSum
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-! # Short convolutions through the ring product

A ring record of size `r` holding a sequence supported on `[0, A)` and one supported on
`[0, B)` with `A + B ≤ r + 1` has the linear convolution of the two sequences as its negacyclic
product: no coefficient wraps (`negacyclicMul_recOf`). The vendored ring product computes
`Q_p(u v / r)` recordwise (`Fast/RingProd`), so on zero-padded integer records of size
`r = 2^l` its output numerators are the truncated divisions of the integer convolution by
`2^(p+l)` (`rpOut_recOf`). Both the triangular Toeplitz products of the phase-cell solve
(`lower`) and the block correlations of the chirped forward map are such convolutions.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast Finset
open IntegerMultBounds.Spec.SignedRingProduct (gridPoly)

/-- The record of size `r` holding the first `r` terms of a sequence. -/
def recOf (r : ℕ) {β : Type*} (f : ℕ → β) : Fin r → β := fun i => f i.val

/-- **No wrap.** The negacyclic product of two records whose sequences are supported on
`[0, A)` and `[0, B)`, `A + B ≤ r + 1`, is the linear convolution. -/
theorem negacyclicMul_recOf {r : ℕ} (f g : ℕ → ℂ) (A B : ℕ) (hAB : A+B≤r+1)
    (hf : ∀ i, A ≤ i → f i=0) (hg : ∀ j, B ≤ j → g j=0) (n : Fin r) :
    negacyclicMul (recOf r f) (recOf r g) n=∑ i∈range (n.val+1), f i*g (n.val-i) := by
  unfold negacyclicMul recOf negaSign negaIdx
  have hwrap : ∀ i : Fin r, ¬i≤n → f i.val*g (n-i).val=0 := by
    intro i hi
    rw [Fin.not_le] at hi
    by_cases hA : A ≤ i.val
    · rw [hf _ hA, zero_mul]
    · have hv := Fin.coe_sub_iff_lt.mpr hi
      rw [hg _ (by omega), mul_zero]
  have hterm : ∀ i : Fin r, (if i≤n then (1 : ℂ) else -1)*f i.val*g (n-i).val=
      if i.val≤n.val then f i.val*g (n.val-i.val) else 0 := by
    intro i
    by_cases hin : i≤n
    · rw [ite_eq_left hin, ite_eq_left (Fin.le_def.mp hin), one_mul, Fin.coe_sub_iff_le.mpr hin]
    · rw [ite_eq_right hin, ite_eq_right (fun h => hin (Fin.le_def.mpr h)), mul_assoc, hwrap i hin,
        mul_zero]
  rw [Finset.sum_congr rfl fun i _ => hterm i,
    Fin.sum_univ_eq_sum_range (fun i => if i≤n.val then f i*g (n.val-i) else 0) r,
    ←Finset.sum_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_range]
  have := n.isLt
  omega

/-- The truncated linear convolution of two integer sequences at index `c`. -/
def convZ (x y : ℕ → GaussianInt) (c : ℕ) : GaussianInt := ∑ i∈range (c+1), x i*y (c-i)

/-- **Short convolutions on the ring product.** On zero-padded records of size `2^l` the
output numerators of the ring product are the truncated divisions of the integer convolution
by `2^(p+l)`. -/
theorem rpOut_recOf (p l : ℕ) (x y : ℕ → ℕ → GaussianInt) (A B : ℕ) (hAB : A+B≤2^l+1)
    (hx : ∀ n i, A ≤ i → x n i=0) (hy : ∀ n j, B ≤ j → y n j=0) (n : ℕ) (c : Fin (2^l)) :
    rpOut p (fun n => recOf (2^l) (x n)) (fun n => recOf (2^l) (y n)) n c=
      ⟨(convZ (x n) (y n) c).re.tdiv (2^(p+l)), (convZ (x n) (y n) c).im.tdiv (2^(p+l))⟩ := by
  have hgrid := rp_pwC_grid p (fun n => recOf (2^l) (x n)) (fun n => recOf (2^l) (y n)) n c
  set z := rpOut p (fun n => recOf (2^l) (x n)) (fun n => recOf (2^l) (y n)) n c
  -- The grid records are the records of the complex sequences.
  have hcre (w : GaussianInt) : (GaussianInt.toComplex w).re=(w.re : ℝ) := (GaussianInt.intCast_re w).symm
  have hcim (w : GaussianInt) : (GaussianInt.toComplex w).im=(w.im : ℝ) := (GaussianInt.intCast_im w).symm
  have h2c : (2 : ℂ)^p=((2^p : ℝ) : ℂ) := by push_cast; ring
  have hX : rpGrid p (fun n => recOf (2^l) (x n)) n=
      recOf (2^l) (fun i => (GaussianInt.toComplex (x n i))/2^p) := by
    funext i
    apply Complex.ext <;>
      simp only [rpGrid, gridPoly, rpRec, recOf, h2c, Complex.div_ofReal_re, Complex.div_ofReal_im,
        hcre, hcim]
  have hY : rpGrid p (fun n => recOf (2^l) (y n)) n=
      recOf (2^l) (fun i => (GaussianInt.toComplex (y n i))/2^p) := by
    funext i
    apply Complex.ext <;>
      simp only [rpGrid, gridPoly, rpRec, recOf, h2c, Complex.div_ofReal_re, Complex.div_ofReal_im,
        hcre, hcim]
  have hconv : negacyclicMul (rpGrid p (fun n => recOf (2^l) (x n)) n)
      (rpGrid p (fun n => recOf (2^l) (y n)) n) c=
      GaussianInt.toComplex (convZ (x n) (y n) c)/(2^p*2^p) := by
    rw [hX, hY, negacyclicMul_recOf _ _ A B hAB (fun i hi => by rw [hx n i hi]; simp)
      (fun j hj => by rw [hy n j hj]; simp)]
    unfold convZ
    rw [map_sum, Finset.sum_div]
    refine sum_congr rfl fun i _ => ?_
    rw [map_mul, div_mul_div_comm]
  rw [SynthErr.pwC, SynthErr.rdR, SynthErr.pwE] at hgrid
  simp only [Pi.smul_apply, smul_eq_mul] at hgrid
  rw [hconv] at hgrid
  have e : (1/((2^l : ℕ) : ℂ))*(GaussianInt.toComplex (convZ (x n) (y n) c)/(2^p*2^p))=
      GaussianInt.toComplex (convZ (x n) (y n) c)/(((2 : ℝ)^p*2^(p+l) : ℝ) : ℂ) := by
    push_cast
    rw [pow_add]
    field_simp
  rw [e] at hgrid
  have hre := congrArg Complex.re hgrid
  have him := congrArg Complex.im hgrid
  simp only [rhoC_re, rhoC_im, Complex.div_ofReal_re, Complex.div_ofReal_im,
    hcre, hcim] at hre him
  have h2 : (0 : ℝ)<2^p := by positivity
  have hsc (q : ℤ) : (2 : ℝ)^p*((q : ℝ)/(2^p*2^(p+l)))=(q : ℝ)/2^(p+l) := by
    field_simp
  rw [hsc, Resampling.WindowSum.rho0_div_pow] at hre
  rw [hsc, Resampling.WindowSum.rho0_div_pow] at him
  have hre' : z.re=(convZ (x n) (y n) c).re.tdiv (2^(p+l)) := by
    have := (div_left_inj' h2.ne').mp hre
    exact_mod_cast this.symm
  have him' : z.im=(convZ (x n) (y n) c).im.tdiv (2^(p+l)) := by
    have := (div_left_inj' h2.ne').mp him
    exact_mod_cast this.symm
  exact Zsqrtd.ext hre' him'

/-- The computed pointwise products of zero-padded records are the rounded convolutions:
`Q_p(conv / r)` coefficientwise. -/
theorem pwC_recOf {r : ℕ} [NeZero r] (p : ℕ) (u v : ℕ → ℕ → ℂ) (A B : ℕ) (hAB : A+B≤r+1)
    (hu : ∀ n i, A ≤ i → u n i=0) (hv : ∀ n j, B ≤ j → v n j=0) (n : ℕ) (c : Fin r) :
    SynthErr.pwC p (fun n => recOf r (u n)) (fun n => recOf r (v n)) n c=
      rhoC p ((1/(r : ℂ))*∑ i∈range (c.val+1), u n i*v n (c.val-i)) := by
  rw [SynthErr.pwC, SynthErr.rdR, SynthErr.pwE]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [negacyclicMul_recOf _ _ A B hAB (hu n) (hv n)]

/-- The rescaled ring output is within `2r/2^p` of the convolution. -/
theorem pwC_recOf_err {r : ℕ} [NeZero r] (p : ℕ) (u v : ℕ → ℕ → ℂ) (A B : ℕ) (hAB : A+B≤r+1)
    (hu : ∀ n i, A ≤ i → u n i=0) (hv : ∀ n j, B ≤ j → v n j=0) (n : ℕ) (c : Fin r) :
    ‖(r : ℂ)*SynthErr.pwC p (fun n => recOf r (u n)) (fun n => recOf r (v n)) n c-
      ∑ i∈range (c.val+1), u n i*v n (c.val-i)‖≤2*r/2^p := by
  rw [pwC_recOf p u v A B hAB hu hv n c]
  have hr : (0 : ℝ)<r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  set S := ∑ i∈range (c.val+1), u n i*v n (c.val-i)
  have hr0 : (r : ℂ)≠0 := by exact_mod_cast (NeZero.ne r)
  have e : (r : ℂ)*rhoC p ((1/(r : ℂ))*S)-S=(r : ℂ)*(rhoC p ((1/(r : ℂ))*S)-(1/(r : ℂ))*S) := by
    rw [mul_sub, ←mul_assoc, mul_one_div_cancel hr0, one_mul]
  rw [e, norm_mul, Complex.norm_natCast]
  calc (r : ℝ)*‖rhoC p ((1/(r : ℂ))*S)-(1/(r : ℂ))*S‖≤r*(2/2^p) :=
        mul_le_mul_of_nonneg_left (norm_rhoC_sub_le_two p _) hr.le
    _ =2*r/2^p := by ring

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
