module

public import IntegerMultBounds.NLogN.SchurLU
import IntegerMultBounds.NLogN.SchurBlockError

/-! Rounded triangular solves with rounded factors. Computed multipliers and
pivot rows differ from the exact elimination factors by row sums `εL`, `εU`;
forward substitution rounds each unit-diagonal row within `η`, and back
substitution leaves pivot-row residual `δ`. Under the smallness condition
`(Λ εU + εL (M + εU))/μ ≤ 1/2`, the computed solution is within
`2 ((Λ δ + η + εL δ)/μ + c X)` of the exact one, where `X` bounds the exact
solution and `c` is the smallness ratio. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.SchurDominance

open scoped BigOperators
open Finset
variable {ι : Type*} [DecidableEq ι]

theorem luL_diag (A : Matrix ι ι ℝ) (S : Finset ι) (ks : List ι) (i : ι) (hi : i∈S) :
    luL A S ks i i=1 := by
  induction ks generalizing A S with
  | nil => simp [luL, hi]
  | cons k ks ih =>
    by_cases hk : k∈S
    · simp only [luL, hk, ite_true]
      by_cases hik : i=k
      · simp [hik]
      · simp only [hik, ite_false]
        exact ih _ _ (mem_erase.mpr ⟨hik, hi⟩)
    · simp only [luL, hk, ite_false]
      exact ih _ _ hi

theorem rounded_lu (A Lh Uh : Matrix ι ι ℝ) (S : Finset ι) (μ : ℝ) (hμ : 0<μ)
    (hA : DominatesOn A S μ) (ks : List ι) (x b xh y : ι → ℝ) (hx : Solves A S x b)
    (Λ M εL εU η δ X : ℝ) (hδ : 0≤δ) (hεL : 0≤εL) (hεU : 0≤εU) (hX : 0≤X)
    (hΛ : ∀ i∈S, ∑ k∈S, |luL A S ks i k|≤Λ) (hΛ0 : 0≤Λ) (hM0 : 0≤M)
    (hM : ∀ k∈S, ∑ j∈S, |luU A S ks k j|≤M)
    (hLh : ∀ i∈S, ∑ k∈S, |Lh i k-luL A S ks i k|≤εL)
    (hUh : ∀ k∈S, ∑ j∈S, |Uh k j-luU A S ks k j|≤εU)
    (hxX : ∀ j∈S, |x j|≤X)
    (hf : ∀ k∈S, |y k+∑ j∈S.erase k, Lh k j*y j-b k|≤η)
    (hb : ∀ k∈S, |∑ j∈S, Uh k j*xh j-y k|≤δ)
    (hsmall : (Λ*εU+εL*(M+εU))/μ≤1/2) (j : ι) (hj : j∈S) :
    |xh j-x j|≤2*((Λ*δ+η+εL*δ)/μ+(Λ*εU+εL*(M+εU))/μ*X) := by
  obtain ⟨m, hm, hmax⟩ := exists_max_image S (fun j => |xh j-x j|) ⟨j, hj⟩
  set E := |xh m-x m|
  have hE0 : 0≤E := abs_nonneg _
  have hxh : ∀ i∈S, |xh i|≤X+E := fun i hi => by
    have := abs_add_le (xh i-x i) (x i)
    rw [sub_add_cancel] at this
    linarith [hmax i hi, hxX i hi]
  -- Exact-factor residuals of the computed substitutions.
  have hbE : ∀ k∈S, |∑ j∈S, luU A S ks k j*xh j-y k|≤δ+εU*(X+E) := by
    intro k hk
    have hd := row_bound (Uh-luU A S ks) S xh k εU (X+E) (by simpa using hUh k hk)
      (by linarith) hxh
    have heq : ∑ j∈S, luU A S ks k j*xh j-y k=
        (∑ j∈S, Uh k j*xh j-y k)-∑ j∈S, (Uh-luU A S ks) k j*xh j := by
      simp only [Matrix.sub_apply, sub_mul, sum_sub_distrib]
      ring
    rw [heq]
    exact (abs_sub _ _).trans (add_le_add (hb k hk) hd)
  have hyb : ∀ k∈S, |y k|≤(M+εU)*(X+E)+δ := by
    intro k hk
    have hU := row_bound (luU A S ks) S xh k M (X+E) (hM k hk) (by linarith) hxh
    have := hbE k hk
    have h3 := abs_sub_abs_le_abs_sub (∑ j∈S, luU A S ks k j*xh j) (y k)
    have h4 : |y k|≤|∑ j∈S, luU A S ks k j*xh j|+|∑ j∈S, luU A S ks k j*xh j-y k| := by
      have := abs_sub_abs_le_abs_sub (y k) (∑ j∈S, luU A S ks k j*xh j)
      rw [abs_sub_comm (y k)] at this
      linarith
    nlinarith
  have hfE : ∀ i∈S, |∑ k∈S, luL A S ks i k*y k-b i|≤η+εL*((M+εU)*(X+E)+δ) := by
    intro i hi
    have hmassE : ∑ k∈S.erase i, |(Lh-luL A S ks) i k|≤εL :=
      (sum_le_sum_of_subset_of_nonneg (erase_subset i S) fun _ _ _ => abs_nonneg _).trans
        (by simpa using hLh i hi)
    have hd := row_bound (Lh-luL A S ks) (S.erase i) y i εL ((M+εU)*(X+E)+δ) hmassE
      (add_nonneg (mul_nonneg (add_nonneg hM0 hεU) (by linarith)) hδ)
      (fun k hk => hyb k (mem_of_mem_erase hk))
    have hsplitL := sum_erase_add S (fun k => luL A S ks i k*y k) hi
    have heq : ∑ k∈S, luL A S ks i k*y k-b i=
        (y i+∑ k∈S.erase i, Lh i k*y k-b i)-∑ k∈S.erase i, (Lh-luL A S ks) i k*y k := by
      rw [←hsplitL, luL_diag A S ks i hi]
      simp only [Matrix.sub_apply, sub_mul, sum_sub_distrib]
      ring
    rw [heq]
    exact (abs_sub _ _).trans (add_le_add (hf i hi) hd)
  have hres := lu_residual A (luL A S ks) (luU A S ks) S (fun i hi j hj => lu_eq A S μ hμ hA ks i j hi hj)
    μ hμ hA x b hx Λ hΛ xh y _ _
    (add_nonneg hδ (mul_nonneg hεU (by linarith))) hfE hbE m hm
  set c := (Λ*εU+εL*(M+εU))/μ
  have hE : E≤(Λ*δ+η+εL*δ)/μ+c*(X+E) := by
    refine hres.trans (le_of_eq ?_)
    simp only [c]
    field_simp
    ring
  have hc0 : 0≤c :=
    div_nonneg (add_nonneg (mul_nonneg hΛ0 hεU) (mul_nonneg hεL (add_nonneg hM0 hεU))) hμ.le
  have hE' : E≤2*((Λ*δ+η+εL*δ)/μ+c*X) := by nlinarith
  exact (hmax j hj).trans hE'

/-- Backward-error form: computed factors whose product is the matrix up to a
perturbation of row mass `εS`. With computed multiplier rows at most `Λ`,
forward rows rounded within `η`, back residual `δ` and `εS/μ ≤ 1/2`, the
computed solution is within `2((Λδ+η)/μ + (εS/μ) X)` of the exact one. -/
theorem backward_lu (A Lh Uh : Matrix ι ι ℝ) (S : Finset ι) (μ : ℝ) (hμ : 0<μ)
    (hA : DominatesOn A S μ) (x b xh y : ι → ℝ) (hx : Solves A S x b)
    (Λ εS η δ X : ℝ) (hεS : 0≤εS) (hX : 0≤X)
    (hLd : ∀ i∈S, Lh i i=1)
    (hΛ : ∀ i∈S, ∑ k∈S, |Lh i k|≤Λ)
    (hΔ : ∀ i∈S, ∑ j∈S, |∑ k∈S, Lh i k*Uh k j-A i j|≤εS)
    (hxX : ∀ j∈S, |x j|≤X)
    (hf : ∀ k∈S, |y k+∑ j∈S.erase k, Lh k j*y j-b k|≤η)
    (hb : ∀ k∈S, |∑ j∈S, Uh k j*xh j-y k|≤δ)
    (hsmall : εS/μ≤1/2) (j : ι) (hj : j∈S) :
    |xh j-x j|≤2*((Λ*δ+η)/μ+εS/μ*X) := by
  obtain ⟨m, hm, hmax⟩ := exists_max_image S (fun j => |xh j-x j|) ⟨j, hj⟩
  set E := |xh m-x m|
  have hE0 : 0≤E := abs_nonneg _
  have hxh : ∀ i∈S, |xh i|≤X+E := fun i hi => by
    have := abs_add_le (xh i-x i) (x i)
    rw [sub_add_cancel] at this
    linarith [hmax i hi, hxX i hi]
  set res : ι → ℝ := fun i => ∑ j∈S, A i j*xh j-b i
  have hres : ∀ i∈S, |res i|≤Λ*δ+η+εS*(X+E) := by
    intro i hi
    set Δ : Matrix ι ι ℝ := fun i j => ∑ k∈S, Lh i k*Uh k j-A i j
    have hexp : res i=∑ k∈S, Lh i k*(∑ j∈S, Uh k j*xh j-y k)+
        (y i+∑ k∈S.erase i, Lh i k*y k-b i)-∑ j∈S, Δ i j*xh j := by
      have hsplit := sum_erase_add S (fun k => Lh i k*y k) hi
      simp only [hLd i hi, one_mul] at hsplit
      simp only [res, Δ, sub_mul, sum_sub_distrib, sum_mul, mul_sub, mul_sum]
      rw [sum_comm (s := S) (t := S) (f := fun j k => Lh i k*Uh k j*xh j)]
      simp_rw [mul_assoc]
      linarith
    rw [hexp]
    have h1 := row_bound Lh S (fun k => ∑ j∈S, Uh k j*xh j-y k) i Λ δ (hΛ i hi)
      (le_trans (abs_nonneg _) (hb i hi)) hb
    have h3 := row_bound Δ S xh i εS (X+E) (hΔ i hi) (by linarith) hxh
    calc |∑ k∈S, Lh i k*(∑ j∈S, Uh k j*xh j-y k)+(y i+∑ k∈S.erase i, Lh i k*y k-b i)-
          ∑ j∈S, Δ i j*xh j|
        ≤|∑ k∈S, Lh i k*(∑ j∈S, Uh k j*xh j-y k)|+|y i+∑ k∈S.erase i, Lh i k*y k-b i|+
          |∑ j∈S, Δ i j*xh j| :=
          (abs_sub _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _≤Λ*δ+η+εS*(X+E) := add_le_add (add_le_add h1 (hf i hi)) h3
  have hsol : Solves A S (xh-x) res := by
    intro i hi
    simp only [res, Pi.sub_apply, mul_sub, sum_sub_distrib, hx i hi]
  have hEb := solves_bound A S μ hμ hA _ res hsol _ hres m hm
  have hE : E≤(Λ*δ+η)/μ+εS/μ*(X+E) := by
    refine hEb.trans (le_of_eq ?_)
    field_simp
  have hc0 : 0≤εS/μ := div_nonneg hεS hμ.le
  have hE' : E≤2*((Λ*δ+η)/μ+εS/μ*X) := by nlinarith
  exact (hmax j hj).trans hE'

/-- Backward-error form where the back residual may grow with the size of the
computed solution: `|Σ U x̂ - y| ≤ δ + κ B` whenever `|x̂| ≤ B`. Under
`(εS+Λκ)/μ ≤ 1/2` the error is `2((Λδ+η)/μ + ((εS+Λκ)/μ) X)`. -/
theorem backward_lu_k (A Lh Uh : Matrix ι ι ℝ) (S : Finset ι) (μ : ℝ) (hμ : 0<μ)
    (hA : DominatesOn A S μ) (x b xh y : ι → ℝ) (hx : Solves A S x b)
    (Λ εS η δ κ X : ℝ) (hΛ0 : 0≤Λ) (hεS : 0≤εS) (hκ : 0≤κ) (hX : 0≤X)
    (hLd : ∀ i∈S, Lh i i=1)
    (hΛ : ∀ i∈S, ∑ k∈S, |Lh i k|≤Λ)
    (hΔ : ∀ i∈S, ∑ j∈S, |∑ k∈S, Lh i k*Uh k j-A i j|≤εS)
    (hxX : ∀ j∈S, |x j|≤X)
    (hf : ∀ k∈S, |y k+∑ j∈S.erase k, Lh k j*y j-b k|≤η)
    (hb : ∀ B, (∀ j∈S, |xh j|≤B) → ∀ k∈S, |∑ j∈S, Uh k j*xh j-y k|≤δ+κ*B)
    (hsmall : (εS+Λ*κ)/μ≤1/2) (j : ι) (hj : j∈S) :
    |xh j-x j|≤2*((Λ*δ+η)/μ+(εS+Λ*κ)/μ*X) := by
  obtain ⟨m, hm, hmax⟩ := exists_max_image S (fun j => |xh j-x j|) ⟨j, hj⟩
  set E := |xh m-x m|
  have hE0 : 0≤E := abs_nonneg _
  have hxh : ∀ i∈S, |xh i|≤X+E := fun i hi => by
    have := abs_add_le (xh i-x i) (x i)
    rw [sub_add_cancel] at this
    linarith [hmax i hi, hxX i hi]
  have hbE := hb (X+E) hxh
  have hδ0 : 0≤δ+κ*(X+E) := le_trans (abs_nonneg _) (hbE m hm)
  set res : ι → ℝ := fun i => ∑ j∈S, A i j*xh j-b i
  have hres : ∀ i∈S, |res i|≤Λ*(δ+κ*(X+E))+η+εS*(X+E) := by
    intro i hi
    set Δ : Matrix ι ι ℝ := fun i j => ∑ k∈S, Lh i k*Uh k j-A i j
    have hexp : res i=∑ k∈S, Lh i k*(∑ j∈S, Uh k j*xh j-y k)+
        (y i+∑ k∈S.erase i, Lh i k*y k-b i)-∑ j∈S, Δ i j*xh j := by
      have hsplit := sum_erase_add S (fun k => Lh i k*y k) hi
      simp only [hLd i hi, one_mul] at hsplit
      simp only [res, Δ, sub_mul, sum_sub_distrib, sum_mul, mul_sub, mul_sum]
      rw [sum_comm (s := S) (t := S) (f := fun j k => Lh i k*Uh k j*xh j)]
      simp_rw [mul_assoc]
      linarith
    rw [hexp]
    have h1 := row_bound Lh S (fun k => ∑ j∈S, Uh k j*xh j-y k) i Λ (δ+κ*(X+E)) (hΛ i hi)
      hδ0 hbE
    have h3 := row_bound Δ S xh i εS (X+E) (hΔ i hi) (by linarith) hxh
    calc |∑ k∈S, Lh i k*(∑ j∈S, Uh k j*xh j-y k)+(y i+∑ k∈S.erase i, Lh i k*y k-b i)-
          ∑ j∈S, Δ i j*xh j|
        ≤|∑ k∈S, Lh i k*(∑ j∈S, Uh k j*xh j-y k)|+|y i+∑ k∈S.erase i, Lh i k*y k-b i|+
          |∑ j∈S, Δ i j*xh j| :=
          (abs_sub _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _≤Λ*(δ+κ*(X+E))+η+εS*(X+E) := add_le_add (add_le_add h1 (hf i hi)) h3
  have hsol : Solves A S (xh-x) res := by
    intro i hi
    simp only [res, Pi.sub_apply, mul_sub, sum_sub_distrib, hx i hi]
  have hEb := solves_bound A S μ hμ hA _ res hsol _ hres m hm
  have hE : E≤(Λ*δ+η)/μ+(εS+Λ*κ)/μ*(X+E) := by
    refine hEb.trans (le_of_eq ?_)
    field_simp
    ring
  have hc0 : 0≤(εS+Λ*κ)/μ := div_nonneg (by positivity) hμ.le
  have hE' : E≤2*((Λ*δ+η)/μ+(εS+Λ*κ)/μ*X) := by nlinarith
  exact (hmax j hj).trans hE'

end IntegerMultBounds.NLogN.SchurDominance
