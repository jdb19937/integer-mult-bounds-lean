module

import IntegerMultBounds.NLogN.SchurBlockError
public import IntegerMultBounds.NLogN.SchurSolve

/-! LU factors of successive Schur elimination and the residual bound for
rounded triangular solves. Eliminating in list order gives `A = L U` on the
active set, with unit-diagonal multipliers whose absolute row sums are at most
`1 + mass/μ`, and pivot rows that keep the margin `μ`. Any computed forward
and back substitutions with residuals `εf` and `εb` against the exact factors
solve the system within `(Λ εb + εf)/μ`. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.SchurDominance

open scoped BigOperators
open Finset
variable {ι : Type*} [DecidableEq ι]

/-- A pivot consumes `μ|A i k|/A k k` of every other row's mass. -/
theorem eliminate_mass_sharp (A : Matrix ι ι ℝ) (S : Finset ι) (μ : ℝ) (k i : ι) (hkS : k∈S)
    (hdiag : 0<A k k) (hrow : μ+∑ j∈S.erase k, |A k j|≤A k k) :
    (∑ j∈S.erase k, |eliminate A k i j|)+μ*(|A i k|/A k k)≤∑ j∈S, |A i j| := by
  set c := |A i k|/A k k
  have hc : 0≤c := div_nonneg (abs_nonneg _) hdiag.le
  have hc_eq : c*A k k=|A i k| := div_mul_cancel₀ _ hdiag.ne'
  have hsplit := sum_erase_add S (fun j => |A i j|) hkS
  have hfill : (∑ j∈S.erase k, |eliminate A k i j|)≤
      (∑ j∈S.erase k, |A i j|)+c*∑ j∈S.erase k, |A k j| := by
    rw [mul_sum, ←sum_add_distrib]
    refine sum_le_sum fun j _ => ?_
    calc |eliminate A k i j|≤|A i j|+|A i k/A k k*A k j| := abs_sub _ _
      _=|A i j|+c*|A k j| := by simp [abs_mul, abs_div, abs_of_pos hdiag, c]
  have hck := mul_le_mul_of_nonneg_left hrow hc
  nlinarith

/-- One elimination step as a matrix. -/
noncomputable def elimM (A : Matrix ι ι ℝ) (k : ι) : Matrix ι ι ℝ := fun i j => eliminate A k i j

/-- Unit lower factor: multipliers of each pivot, recorded in list order. -/
noncomputable def luL (A : Matrix ι ι ℝ) (S : Finset ι) : List ι → Matrix ι ι ℝ
  | [] => fun i j => if i∈S ∧ i=j then 1 else 0
  | k::ks => fun i j => if k∈S then
      (if j=k then (if i=k then 1 else if i∈S then A i k/A k k else 0)
      else luL (elimM A k) (S.erase k) ks i j)
    else luL A S ks i j

/-- Upper factor: each pivot row at its elimination stage. -/
noncomputable def luU (A : Matrix ι ι ℝ) (S : Finset ι) : List ι → Matrix ι ι ℝ
  | [] => fun i j => if i∈S ∧ j∈S then A i j else 0
  | k::ks => fun i j => if k∈S then
      (if i=k then (if j∈S then A k j else 0)
      else luU (elimM A k) (S.erase k) ks i j)
    else luU A S ks i j

theorem luL_supp (A : Matrix ι ι ℝ) (S : Finset ι) (ks : List ι) (i j : ι) (hi : i∉S) :
    luL A S ks i j=0 := by
  induction ks generalizing A S with
  | nil => simp [luL, hi]
  | cons k ks ih =>
    by_cases hk : k∈S
    · simp only [luL, hk, ite_true]
      split
      · rename_i hjk
        have hik : i≠k := fun h => hi (h ▸ hk)
        simp [hik]
      · exact ih _ _ (fun h => hi (mem_of_mem_erase h))
    · simp only [luL, hk, ite_false]
      exact ih _ _ hi

theorem luU_supp_row (A : Matrix ι ι ℝ) (S : Finset ι) (ks : List ι) (i j : ι) (hi : i∉S) :
    luU A S ks i j=0 := by
  induction ks generalizing A S with
  | nil => simp [luU, hi]
  | cons k ks ih =>
    by_cases hk : k∈S
    · simp only [luU, hk, ite_true]
      have hik : i≠k := fun h => hi (h ▸ hk)
      simp only [hik, ite_false]
      exact ih _ _ (fun h => hi (mem_of_mem_erase h))
    · simp only [luU, hk, ite_false]
      exact ih _ _ hi

theorem luU_supp_col (A : Matrix ι ι ℝ) (S : Finset ι) (ks : List ι) (i j : ι) (hj : j∉S) :
    luU A S ks i j=0 := by
  induction ks generalizing A S with
  | nil => simp [luU, hj]
  | cons k ks ih =>
    by_cases hk : k∈S
    · simp only [luU, hk, ite_true]
      split
      · simp
      · exact ih _ _ (fun h => hj (mem_of_mem_erase h))
    · simp only [luU, hk, ite_false]
      exact ih _ _ hj

/-- Elimination in list order factors the active block. -/
theorem lu_eq (A : Matrix ι ι ℝ) (S : Finset ι) (μ : ℝ) (hμ : 0<μ) (hA : DominatesOn A S μ)
    (ks : List ι) (i j : ι) (hi : i∈S) (hj : j∈S) :
    A i j=∑ k∈S, luL A S ks i k*luU A S ks k j := by
  induction ks generalizing A S with
  | nil =>
    simp only [luL, luU]
    rw [sum_eq_single i (fun k _ hk => by simp [Ne.symm hk]) (fun h => absurd hi h)]
    simp [hi, hj]
  | cons k ks ih =>
    by_cases hk : k∈S
    · have hdiag := pivot_pos A S μ hμ hA k hk
      have hnext : DominatesOn (elimM A k) (S.erase k) μ := eliminate_preserves A S μ hμ hA k hk
      simp only [luL, luU, hk, ite_true]
      rw [←sum_erase_add S _ hk]
      simp only [ite_true]
      have hrest : ∑ k'∈S.erase k, (if k'=k then (if i=k then (1 : ℝ) else if i∈S then
            A i k/A k k else 0) else luL (elimM A k) (S.erase k) ks i k')*
          (if k'=k then (if j∈S then A k j else 0) else
            luU (elimM A k) (S.erase k) ks k' j)=
          ∑ k'∈S.erase k, luL (elimM A k) (S.erase k) ks i k'*
            luU (elimM A k) (S.erase k) ks k' j :=
        sum_congr rfl fun k' hk' => by simp [ne_of_mem_erase hk']
      rw [hrest]
      by_cases hik : i=k
      · subst hik
        rw [sum_eq_zero fun k' _ => mul_eq_zero_of_left (luL_supp _ _ ks _ _ (notMem_erase i S)) _]
        simp [hj]
      · have hiS' : i∈S.erase k := mem_erase.mpr ⟨hik, hi⟩
        by_cases hjk : j=k
        · subst hjk
          rw [sum_eq_zero fun k' _ => mul_eq_zero_of_right _ (luU_supp_col _ _ ks _ _ (notMem_erase j S))]
          simp only [hik, ite_false, hi, ite_true, hk, zero_add]
          field_simp
        · rw [←ih _ _ hnext hiS' (mem_erase.mpr ⟨hjk, hj⟩)]
          simp only [hik, ite_false, hi, ite_true, hj, elimM, eliminate]
          ring
    · simp only [luL, luU, hk, ite_false]
      exact ih A S hA hi hj

/-- Multiplier rows are bounded by the consumed row mass. -/
theorem luL_mass (A : Matrix ι ι ℝ) (S : Finset ι) (μ : ℝ) (hμ : 0<μ) (hA : DominatesOn A S μ)
    (ks : List ι) (i : ι) (hi : i∈S) :
    ∑ k∈S, |luL A S ks i k|≤1+(∑ j∈S, |A i j|)/μ := by
  induction ks generalizing A S with
  | nil =>
    simp only [luL]
    rw [sum_eq_single i (fun k _ hk => by simp [Ne.symm hk]) (fun h => absurd hi h)]
    simp only [hi, and_self, ite_true, abs_one]
    have : 0≤(∑ j∈S, |A i j|)/μ := div_nonneg (sum_nonneg fun _ _ => abs_nonneg _) hμ.le
    linarith
  | cons k ks ih =>
    by_cases hk : k∈S
    · have hdiag := pivot_pos A S μ hμ hA k hk
      have hnext : DominatesOn (elimM A k) (S.erase k) μ := eliminate_preserves A S μ hμ hA k hk
      simp only [luL, hk, ite_true]
      rw [←sum_erase_add S _ hk]
      simp only [ite_true]
      have hrest : ∑ k'∈S.erase k, |if k'=k then (if i=k then (1 : ℝ) else if i∈S then
            A i k/A k k else 0) else luL (elimM A k) (S.erase k) ks i k'|=
          ∑ k'∈S.erase k, |luL (elimM A k) (S.erase k) ks i k'| :=
        sum_congr rfl fun k' hk' => by simp [ne_of_mem_erase hk']
      rw [hrest]
      have hmass0 : 0≤(∑ j∈S, |A i j|)/μ := div_nonneg (sum_nonneg fun _ _ => abs_nonneg _) hμ.le
      by_cases hik : i=k
      · subst hik
        rw [sum_eq_zero fun k' _ => abs_eq_zero.mpr (luL_supp _ _ ks _ _ (notMem_erase i S))]
        simp only [ite_true, abs_one, zero_add]
        linarith
      · have hiS' : i∈S.erase k := mem_erase.mpr ⟨hik, hi⟩
        have hih := ih _ _ hnext hiS'
        simp only [elimM] at hih
        have hrow : μ+∑ j∈S.erase k, |A k j|≤A k k := hA k hk
        have hsharp := eliminate_mass_sharp A S μ k i hk hdiag hrow
        simp only [hik, hi, ite_false, ite_true]
        rw [abs_div, abs_of_pos hdiag]
        have hdivmass : (∑ j∈S.erase k, |eliminate A k i j|)/μ+|A i k|/A k k≤
            (∑ j∈S, |A i j|)/μ := by
          rw [div_add' _ _ _ hμ.ne', div_le_div_iff_of_pos_right hμ]
          linarith
        linarith
    · simp only [luL, hk, ite_false]
      exact ih A S hA hi

/-- Pivot rows keep the margin and never exceed the original row mass. -/
theorem luU_row (A : Matrix ι ι ℝ) (S : Finset ι) (μ : ℝ) (hμ : 0<μ) (hA : DominatesOn A S μ)
    (ks : List ι) (i : ι) (hi : i∈S) :
    μ+∑ j∈S.erase i, |luU A S ks i j|≤luU A S ks i i ∧
      ∑ j∈S, |luU A S ks i j|≤∑ j∈S, |A i j| := by
  induction ks generalizing A S with
  | nil =>
    simp only [luU]
    refine ⟨?_, le_of_eq (sum_congr rfl fun j hj => by simp [hi, hj])⟩
    have hsum : ∑ j∈S.erase i, |(if i∈S ∧ j∈S then A i j else 0)|=∑ j∈S.erase i, |A i j| :=
      sum_congr rfl fun j hj => by simp [hi, mem_of_mem_erase hj]
    have hd : (if i∈S ∧ i∈S then A i i else 0)=A i i := by simp [hi]
    rw [hsum, hd]
    exact hA i hi
  | cons k ks ih =>
    by_cases hk : k∈S
    · have hdiag := pivot_pos A S μ hμ hA k hk
      have hnext : DominatesOn (elimM A k) (S.erase k) μ := eliminate_preserves A S μ hμ hA k hk
      simp only [luU, hk, ite_true]
      by_cases hik : i=k
      · subst hik
        simp only [ite_true]
        refine ⟨?_, le_of_eq (sum_congr rfl fun j hj => by simp [hj])⟩
        have hsum : ∑ j∈S.erase i, |(if j∈S then A i j else 0)|=∑ j∈S.erase i, |A i j| :=
          sum_congr rfl fun j hj => by simp [mem_of_mem_erase hj]
        have hd : (if i∈S then A i i else 0)=A i i := by simp [hi]
        rw [hsum, hd]
        exact hA i hi
      · have hiS' : i∈S.erase k := mem_erase.mpr ⟨hik, hi⟩
        obtain ⟨hd, hm⟩ := ih _ _ hnext hiS'
        simp only [hik, ite_false]
        have hzk : luU (elimM A k) (S.erase k) ks i k=0 := luU_supp_col _ _ ks _ _ (notMem_erase k S)
        have hsplit₁ := sum_erase_add (S.erase i) (fun j => |luU (elimM A k) (S.erase k) ks i j|)
          (mem_erase.mpr ⟨Ne.symm hik, hk⟩)
        have hsplit₂ := sum_erase_add S (fun j => |luU (elimM A k) (S.erase k) ks i j|) hk
        rw [hzk, abs_zero, add_zero, erase_right_comm] at hsplit₁
        rw [hzk, abs_zero, add_zero] at hsplit₂
        have hmass := eliminate_mass A S k i hk hdiag (by have := hA k hk; linarith)
        simp only [elimM] at hm hd hsplit₁ hsplit₂ ⊢
        constructor
        · linarith
        · linarith
    · simp only [luU, hk, ite_false]
      exact ih A S hA hi

/-- Residual bound: computed forward and back substitutions against exact
factors solve the dominant system within `(Λ εb + εf)/μ`. -/
theorem lu_residual (A L U : Matrix ι ι ℝ) (S : Finset ι)
    (hLU : ∀ i∈S, ∀ j∈S, A i j=∑ k∈S, L i k*U k j) (μ : ℝ) (hμ : 0<μ)
    (hA : DominatesOn A S μ) (x b : ι → ℝ) (hx : Solves A S x b)
    (Λ : ℝ) (hΛ : ∀ i∈S, ∑ k∈S, |L i k|≤Λ) (xh y : ι → ℝ) (εf εb : ℝ) (hεb : 0≤εb)
    (hf : ∀ i∈S, |∑ k∈S, L i k*y k-b i|≤εf)
    (hb : ∀ k∈S, |∑ j∈S, U k j*xh j-y k|≤εb) (j : ι) (hj : j∈S) :
    |xh j-x j|≤(Λ*εb+εf)/μ := by
  set res : ι → ℝ := fun i => ∑ j∈S, A i j*xh j-b i
  have hres : ∀ i∈S, |res i|≤Λ*εb+εf := by
    intro i hi
    have hexp : res i=∑ k∈S, L i k*(∑ j∈S, U k j*xh j-y k)+(∑ k∈S, L i k*y k-b i) := by
      simp only [res]
      rw [sum_congr rfl fun j hj => by rw [hLU i hi j hj]]
      simp only [sum_mul, mul_sub, mul_sum, sum_sub_distrib]
      rw [sum_comm]
      simp_rw [mul_assoc]
      ring
    rw [hexp]
    have h1 := row_bound L S (fun k => ∑ j∈S, U k j*xh j-y k) i Λ εb (hΛ i hi) hεb hb
    exact (abs_add_le _ _).trans (add_le_add h1 (hf i hi))
  have hsol : Solves A S (xh-x) res := by
    intro i hi
    simp only [res, Pi.sub_apply, mul_sub, sum_sub_distrib, hx i hi]
  exact solves_bound A S μ hμ hA _ res hsol _ hres j hj

end IntegerMultBounds.NLogN.SchurDominance
