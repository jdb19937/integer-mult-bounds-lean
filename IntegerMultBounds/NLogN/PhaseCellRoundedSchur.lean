module

public import IntegerMultBounds.NLogN.PhaseCellBoundaryOrder
public import IntegerMultBounds.NLogN.SchurPerturbSolve
import IntegerMultBounds.NLogN.PhaseCellBoundaryLU
import IntegerMultBounds.NLogN.PhaseCellRoundedSolve
import IntegerMultBounds.NLogN.PhaseCellBoundary
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log
public import IntegerMultBounds.BinaryWords

/-! # The rounded boundary solve of the phase-cell inverse

After the interior `I` is eliminated, the boundary unknowns `B = univ \ I` satisfy the reduced
system `S`, with entries `S_ij = A_ij - A_iI R(A_Ij)` for the exact interior solver `R`
(`run_entry`), margin `1/(8p)` and row mass at most two.

* **The computed boundary matrix.** Entries of a band `Rel` that contains the support of `S`
  are formed from computed interior responses `Y j`, within `eR` of `R(A_Ij)` wherever a
  boundary row reads them, with one rounding `η`; entries outside the band are zero. Each row is
  within `|B| (η + eR)` of `S` (`rounded_schur_rows`).
* **The solve.** The machine-faithful solve `bandSolveG` of the computed matrix in any
  elimination order of `B` is within `2^16 p³ N (N η + eR + θ) (1 + ρ)` of the exact boundary
  solution, for right-hand sides at most `ρ`, any `N ≥ |B|`, and
  `2^13 p² N (N η + eR + θ) ≤ 1` (`rounded_schur_solve`). This is the boundary stage `e₃` of
  `rounded_four_step`; it needs no forward bounds on the factors. The bands and orders used are
  the folded ones of `PhaseCellBoundaryFold`. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open scoped BigOperators
open Finset SchurDominance
variable (s t : ℕ) [NeZero s]

omit [NeZero s] in
theorem bOrder_val_sorted (B : Finset (ZMod s)) :
    (bOrder s B).Pairwise fun a b => a.val<b.val :=
  (physOrder_sorted s).filter _

theorem bOrder_length (B : Finset (ZMod s)) : (bOrder s B).length=B.card := by
  have hnd : (bOrder s B).Nodup :=
    (bOrder_val_sorted s B).imp fun h => ne_of_apply_ne ZMod.val (ne_of_lt h)
  rw [←List.toFinset_card_of_nodup hnd, bOrder_toFinset]

variable [NeZero t]

/-- The reduced boundary matrix keeps margin `1/(8p)` and row mass at most two. -/
theorem schur_stageInv (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p)
    (I : Finset (ZMod s)) (ks : List (ZMod s)) (hks : ks.toFinset=I) :
    StageInv (run (realMatrix s t p u) univ ks).1 (univ\I) (1/(8*(p : ℝ))) 2 := by
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  have hμ : (0 : ℝ)<1/(8*(p : ℝ)) := by positivity
  have hU : I∪(univ\I)=univ := union_sdiff_of_subset (subset_univ I)
  have hIB : Disjoint I (univ\I) := disjoint_sdiff
  have hA0 := matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget
  have hA := hA0
  rw [←hU] at hA
  have hSm : (run (realMatrix s t p u) univ ks).1=
      (run (realMatrix s t p u) (I∪(univ\I)) ks).1 := by rw [hU]
  refine ⟨by rw [hSm]; exact schur_dominates _ I _ hIB _ hμ hA _ hks, fun i _ => ?_⟩
  have h := run_mass (realMatrix s t p u) univ _ hμ hA0 ks i
  rw [run_set, hks] at h
  exact h.trans (row_mass s t hst hα p u hp hwidth hαu hθ hgap hbudget i)

/-- Every row of the computed boundary matrix is within `|B| (η + eR)` of the reduced
boundary matrix. -/
theorem rounded_schur_rows (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p)
    (I : Finset (ZMod s)) (R : (ZMod s → ℝ) → ZMod s → ℝ)
    (hR : ∀ c, Solves (realMatrix s t p u) I (R c) c)
    (ks : List (ZMod s)) (hks : ks.toFinset=I)
    (η eR : ℝ) (hη : 0≤η) (heR : 0≤eR) (Rel : ZMod s → ZMod s → Prop)
    (hRel : ∀ i∈univ\I, ∀ j∈univ\I, (run (realMatrix s t p u) univ ks).1 i j≠0 → Rel i j)
    (Y : ZMod s → ZMod s → ℝ) (Sh : Matrix (ZMod s) (ZMod s) ℝ)
    (hY : ∀ i∈univ\I, ∀ j∈univ\I, ∀ k∈I, realMatrix s t p u i k≠0 →
      |Y j k-R (fun l => realMatrix s t p u l j) k|≤eR)
    (hSh : ∀ i∈univ\I, ∀ j∈univ\I, Rel i j →
      |Sh i j-(realMatrix s t p u i j-∑ k∈I, realMatrix s t p u i k*Y j k)|≤η)
    (hSh0 : ∀ i∈univ\I, ∀ j∈univ\I, ¬Rel i j → Sh i j=0)
    (i : ZMod s) (hi : i∈univ\I) :
    ∑ j∈univ\I, |Sh i j-(run (realMatrix s t p u) univ ks).1 i j|≤(univ\I).card*(η+eR) := by
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  have hμ : (0 : ℝ)<1/(8*(p : ℝ)) := by positivity
  have hU : I∪(univ\I)=univ := union_sdiff_of_subset (subset_univ I)
  have hIB : Disjoint I (univ\I) := disjoint_sdiff
  have hA := matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget
  rw [←hU] at hA
  have hmassI : ∑ k∈I, |realMatrix s t p u i k|≤1 :=
    (sum_le_sum_of_subset_of_nonneg (fun k hk => mem_erase.mpr
      ⟨fun h => (mem_sdiff.mp hi).2 (by rw [←h]; exact hk), mem_univ k⟩) fun _ _ _ => abs_nonneg _).trans
      (offDiag_mass s t hst hα p u hp hwidth hαu hθ hgap hbudget i)
  have hentry : ∀ j∈univ\I, |Sh i j-(run (realMatrix s t p u) univ ks).1 i j|≤η+eR := by
    intro j hj
    by_cases hrel : Rel i j
    · have he := run_entry _ I _ hIB _ hμ hA R hR ks hks i j hi hj
      rw [hU] at he
      rw [he]
      have hdiff : |∑ k∈I, realMatrix s t p u i k*R (fun l => realMatrix s t p u l j) k-
          ∑ k∈I, realMatrix s t p u i k*Y j k|≤eR := by
        rw [←sum_sub_distrib]
        refine (abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ k∈I, |realMatrix s t p u i k*R (fun l => realMatrix s t p u l j) k-
              realMatrix s t p u i k*Y j k|
            ≤∑ k∈I, |realMatrix s t p u i k| * eR := sum_le_sum fun k hk => by
              rw [←mul_sub, abs_mul]
              by_cases h0 : realMatrix s t p u i k=0
              · simp [h0]
              · rw [abs_sub_comm]
                exact mul_le_mul_of_nonneg_left (hY i hi j hj k hk h0) (abs_nonneg _)
          _=(∑ k∈I, |realMatrix s t p u i k|) * eR := (sum_mul _ _ _).symm
          _≤1*eR := mul_le_mul_of_nonneg_right hmassI heR
          _=eR := one_mul _
      have h := abs_add_le (Sh i j-(realMatrix s t p u i j-∑ k∈I, realMatrix s t p u i k*Y j k))
        (∑ k∈I, realMatrix s t p u i k*R (fun l => realMatrix s t p u l j) k-
          ∑ k∈I, realMatrix s t p u i k*Y j k)
      have e : Sh i j-(realMatrix s t p u i j-∑ k∈I, realMatrix s t p u i k*Y j k)+
          (∑ k∈I, realMatrix s t p u i k*R (fun l => realMatrix s t p u l j) k-
            ∑ k∈I, realMatrix s t p u i k*Y j k)=
          Sh i j-(realMatrix s t p u i j-
            ∑ k∈I, realMatrix s t p u i k*R (fun l => realMatrix s t p u l j) k) := by ring
      rw [e] at h
      linarith [hSh i hi j hj hrel]
    · have h0 : (run (realMatrix s t p u) univ ks).1 i j=0 := by
        by_contra h
        exact hrel (hRel i hi j hj h)
      rw [hSh0 i hi j hj hrel, h0, sub_zero, abs_zero]
      linarith
  calc ∑ j∈univ\I, |Sh i j-(run (realMatrix s t p u) univ ks).1 i j|
      ≤∑ _j∈univ\I, (η+eR) := sum_le_sum hentry
    _=(univ\I).card*(η+eR) := by rw [sum_const, nsmul_eq_mul]

omit [NeZero s] [NeZero t] in
/-- The size bookkeeping of the boundary solve at margin `μ = 1/(8p)`, mass `2` and pivot
bound `3`, with `n` boundary vertices, an elimination list of length `L ≤ n`, entry error
`η + eR` and reciprocal error `θ`. -/
private theorem boundary_arith (p n L η θ eR ρ : ℝ) (hp : 2≤p) (hn : 1≤n) (hLn : L≤n)
    (hη : 0≤η) (hθ : 0≤θ) (heR : 0≤eR) (hρ : 0≤ρ)
    (hsmall : 2^13*p^2*(n*(n*η+eR+θ))≤1) :
    2+n*(η+eR)+L*(η*(n+3))≤3 ∧
      1/(8*p)/2+n*(η+eR)+2*L*(η*(n+3))≤1/(8*p) ∧ θ≤1/2 ∧
      (n*(L*(η*(1+3)))+n*(η+eR)+(1+L*(2*3/(1/(8*p))+η))*(2*θ*3))/(1/(8*p))≤1/2 ∧
      2*(((1+L*(2*3/(1/(8*p))+η))*((n+3+2*θ*3)*η)+n*η)/(1/(8*p))+
        (n*(L*(η*(1+3)))+n*(η+eR)+(1+L*(2*3/(1/(8*p))+η))*(2*θ*3))/(1/(8*p))*(8*p*ρ))≤
        2^16*p^3*(n*(n*η+eR+θ))*(1+ρ) := by
  have hp0 : 0<p := by linarith
  have hn0 : 0≤n := by linarith
  have hdiv (q : ℝ) : q/(1/(8*p))=q*(8*p) := by field_simp
  simp only [hdiv]
  obtain ⟨E, hE⟩ : ∃ E, E=n*(n*η+eR+θ) := ⟨_, rfl⟩
  rw [←hE] at hsmall ⊢
  have hEsum : n*n*η+n*eR+n*θ=E := by rw [hE]; ring
  have hnn : 0≤n*eR := mul_nonneg hn0 heR
  have hnθ : 0≤n*θ := mul_nonneg hn0 hθ
  have hnnη : 0≤n*n*η := mul_nonneg (mul_nonneg hn0 hn0) hη
  have hE0 : 0≤E := by linarith
  have he1 : n*n*η≤E := by linarith
  have he3 : n*θ≤E := by linarith
  have hp2 : 4≤p^2 := by
    have := mul_le_mul hp hp (by norm_num) hp0.le
    linarith
  have hp2E : 0≤p^2*E := mul_nonneg (sq_nonneg p) hE0
  have hE1 : 32768*E≤1 := by
    have := mul_le_mul_of_nonneg_right hp2 hE0
    linarith
  have hnη : n*η≤n*n*η := by
    have := mul_nonneg (mul_nonneg hn0 hη) (by linarith : 0≤n-1)
    linarith
  have hη1 : η≤1 := by
    have := mul_nonneg hη (by linarith : 0≤n-1)
    linarith
  have hθn : θ≤n*θ := by
    have := mul_nonneg hθ (by linarith : 0≤n-1)
    linarith
  have hLη : L*(η*(n+3))≤4*(n*n*η) := by
    have := mul_le_mul_of_nonneg_right hLn (by positivity : 0≤η*(n+3))
    linarith
  have hpE : E≤p*E := by
    have := mul_nonneg hE0 (by linarith : 0≤p-1)
    linarith
  have hpE2 : 2*E≤p*E := by
    have := mul_nonneg hE0 (by linarith : 0≤p-2)
    linarith
  have hΛ : 1+L*(2*3*(8*p)+η)≤50*p*n := by
    have h1 : L*(2*3*(8*p)+η)≤n*(48*p+1) := mul_le_mul hLn (by linarith) (by positivity) hn0
    have h2 := mul_le_mul_of_nonneg_right hp hn0
    linarith
  have hT2 : n*(L*(η*(1+3)))+n*(η+eR)+(1+L*(2*3*(8*p)+η))*(2*θ*3)≤303*p*E := by
    have h1 : n*(L*(η*(1+3)))≤n*(n*(η*(1+3))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLn (by positivity)) hn0
    have h2 : (1+L*(2*3*(8*p)+η))*(2*θ*3)≤50*p*n*(2*θ*3) :=
      mul_le_mul_of_nonneg_right hΛ (by positivity)
    have h3 : p*(n*θ)≤p*E := mul_le_mul_of_nonneg_left he3 hp0.le
    linarith
  have hT1 : (1+L*(2*3*(8*p)+η))*((n+3+2*θ*3)*η)+n*η≤351*p*E := by
    have h7 : (n+3+2*θ*3)*η≤7*n*η := by
      have := mul_nonneg (by linarith : 0≤6*n-3-6*θ) hη
      linarith
    have h1 : (1+L*(2*3*(8*p)+η))*((n+3+2*θ*3)*η)≤50*p*n*(7*n*η) :=
      mul_le_mul hΛ h7 (by positivity) (by positivity)
    have h2 : p*(n*n*η)≤p*E := mul_le_mul_of_nonneg_left he1 hp0.le
    linarith
  refine ⟨by linarith, ?_, by linarith, ?_, ?_⟩
  · have h10 : 10*E≤1/(8*p)/2 := by
      rw [div_div, le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_right hp (mul_nonneg hp0.le hE0)
      have hpE0 := mul_nonneg hp0.le hE0
      linarith
    linarith
  · have := mul_le_mul_of_nonneg_right hT2 (by positivity : 0≤8*p)
    linarith
  · have h1 := mul_le_mul_of_nonneg_right hT1 (by positivity : 0≤8*p)
    have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hT2 (by positivity : 0≤8*p))
      (by positivity : 0≤8*p*ρ)
    have h3 : p^2*E≤p^3*E := by
      have := mul_nonneg hp2E (by linarith : 0≤p-1)
      linarith
    have h4 := mul_nonneg (mul_nonneg (pow_nonneg hp0.le 3) hE0) hρ
    linarith

/-- **The rounded boundary solve.** The machine-faithful solve of the computed boundary
matrix in any elimination order `kb` of the boundary is within `2^16 p³ N (N η + eR + θ) (1 + ρ)`
of the exact boundary solution `Z` for any right-hand side `r` at most `ρ`. -/
theorem rounded_schur_solve (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p)
    (I : Finset (ZMod s)) (R : (ZMod s → ℝ) → ZMod s → ℝ)
    (hR : ∀ c, Solves (realMatrix s t p u) I (R c) c)
    (rd : ℝ → ℝ) (mul : ℝ → ℝ → ℝ) (rec : ℝ → ℝ) (η θ eR : ℝ)
    (hrd : ∀ x, |rd x-x|≤η) (hrd0 : rd 0=0) (hmul : ∀ a b, |mul a b-a/b|≤η)
    (hmul0 : ∀ b, mul 0 b=0) (hrec : ∀ c, 1/(8*(p : ℝ))/2≤c → c≤3 → |c*rec c-1|≤θ)
    (heR : 0≤eR) (N : ℕ) (hcardN : (univ\I).card≤N)
    (hsmall : 2^13*(p : ℝ)^2*(N*(N*η+eR+θ))≤1)
    (Rel : ZMod s → ZMod s → Prop)
    (hRel : ∀ ks : List (ZMod s), ks.toFinset=I →
      ∀ i∈univ\I, ∀ j∈univ\I, (run (realMatrix s t p u) univ ks).1 i j≠0 → Rel i j)
    (kb : List (ZMod s)) (pos : ZMod s → ℕ) (hpos : Function.Injective pos)
    (hkb : kb.toFinset=univ\I) (hsort : kb.Pairwise fun a b => pos a<pos b)
    (Y : ZMod s → ZMod s → ℝ) (Sh : Matrix (ZMod s) (ZMod s) ℝ)
    (hY : ∀ i∈univ\I, ∀ j∈univ\I, ∀ k∈I, realMatrix s t p u i k≠0 →
      |Y j k-R (fun l => realMatrix s t p u l j) k|≤eR)
    (hSh : ∀ i∈univ\I, ∀ j∈univ\I, Rel i j →
      |Sh i j-(realMatrix s t p u i j-∑ k∈I, realMatrix s t p u i k*Y j k)|≤η)
    (hSh0 : ∀ i∈univ\I, ∀ j∈univ\I, ¬Rel i j → Sh i j=0)
    (r Z : ZMod s → ℝ) (hZ : ∀ i∈univ\I, schurOp (realMatrix s t p u) I (univ\I) R Z i=r i)
    (ρ : ℝ) (hr : ∀ i∈univ\I, |r i|≤ρ) (j : ZMod s) (hj : j∈univ\I) :
    |bandSolveG rd mul rec Sh (univ\I) kb r j-Z j|≤
      2^16*(p : ℝ)^3*(N*(N*η+eR+θ))*(1+ρ) := by
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  have hη : 0≤η := le_trans (abs_nonneg _) (hrd 0)
  have hμ : (0 : ℝ)<1/(8*(p : ℝ)) := by positivity
  have hU : I∪(univ\I)=univ := union_sdiff_of_subset (subset_univ I)
  have hIB : Disjoint I (univ\I) := disjoint_sdiff
  have hA0 := matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget
  have hA := hA0
  rw [←hU] at hA
  have hks : I.toList.toFinset=I := toList_toFinset I
  have hSm : (run (realMatrix s t p u) univ I.toList).1=
      (run (realMatrix s t p u) (I∪(univ\I)) I.toList).1 := by rw [hU]
  have hSdom : DominatesOn (run (realMatrix s t p u) univ I.toList).1 (univ\I)
      (1/(8*(p : ℝ))) := by
    rw [hSm]; exact schur_dominates _ I _ hIB _ hμ hA _ hks
  have hsol : Solves (run (realMatrix s t p u) univ I.toList).1 (univ\I) Z r := by
    intro i hi
    rw [←hZ i hi, schurOp_eq_run _ I _ hIB _ hμ hA R hR _ hks Z i hi, hSm]
  have hmass : ∀ i∈univ\I, ∑ k∈univ\I, |(run (realMatrix s t p u) univ I.toList).1 i k|≤2 := by
    intro i _
    have h := run_mass (realMatrix s t p u) univ _ hμ hA0 I.toList i
    rw [run_set, hks] at h
    exact h.trans (row_mass s t hst hα p u hp hwidth hαu hθ hgap hbudget i)
  have hX : ∀ i∈univ\I, |Z i|≤8*p*ρ := by
    intro i hi
    have h := solves_bound _ _ _ hμ hSdom Z r hsol ρ hr i hi
    rwa [div_div_eq_mul_div, div_one, mul_comm] at h
  have hρ : 0≤ρ := le_trans (abs_nonneg _) (hr j hj)
  have hθ0 : 0≤θ := le_trans (abs_nonneg _) (hrec 1
    (by rw [div_div, div_le_one (by positivity)]; linarith) (by norm_num))
  have hn1 : (1 : ℝ)≤N := by
    have : 0<(univ\I).card := card_pos.mpr ⟨j, hj⟩
    exact_mod_cast this.trans_le hcardN
  have hLn : (kb.length : ℝ)≤N := by
    have hnd : kb.Nodup := hsort.imp fun h e => by rw [e] at h; exact lt_irrefl _ h
    rw [←List.toFinset_card_of_nodup hnd, hkb]; exact_mod_cast hcardN
  have hrows : ∀ i∈univ\I, ∑ j∈univ\I, |Sh i j-(run (realMatrix s t p u) univ I.toList).1 i j|≤
      N*(η+eR) := fun i hi =>
    (rounded_schur_rows s t hst hα p u hp hwidth hαu hθ hgap hbudget I R hR _ hks η eR hη heR
      Rel (hRel _ hks) Y Sh hY hSh hSh0 i hi).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hcardN) (by positivity))
  obtain ⟨hm, hmu, hθh, hsm, hfin⟩ := boundary_arith (p : ℝ) (N : ℝ) _ η θ eR ρ hpR hn1 hLn hη hθ0
    heR hρ hsmall
  exact (bandSolveG_perturbed_error rd mul rec η θ hrd hrd0 hmul hmul0 pos hpos _ Sh (univ\I) _ 2
    3 N _ hμ (by norm_num) (by norm_num) ⟨hSdom, hmass⟩ (by positivity) hrows
    (by exact_mod_cast hcardN) kb hkb hsort hm hmu hrec hθh Z r hsol (8*p*ρ)
    (by positivity) hX hsm j hj).trans hfin

end IntegerMultBounds.NLogN.PhaseCellMatrix
