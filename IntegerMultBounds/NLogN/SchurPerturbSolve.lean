module

import IntegerMultBounds.NLogN.SchurFill
public import IntegerMultBounds.NLogN.SchurSubst
import IntegerMultBounds.NLogN.SchurLURounded
public import IntegerMultBounds.NLogN.SchurIdentify
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Rounded solves of a computed approximation of a dominant system. A computed
matrix within row mass `ε` of a dominant matrix keeps the stage invariant with
margin `μ - ε` and mass `m + ε`, so the machine-faithful solve `bandSolveG` of
the computed matrix approximates the exact solution of the original system with
`ε` added to the backward error of the rounded factors. Dominant systems are
solvable for every right-hand side, and the reduced boundary matrix has the
Schur complement entries `A_ij - A_iI R(A_Ij)`. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.SchurDominance

open scoped BigOperators
open Finset
variable {ι : Type*} [DecidableEq ι]

/-- A dominant system has a solution for every right-hand side. -/
theorem solves_exists [Fintype ι] (A : Matrix ι ι ℝ) (S : Finset ι) (μ : ℝ) (hμ : 0<μ)
    (hA : DominatesOn A S μ) (b : ι → ℝ) : ∃ x, Solves A S x b := by
  set M : Matrix ι ι ℝ := fun i j => if i∈S then (if j∈S then A i j else 0) else
    (if i=j then 1 else 0)
  have hM (x : ι → ℝ) (i : ι) : M.mulVec x i=if i∈S then ∑ j∈S, A i j*x j else x i := by
    by_cases hi : i∈S
    · simp only [M, Matrix.mulVec, dotProduct, hi, ite_true, ite_mul, zero_mul]
      rw [sum_ite_mem, univ_inter]
    · simp [M, Matrix.mulVec, dotProduct, hi]
  have hinj : Function.Injective M.mulVec := by
    intro x y hxy
    have hsol : Solves A S x (fun i => ∑ j∈S, A i j*y j) := fun i hi => by
      have := congrFun hxy i
      rwa [hM, hM, ite_eq_left hi, ite_eq_left hi] at this
    funext i
    by_cases hi : i∈S
    · exact solves_unique A S μ hμ hA x y _ hsol (fun _ _ => rfl) i hi
    · have := congrFun hxy i
      rwa [hM, hM, ite_eq_right hi, ite_eq_right hi] at this
  obtain ⟨x, hx⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr
    (Matrix.mulVec_injective_iff_isUnit.mp hinj) b
  exact ⟨x, fun i hi => by rw [←hx, hM, ite_eq_left hi]⟩

/-- Entries of the reduced boundary matrix are the Schur complement entries
`A_ij - A_iI R(A_Ij)`. -/
theorem run_entry (A : Matrix ι ι ℝ) (I B : Finset ι) (hIB : Disjoint I B) (μ : ℝ) (hμ : 0<μ)
    (hA : DominatesOn A (I∪B) μ) (R : (ι → ℝ) → ι → ℝ) (hR : ∀ c, Solves A I (R c) c)
    (ks : List ι) (hks : ks.toFinset=I) (i j : ι) (hi : i∈B) (hj : j∈B) :
    (run A (I∪B) ks).1 i j=A i j-∑ k∈I, A i k*R (fun l => A l j) k := by
  have h := schurOp_eq_run A I B hIB μ hμ hA R hR ks hks (Pi.single j 1) i hi
  have hc : couple A B (Pi.single j 1)=fun l => A l j := by
    funext l
    simp only [couple]
    rw [sum_eq_single_of_mem j hj (fun k _ hk => by simp [hk])]
    simp
  rw [sum_eq_single_of_mem j hj (fun k _ hk => by simp [hk])] at h
  simp only [Pi.single_eq_same, mul_one] at h
  rw [←h]
  simp only [schurOp, hc]

/-- A perturbation of row mass `ε` costs at most `ε` of margin and adds at most
`ε` of row mass. -/
theorem stageInv_perturb (A Ah : Matrix ι ι ℝ) (S : Finset ι) (μ m ε : ℝ)
    (hA : StageInv A S μ m) (hAh : ∀ i∈S, ∑ j∈S, |Ah i j-A i j|≤ε) :
    StageInv Ah S (μ-ε) (m+ε) := by
  have hle (T : Finset ι) (i : ι) :
      ∑ j∈T, |Ah i j|≤∑ j∈T, |A i j|+∑ j∈T, |Ah i j-A i j| := by
    rw [←sum_add_distrib]
    exact sum_le_sum fun j _ => by
      have := abs_add_le (A i j) (Ah i j-A i j)
      rwa [add_sub_cancel] at this
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have hsplit := sum_erase_add S (fun j => |Ah i j-A i j|) hi
    have hd := neg_abs_le (Ah i i-A i i)
    linarith [hA.1 i hi, hle (S.erase i) i, hAh i hi]
  · linarith [hA.2 i hi, hle S i, hAh i hi]

variable (rd : ℝ → ℝ) (mul : ℝ → ℝ → ℝ) (rec : ℝ → ℝ) (η θ : ℝ)

/-- The machine-faithful solve of a computed matrix `Ah` within row mass `εA` of
a dominant `A`: the error against the exact solution of `A` is that of
`bandSolveG_error` with `εA` added to the backward error of the factors. -/
theorem bandSolveG_perturbed_error (hrd : ∀ x, |rd x-x|≤η) (hrd0 : rd 0=0)
    (hmul : ∀ a b, |mul a b-a/b|≤η) (hmul0 : ∀ b, mul 0 b=0)
    (pos : ι → ℕ) (hpos : Function.Injective pos)
    (A Ah : Matrix ι ι ℝ) (S : Finset ι) (μ m M n εA : ℝ) (hμ : 0<μ) (hM : 0≤M) (hm0 : 0≤m)
    (hinv : StageInv A S μ m) (hεA : 0≤εA) (hAh : ∀ i∈S, ∑ j∈S, |Ah i j-A i j|≤εA)
    (hcard : (S.card : ℝ)≤n) (ks : List ι) (hks : ks.toFinset=S)
    (hsort : ks.Pairwise (fun a b => pos a<pos b))
    (hm : m+εA+ks.length*(η*(n+M))≤M) (hmu : μ/2+εA+2*ks.length*(η*(n+M))≤μ)
    (hrec : ∀ c, μ/2≤c → c≤M → |c*rec c-1|≤θ) (hθ : θ≤1/2)
    (x b : ι → ℝ) (hx : Solves A S x b) (X : ℝ) (hX : 0≤X) (hxX : ∀ j∈S, |x j|≤X)
    (hsmall : (n*(ks.length*(η*(1+M)))+εA+(1+ks.length*(2*M/μ+η))*(2*θ*M))/μ≤1/2)
    (j : ι) (hj : j∈S) :
    |bandSolveG rd mul rec Ah S ks b j-x j|≤
      2*(((1+ks.length*(2*M/μ+η))*((n+M+2*θ*M)*η)+n*η)/μ+
        (n*(ks.length*(η*(1+M)))+εA+(1+ks.length*(2*M/μ+η))*(2*θ*M))/μ*X) := by
  have hη : 0≤η := le_trans (abs_nonneg _) (hrd 0)
  have hn : 0≤n := le_trans (Nat.cast_nonneg _) hcard
  have hinv' := stageInv_perturb A Ah S μ m εA hinv hAh
  obtain ⟨hgood, hU, hL⟩ := lur_good rd mul η hrd hmul μ M n hμ hM hn ks Ah S (μ-εA) (m+εA)
    hinv' hcard (by linarith) hm (by linarith)
  have hprod := lur_product rd mul η hrd hmul M hM ks Ah S hgood
  obtain ⟨hLt, hUt⟩ := fill_support_r rd mul hrd0 hmul0 pos (fun _ _ => True)
    (fun _ _ _ _ _ _ _ => trivial) ks Ah S (by rw [hks]) hsort (fun _ _ _ _ _ => trivial)
  have hmem : ∀ k∈ks, k∈S := fun k hk => hks ▸ List.mem_toFinset.mpr hk
  have hdone : (∅ : Finset ι)=S\ks.toFinset := by rw [hks, sdiff_self]; rfl
  have hf := fwdM_residual rd η hrd pos (luLr rd mul Ah S ks) b S
    (fun i k h => (hLt i k h).imp id And.right) ks ∅ (fun _ => 0) hsort hmem hdone
  have hdiag : ∀ k∈S, |luUr rd mul Ah S ks k k|≤M ∧
      |luUr rd mul Ah S ks k k*rec (luUr rd mul Ah S ks k k)-1|≤θ := by
    intro k hk
    obtain ⟨hd, hmass⟩ := hU k hk
    have h0 : 0≤∑ j∈S.erase k, |luUr rd mul Ah S ks k j| := sum_nonneg fun _ _ => abs_nonneg _
    have hle : |luUr rd mul Ah S ks k k|≤M := by
      have := single_le_sum (f := fun j => |luUr rd mul Ah S ks k j|) (fun _ _ => abs_nonneg _) hk
      linarith
    exact ⟨hle, hrec _ (by linarith) ((le_abs_self _).trans hle)⟩
  have hb := bwdM_residual rd η M θ hrd pos hpos (luUr rd mul Ah S ks) _
    (fwdM rd (luLr rd mul Ah S ks) b ∅ (fun _ => 0) ks) S (fun k j h => (hUt k j h).2) hdiag hθ hM
    ks.reverse ∅ (fun _ => 0) (List.pairwise_reverse.mpr hsort)
    (fun k hk => hmem k (List.mem_reverse.mp hk)) (by rw [List.toFinset_reverse]; exact hdone)
  have hΛ0 : 0≤1+ks.length*(2*M/μ+η) := by positivity
  have hθ0 : 0≤θ := le_trans (abs_nonneg _) (hdiag j hj).2
  have hεS : ∀ i∈S, ∑ j∈S, |∑ k∈S, luLr rd mul Ah S ks i k*luUr rd mul Ah S ks k j-A i j|≤
      n*(ks.length*(η*(1+M)))+εA := by
    intro i hi
    calc ∑ j∈S, |∑ k∈S, luLr rd mul Ah S ks i k*luUr rd mul Ah S ks k j-A i j|
        ≤∑ j∈S, ((ks.length : ℝ)*(η*(1+M))+|Ah i j-A i j|) := sum_le_sum fun j hj => by
          have := abs_add_le (∑ k∈S, luLr rd mul Ah S ks i k*luUr rd mul Ah S ks k j-Ah i j)
            (Ah i j-A i j)
          rw [sub_add_sub_cancel] at this
          linarith [hprod i hi j hj]
      _=(S.card : ℝ)*(ks.length*(η*(1+M)))+∑ j∈S, |Ah i j-A i j| := by
          rw [sum_add_distrib, sum_const, nsmul_eq_mul]
      _≤n*(ks.length*(η*(1+M)))+εA := by
          have : (S.card : ℝ)*(ks.length*(η*(1+M)))≤n*(ks.length*(η*(1+M))) := by gcongr
          linarith [hAh i hi]
  have hfη : ∀ k∈S, |fwdM rd (luLr rd mul Ah S ks) b ∅ (fun _ => 0) ks k+
      ∑ j∈S.erase k, luLr rd mul Ah S ks k j*fwdM rd (luLr rd mul Ah S ks) b ∅ (fun _ => 0) ks j-
        b k|≤n*η :=
    fun k hk => (hf k (List.mem_toFinset.mp (hks ▸ hk))).trans
      (mul_le_mul_of_nonneg_right hcard hη)
  have hbB : ∀ B, (∀ j∈S, |bandSolveG rd mul rec Ah S ks b j|≤B) → ∀ k∈S,
      |∑ j∈S, luUr rd mul Ah S ks k j*bandSolveG rd mul rec Ah S ks b j-
        fwdM rd (luLr rd mul Ah S ks) b ∅ (fun _ => 0) ks k|≤
        (n+M+2*θ*M)*η+2*θ*M*B := by
    intro B hB k hk
    have := hb B hB k (List.mem_reverse.mpr (List.mem_toFinset.mp (hks ▸ hk)))
    have hc : ((S.card : ℝ)+M+2*θ*M)*η≤(n+M+2*θ*M)*η :=
      mul_le_mul_of_nonneg_right (by linarith) hη
    unfold bandSolveG
    linarith
  exact backward_lu_k A (luLr rd mul Ah S ks) (luUr rd mul Ah S ks) S μ hμ hinv.1 x b
    (bandSolveG rd mul rec Ah S ks b) _ hx _ _ (n*η) _ (2*θ*M) X hΛ0 (by positivity)
    (by positivity) hX (fun i hi => luLr_diag rd mul Ah S ks i hi) hL hεS hxX hfη hbB hsmall j hj

end IntegerMultBounds.NLogN.SchurDominance
