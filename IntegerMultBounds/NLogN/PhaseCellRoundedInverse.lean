module

public import IntegerMultBounds.NLogN.PhaseCellRoundedSchur
public import IntegerMultBounds.NLogN.PhaseCellRoundedSolve
import IntegerMultBounds.NLogN.SchurBlockError
import IntegerMultBounds.NLogN.PhaseCellBoundary
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star
public import IntegerMultBounds.Machine

/-! # The rounded phase-cell inverse

The source's solve of `A x = b` on the actual rounded periodic Gaussian matrix, with every
stage computed:

1. `y ≈ R b` on the interior, within `e₁`;
2. `r ≈ b_B - A_BI y` on the boundary, within `e₂`;
3. `x_B`, the machine-faithful solve of the computed boundary matrix with right-hand side `r`
   (`rounded_schur_solve`);
4. `c ≈ b_I - A_IB x_B` within `e₄`, and `x_I ≈ R c` within `e₅`.

With `|b| ≤ β` the boundary right-hand side is at most `(1 + 8p) β + e₁ + e₂`, so the boundary
stage error is `e₃ = 2^16 p³ N (N η + eR + θ) (1 + (1 + 8p) β + e₁ + e₂)`, the boundary values
are within `e₃ + 8p (e₁ + e₂)` and the interior values within
`e₅ + 8p (e₄ + e₃ + 8p (e₁ + e₂))` of the exact solution (`rounded_inverse`). The interior
errors `e₁`, `e₅` and `eR` come from the rounded cell solves (`rounded_interior`); the boundary
columns are interior right-hand sides at most one (`entry_le_one`). -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open scoped BigOperators
open Finset SchurDominance
variable (s t : ℕ) [NeZero s] [NeZero t]

/-- Off-diagonal entries of the actual matrix are at most one, so every boundary column is an
interior right-hand side of size at most one. -/
theorem entry_le_one (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p) (l j : ZMod s) (hlj : l≠j) :
    |realMatrix s t p u l j|≤1 :=
  (single_le_sum (f := fun k => |realMatrix s t p u l k|) (fun _ _ => abs_nonneg _)
    (mem_erase.mpr ⟨hlj.symm, mem_univ j⟩)).trans
    (offDiag_mass s t hst hα p u hp hwidth hαu hθ hgap hbudget l)

theorem rounded_inverse (hst : s<t) {α d : ℝ} (hα : 0<α)
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
    (b x : ZMod s → ℝ) (hx : Matrix.mulVec (realMatrix s t p u) x=b) (β : ℝ)
    (hb : ∀ i, |b i|≤β) (e₁ e₂ e₄ e₅ : ℝ) (he₁ : 0≤e₁) (he₂ : 0≤e₂)
    (y r c xI : ZMod s → ℝ)
    (hy : ∀ j∈I, |y j-R b j|≤e₁)
    (hr : ∀ i∈univ\I, |r i-(b i-∑ j∈I, realMatrix s t p u i j*y j)|≤e₂)
    (hc : ∀ i∈I, |c i-(b i-couple (realMatrix s t p u) (univ\I)
      (bandSolveG rd mul rec Sh (univ\I) kb r) i)|≤e₄)
    (hxI : ∀ j∈I, |xI j-R c j|≤e₅) :
    (∀ j∈univ\I, |bandSolveG rd mul rec Sh (univ\I) kb r j-x j|≤
        2^16*(p : ℝ)^3*(N*(N*η+eR+θ))*(1+((1+8*p)*β+e₁+e₂))+8*p*(e₁+e₂)) ∧
      ∀ j∈I, |xI j-x j|≤e₅+8*p*(e₄+(2^16*(p : ℝ)^3*(N*(N*η+eR+θ))*(1+((1+8*p)*β+e₁+e₂))+
        8*p*(e₁+e₂))) := by
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  have hμ : (0 : ℝ)<1/(8*(p : ℝ)) := by positivity
  have hη : 0≤η := le_trans (abs_nonneg _) (hrd 0)
  have hθ0 : 0≤θ := le_trans (abs_nonneg _) (hrec 1
    (by rw [div_div, div_le_one (by positivity)]; linarith) (by norm_num))
  have hβ : 0≤β := le_trans (abs_nonneg _) (hb 0)
  have hU : I∪(univ\I)=univ := union_sdiff_of_subset (subset_univ I)
  have hIB : Disjoint I (univ\I) := disjoint_sdiff
  have hA0 := matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget
  have hA := hA0
  rw [←hU] at hA
  have hks : I.toList.toFinset=I := toList_toFinset I
  obtain ⟨Z, hZs⟩ := solves_exists _ _ _ hμ (schur_dominates _ I _ hIB _ hμ hA _ hks) r
  have hZ : ∀ i∈univ\I, schurOp (realMatrix s t p u) I (univ\I) R Z i=r i := fun i hi => by
    rw [schurOp_eq_run _ I _ hIB _ hμ hA R hR _ hks Z i hi]
    exact hZs i hi
  -- The boundary right-hand side is at most `(1 + 8p) β + e₁ + e₂`.
  have hAI := dominates_mono _ univ I _ (subset_univ I) hA0
  have hy' : ∀ j∈I, |y j|≤8*p*β+e₁ := by
    intro j hj
    have h := solves_bound _ _ _ hμ hAI (R b) b (hR b) β (fun i _ => hb i) j hj
    rw [div_div_eq_mul_div, div_one] at h
    have := abs_add_le (y j-R b j) (R b j)
    rw [sub_add_cancel] at this
    linarith [hy j hj]
  have hρ : ∀ i∈univ\I, |r i|≤(1+8*p)*β+e₁+e₂ := by
    intro i hi
    have hmassI : ∑ k∈I, |realMatrix s t p u i k|≤1 :=
      (sum_le_sum_of_subset_of_nonneg (fun k hk => mem_erase.mpr
        ⟨fun h => (mem_sdiff.mp hi).2 (by rw [←h]; exact hk), mem_univ k⟩)
        fun _ _ _ => abs_nonneg _).trans
        (offDiag_mass s t hst hα p u hp hwidth hαu hθ hgap hbudget i)
    have h1 := row_bound (realMatrix s t p u) I y i 1 (8*p*β+e₁) hmassI (by positivity) hy'
    have h2 := abs_add_le (r i-(b i-∑ j∈I, realMatrix s t p u i j*y j))
      (b i-∑ j∈I, realMatrix s t p u i j*y j)
    rw [sub_add_cancel] at h2
    have h3 := abs_sub (b i) (∑ j∈I, realMatrix s t p u i j*y j)
    linarith [hr i hi, hb i]
  have he₃ : 0≤2^16*(p : ℝ)^3*(N*(N*η+eR+θ))*(1+((1+8*p)*β+e₁+e₂)) := by positivity
  exact rounded_four_step s t hst hα p u hp hwidth hαu hθ hgap hbudget I R hR b x hx e₁ e₂ _ e₄ e₅
    he₁ he₂ he₃ y r Z _ c xI hy hr hZ
    (fun j hj => rounded_schur_solve s t hst hα p u hp hwidth hαu hθ hgap hbudget I R hR rd mul
      rec η θ eR hrd hrd0 hmul hmul0 hrec heR N hcardN hsmall Rel hRel kb pos hpos hkb hsort Y Sh
      hY hSh hSh0 r Z hZ _ hρ j hj)
    hc hxI

end IntegerMultBounds.NLogN.PhaseCellMatrix
