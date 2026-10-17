module

public import IntegerMultBounds.NLogN.SchurSubst
import IntegerMultBounds.NLogN.PhaseCellBoundaryLU
import IntegerMultBounds.NLogN.PhaseCellBoundarySolve
import IntegerMultBounds.NLogN.PhaseCellBoundary
public import IntegerMultBounds.NLogN.PhaseCellMatrix
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star
public import IntegerMultBounds.Machine

/-! The concrete rounded band solve on the actual rounded periodic Gaussian
matrix, in physical order. With rounding `η` and `128 p s² η ≤ 1`, the computed
solution of `H x = b` with `|b| ≤ 1/2` is within `2700 s² p² η` of the exact
solution. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open scoped BigOperators
open Finset SchurDominance
variable (s t : ℕ) [NeZero s] [NeZero t]

/-- Physical order of the line. -/
def physOrder : List (ZMod s) := (List.range s).map (fun k : ℕ => (k : ZMod s))

omit [NeZero s] [NeZero t] in
theorem physOrder_sorted : (physOrder s).Pairwise (fun a b => a.val<b.val) := by
  unfold physOrder
  rw [List.pairwise_map]
  refine (List.pairwise_lt_range (n := s)).imp_of_mem fun {a b} ha hb hab => ?_
  rw [ZMod.val_cast_of_lt (List.mem_range.mp ha), ZMod.val_cast_of_lt (List.mem_range.mp hb)]
  exact hab

omit [NeZero t] in
theorem physOrder_toFinset : (physOrder s).toFinset=univ := by
  ext x
  simp only [physOrder, List.mem_toFinset, List.mem_map, List.mem_range, mem_univ, iff_true]
  exact ⟨x.val, ZMod.val_lt x, ZMod.natCast_zmod_val x⟩

omit [NeZero s] [NeZero t] in
theorem physOrder_length : (physOrder s).length=s := by simp [physOrder]

theorem bandSolve_actual (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p)
    (rd : ℝ → ℝ) (η : ℝ) (hrd : ∀ x, |rd x-x|≤η) (hrd0 : rd 0=0)
    (hsmall : 128*p*(s : ℝ)^2*η≤1)
    (x b : ZMod s → ℝ) (hx : Matrix.mulVec (realMatrix s t p u) x=b) (hb : ∀ i, |b i|≤1/2)
    (j : ZMod s) :
    |bandSolve rd (realMatrix s t p u) univ (physOrder s) b j-x j|≤2700*(s : ℝ)^2*(p : ℝ)^2*η := by
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  have hs1 : (1 : ℝ)≤s := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne s)
  have hη : 0≤η := le_trans (abs_nonneg _) (hrd 0)
  set μ : ℝ := 1/(8*(p : ℝ))
  have hμ : 0<μ := by positivity
  have hA := matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget
  have hinv : StageInv (realMatrix s t p u) univ μ 2 :=
    ⟨hA, fun i _ => row_mass s t hst hα p u hp hwidth hαu hθ hgap hbudget i⟩
  have hcard : ((univ : Finset (ZMod s)).card : ℝ)≤s := by simp [ZMod.card]
  have hlen := physOrder_length s
  have hsη : (s : ℝ)^2*η≤1/(128*p) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hpη : (p : ℝ)*(s : ℝ)^2*η≤1/128 := by linarith
  have hsol : Solves (realMatrix s t p u) univ x b := solves_of_mulVec s t p u x b hx
  have hX : ∀ i∈(univ : Finset (ZMod s)), |x i|≤4*p := by
    intro i hi
    have h := solves_bound _ _ μ hμ hA x b hsol (1/2) (fun i _ => hb i) i hi
    simp only [μ] at h
    rw [div_div_eq_mul_div, div_one] at h
    linarith
  set A := (s : ℝ)^2*η with hAdef
  have hA0 : 0≤A := by positivity
  have hsA : (s : ℝ)*η≤A := by
    rw [hAdef]; exact mul_le_mul_of_nonneg_right (by nlinarith) hη
  have hA1 : A≤1/(128*p) := hsη
  have hpA : (p : ℝ)*A≤1/128 := by rw [hAdef]; linarith
  have hη1 : η≤1 := by nlinarith
  have hm' : 2+(s : ℝ)*(η*(s+3))≤3 := by nlinarith
  have hmu' : μ/2+2*(s : ℝ)*(η*(s+3))≤μ := by
    have : (s : ℝ)*(η*(s+3))≤4*A := by nlinarith
    have hμe : μ=1/(8*(p : ℝ)) := rfl
    have : 8*A≤μ/2 := by
      rw [hμe]
      have : A*(128*p)≤1 := (le_div_iff₀ (by positivity)).mp hA1
      rw [div_div, le_div_iff₀ (by positivity)]
      nlinarith
    nlinarith
  have hsm' : (s : ℝ)*((s : ℝ)*(η*(1+3)))/μ≤1/2 := by
    have hμe : (s : ℝ)*((s : ℝ)*(η*(1+3)))/μ=32*(p*A) := by
      simp only [μ, hAdef]; field_simp; ring
    rw [hμe]; linarith
  have key := bandSolve_error rd η hrd hrd0 (fun z : ZMod s => z.val) (ZMod.val_injective s)
    (realMatrix s t p u) univ μ 2 3 s hμ (by norm_num) (by norm_num) hinv hcard (physOrder s)
    (physOrder_toFinset s) (physOrder_sorted s) (by rw [hlen]; exact hm') (by rw [hlen]; exact hmu')
    x b hsol (4*p) (by positivity) hX (by rw [hlen]; exact hsm') j (mem_univ j)
  rw [hlen] at key
  have heq : 2*(((1+(s : ℝ)*(2*3/μ+η))*(3*η)+η)/μ+(s : ℝ)*((s : ℝ)*(η*(1+3)))/μ*(4*p))=
      2*(8*p*(3*η*(1+s*(48*p+η))+η)+128*(p : ℝ)^2*A) := by
    simp only [μ, hAdef]; field_simp; ring
  rw [heq] at key
  refine key.trans ?_
  have hp1 : (1 : ℝ)≤p := by linarith
  have hsη0 : 0≤(s : ℝ)*η := by positivity
  have hPP : (p : ℝ)≤(p : ℝ)^2 := by nlinarith
  have hss : (1 : ℝ)≤(s : ℝ)^2 := by nlinarith
  have hPSP : (p : ℝ)^2≤(s : ℝ)^2*(p : ℝ)^2 := le_mul_of_one_le_left (sq_nonneg _) hss
  have h4 : (p : ℝ)^2*A=(s : ℝ)^2*(p : ℝ)^2*η := by rw [hAdef]; ring
  have h2 : (p : ℝ)^2*((s : ℝ)*η)≤(s : ℝ)^2*(p : ℝ)^2*η := by
    rw [←h4]; exact mul_le_mul_of_nonneg_left hsA (sq_nonneg _)
  have h1 : (p : ℝ)*η≤(s : ℝ)^2*(p : ℝ)^2*η :=
    mul_le_mul_of_nonneg_right (hPP.trans hPSP) hη
  have h3 : (p : ℝ)*((s : ℝ)*η)*η≤(s : ℝ)^2*(p : ℝ)^2*η := by
    have e1 : (p : ℝ)*((s : ℝ)*η)*η≤(p : ℝ)*((s : ℝ)*η)*1 :=
      mul_le_mul_of_nonneg_left hη1 (by positivity)
    have e2 : (p : ℝ)*((s : ℝ)*η)≤(p : ℝ)^2*((s : ℝ)*η) := mul_le_mul_of_nonneg_right hPP hsη0
    linarith
  have hB : 0≤(s : ℝ)^2*(p : ℝ)^2*η := by positivity
  have hexp : 2*(8*p*(3*η*(1+s*(48*p+η))+η)+128*(p : ℝ)^2*A)=
      64*((p : ℝ)*η)+2304*((p : ℝ)^2*((s : ℝ)*η))+48*((p : ℝ)*((s : ℝ)*η)*η)+
        256*((p : ℝ)^2*A) := by ring
  rw [hexp, h4]
  linarith

/-- Arithmetic for the machine-faithful solve, with `q = p`, `S = s`,
margin `1/(8q)`, mass `2`, pivot bound `3`. -/
theorem bandM_arith (q S η : ℝ) (hq : 2≤q) (hS : 1≤S) (hη : 0≤η)
    (hsmall : 2^16*q^2*S^2*η≤1) :
    2+S*(η*(S+3))≤3 ∧ 1/(8*q)/2+2*S*(η*(S+3))≤1/(8*q) ∧ 3*η≤1/2 ∧
    (S*(S*(η*(1+3)))+(1+S*(2*3/(1/(8*q))+η))*(2*(3*η)*3))/(1/(8*q))≤1/2 ∧
    2*(((1+S*(2*3/(1/(8*q))+η))*((S+3+2*(3*η)*3)*η)+S*η)/(1/(8*q))+
      (S*(S*(η*(1+3)))+(1+S*(2*3/(1/(8*q))+η))*(2*(3*η)*3))/(1/(8*q))*(4*q))≤
      62000*q^3*S^2*η := by
  have hq1 : (1 : ℝ)≤q := by linarith
  set A := S^2*η with hAdef
  have hA0 : 0≤A := by positivity
  have hS2 : S≤S^2 := by nlinarith
  have hq2 : q≤q^2 := by nlinarith
  have hq3 : q^2≤q^3 := pow_le_pow_right₀ hq1 (by norm_num)
  have hsA : S*η≤A := mul_le_mul_of_nonneg_right hS2 hη
  have hqqA : q^2*A≤1/2^16 := by
    have : 2^16*(q^2*A)≤1 := by rw [hAdef]; linarith
    rw [le_div_iff₀ (by positivity)]; linarith
  have hqA : q*A≤1/2^16 := le_trans (mul_le_mul_of_nonneg_right hq2 hA0) hqqA
  have hAq : A≤q*A := le_mul_of_one_le_left hA0 hq1
  have hAs : A≤1/2^16 := le_trans hAq hqA
  have hηA : η≤A := le_mul_of_one_le_left hη (by nlinarith)
  have hη1 : η≤1/2^16 := le_trans hηA hAs
  have hinv : 1/(1/(8*q))=8*q := by field_simp
  have hdiv (x : ℝ) : x/(1/(8*q))=x*(8*q) := by field_simp
  have hS3 : S*(η*(S+3))≤4*A := by
    have e : S*(η*(S+3))=A+3*(S*η) := by rw [hAdef]; ring
    rw [e]; linarith only [hsA]
  refine ⟨by linarith only [hS3, hAs], ?_, by linarith only [hη1], ?_, ?_⟩
  · have h8 : 8*A≤1/(8*q)/2 := by
      rw [div_div, le_div_iff₀ (by positivity)]
      have e : 8*A*(8*q*2)=128*(q*A) := by ring
      rw [e]; linarith only [hqA]
    linarith only [hS3, h8]
  · have hη1' : η≤1 := le_trans hη1 (by norm_num)
    have hqS1 : 1≤q*S := one_le_mul_of_one_le_of_one_le hq1 hS
    have hSη : S*η≤q*S := le_trans (mul_le_of_le_one_right (by linarith) hη1')
      (le_mul_of_one_le_left (by linarith) hq1)
    have hΛ : 1+S*(2*3/(1/(8*q))+η)≤50*q*S := by
      rw [hdiv]
      have e : 1+S*(2*3*(8*q)+η)=1+48*(q*S)+S*η := by ring
      rw [e]; linarith only [hqS1, hSη]
    have hk : (1+S*(2*3/(1/(8*q))+η))*(2*(3*η)*3)≤50*q*S*(18*η) := by
      rw [show 2*(3*η)*3=18*η by ring]; exact mul_le_mul_of_nonneg_right hΛ (by positivity)
    have hqS : q*(S*η)≤q*A := mul_le_mul_of_nonneg_left hsA (by positivity)
    have e1 : S*(S*(η*(1+3)))=4*A := by rw [hAdef]; ring
    have e2 : 50*q*S*(18*η)=900*(q*(S*η)) := by ring
    rw [hdiv, e1]
    have hsum : 4*A+(1+S*(2*3/(1/(8*q))+η))*(2*(3*η)*3)≤4*A+900*(q*A) := by
      linarith only [hk, e2, hqS]
    have hmono := mul_le_mul_of_nonneg_right hsum (by positivity : (0 : ℝ)≤8*q)
    have hfin : (4*A+900*(q*A))*(8*q)=32*(q*A)+7200*(q^2*A) := by ring
    have h32 : (32 : ℝ)*(1/2^16)+7200*(1/2^16)≤1/2 := by norm_num
    linarith only [hmono, hfin, hqA, hqqA, h32]
  · have hη1' : η≤1 := le_trans hη1 (by norm_num)
    have hqS1 : 1≤q*S := one_le_mul_of_one_le_of_one_le hq1 hS
    have hSη : S*η≤q*S := le_trans (mul_le_of_le_one_right (by linarith) hη1')
      (le_mul_of_one_le_left (by linarith) hq1)
    have hΛ : 1+S*(2*3*(8*q)+η)≤50*q*S := by
      have e : 1+S*(2*3*(8*q)+η)=1+48*(q*S)+S*η := by ring
      rw [e]; linarith only [hqS1, hSη]
    have hδ : (S+3+2*(3*η)*3)*η≤5*(S*η) := by
      have h3 : 3+2*(3*η)*3≤4*S := by linarith only [hη1, hS]
      have e : (S+3+2*(3*η)*3)*η=S*η+(3+2*(3*η)*3)*η := by ring
      have h4 : (3+2*(3*η)*3)*η≤(4*S)*η := mul_le_mul_of_nonneg_right h3 hη
      have e4 : (4*S)*η=4*(S*η) := by ring
      rw [e]; linarith only [h4, e4]
    have h1 : (1+S*(2*3*(8*q)+η))*((S+3+2*(3*η)*3)*η)≤50*q*S*(5*(S*η)) :=
      mul_le_mul hΛ hδ (by positivity) (by positivity)
    have hk : (1+S*(2*3*(8*q)+η))*(2*(3*η)*3)≤50*q*S*(18*η) := by
      rw [show 2*(3*η)*3=18*η by ring]; exact mul_le_mul_of_nonneg_right hΛ (by positivity)
    have e1 : S*(S*(η*(1+3)))=4*A := by rw [hAdef]; ring
    have e3 : 50*q*S*(5*(S*η))=250*(q*A) := by rw [hAdef]; ring
    have e4 : 50*q*S*(18*η)=900*(q*(S*η)) := by ring
    simp only [hdiv]
    rw [e1]
    have hT1 := mul_le_mul_of_nonneg_right
      (show (1+S*(2*3*(8*q)+η))*((S+3+2*(3*η)*3)*η)+S*η≤250*(q*A)+S*η by
        linarith only [h1, e3]) (by positivity : (0 : ℝ)≤8*q)
    have hT2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (show 4*A+(1+S*(2*3*(8*q)+η))*(2*(3*η)*3)≤4*A+900*(q*(S*η)) by
        linarith only [hk, e4]) (by positivity : (0 : ℝ)≤8*q)) (by positivity : (0 : ℝ)≤4*q)
    have e5 : (250*(q*A)+S*η)*(8*q)=2000*(q^2*A)+8*(q*(S*η)) := by ring
    have e6 : (4*A+900*(q*(S*η)))*(8*q)*(4*q)=128*(q^2*A)+28800*(q^3*(S*η)) := by ring
    have hq3S : q^3*(S*η)≤q^3*A := mul_le_mul_of_nonneg_left hsA (by positivity)
    have hq2S : q^2*(S*η)≤q^3*A := le_trans (mul_le_mul_of_nonneg_left hsA (by positivity))
      (mul_le_mul_of_nonneg_right hq3 hA0)
    have hqSη : q*(S*η)≤q^3*A := le_trans (mul_le_mul_of_nonneg_right hq2 (by positivity)) hq2S
    have hqA3 : q^2*A≤q^3*A := mul_le_mul_of_nonneg_right hq3 hA0
    have hgoal : 62000*q^3*S^2*η=62000*(q^3*A) := by rw [hAdef]; ring
    rw [hgoal]
    have hB : 0≤q^3*A := by positivity
    linarith only [hT1, hT2, e5, e6, hq3S, hqSη, hqA3, hB]

/-- The machine-faithful band solve on the actual matrix: with
`2^16 p² s² η ≤ 1`, error at most `62000 p³ s² η`. -/
theorem bandSolveM_actual (hst : s<t) {α d : ℝ} (hα : 0<α)
    (p u : ℕ) (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p)
    (rd : ℝ → ℝ) (η : ℝ) (hrd : ∀ x, |rd x-x|≤η) (hrd0 : rd 0=0)
    (hsmall : 2^16*(p : ℝ)^2*(s : ℝ)^2*η≤1)
    (x b : ZMod s → ℝ) (hx : Matrix.mulVec (realMatrix s t p u) x=b) (hb : ∀ i, |b i|≤1/2)
    (j : ZMod s) :
    |bandSolveM rd (realMatrix s t p u) univ (physOrder s) b j-x j|≤
      62000*(p : ℝ)^3*(s : ℝ)^2*η := by
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  have hs1 : (1 : ℝ)≤s := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne s)
  have hη : 0≤η := le_trans (abs_nonneg _) (hrd 0)
  have hμ : (0 : ℝ)<1/(8*(p : ℝ)) := by positivity
  have hA := matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget
  have hinv : StageInv (realMatrix s t p u) univ (1/(8*(p : ℝ))) 2 :=
    ⟨hA, fun i _ => row_mass s t hst hα p u hp hwidth hαu hθ hgap hbudget i⟩
  have hcard : ((univ : Finset (ZMod s)).card : ℝ)≤s := by simp [ZMod.card]
  have hlen := physOrder_length s
  have hsol : Solves (realMatrix s t p u) univ x b := solves_of_mulVec s t p u x b hx
  have hX : ∀ i∈(univ : Finset (ZMod s)), |x i|≤4*p := by
    intro i hi
    have h := solves_bound _ _ _ hμ hA x b hsol (1/2) (fun i _ => hb i) i hi
    rw [div_div_eq_mul_div, div_one] at h
    linarith
  obtain ⟨hm', hmu', hMη, hsm', hfin⟩ := bandM_arith (p : ℝ) (s : ℝ) η hpR hs1 hη hsmall
  have key := bandSolveM_error rd η hrd hrd0 (fun z : ZMod s => z.val) (ZMod.val_injective s)
    (realMatrix s t p u) univ (1/(8*(p : ℝ))) 2 3 s hμ (by norm_num) (by norm_num) hinv hcard
    (physOrder s) (physOrder_toFinset s) (physOrder_sorted s) (by rw [hlen]; exact hm')
    (by rw [hlen]; exact hmu') hMη x b hsol (4*p) (by positivity) hX (by rw [hlen]; exact hsm')
    j (mem_univ j)
  rw [hlen] at key
  exact key.trans hfin

end IntegerMultBounds.NLogN.PhaseCellMatrix
