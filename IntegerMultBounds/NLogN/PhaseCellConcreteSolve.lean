module

public import IntegerMultBounds.NLogN.PhaseCellConcreteInterior
public import IntegerMultBounds.NLogN.PhaseCellBoundaryFold
public import IntegerMultBounds.NLogN.PhaseCellRoundedInverse
public import IntegerMultBounds.NLogN.PhaseCellFoldSolve
import IntegerMultBounds.NLogN.SchurCongr
import IntegerMultBounds.NLogN.ToeplitzLocal
import IntegerMultBounds.NLogN.SchurBlockError
import IntegerMultBounds.NLogN.PhaseCellBoundary
import IntegerMultBounds.NLogN.PhaseCellBoundaryLU
import IntegerMultBounds.NLogN.PhaseCellRoundedSolve
import IntegerMultBounds.NLogN.PhaseCellBoundarySolve
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star
public import IntegerMultBounds.Machine

/-! # The concrete phase-cell line solve

`pcSolve` is the source's solve of `A x = b` on the actual rounded periodic Gaussian matrix with
every stage computed by single roundings `rd`:

1. `y = pcInterior b`, the concrete cell runs on the right-hand side;
2. `r = rd (b_B - A_BI y)` (`pcRes`);
3. `x_B`, the machine solve `bandSolveG` with the rules `machMul`, `newtonR` of the computed
   boundary matrix `pcSchur` in the folded boundary order (`pcBoundary`); `pcSchur` takes the
   entries of the folded band of half width `8w + 1` from the concrete interior responses to the
   boundary columns, rounded once, and is zero elsewhere;
4. `c = rd (b_I - A_IB x_B)` (`pcRecov`) and `x_I = pcInterior c`.

With `|b| ≤ 1/2` and `2^(8p+46) p⁷ s² η ≤ 1/2` its output is within `2^(8p+46) p⁷ s² η` of the
exact solution (`pcSolve_error`). The Newton reciprocals use `β = 1/(32p)`. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open scoped BigOperators
open Finset SchurDominance
variable (s t : ℕ) [NeZero s] (p u : ℕ)

/-- The computed boundary matrix: the entries of the folded band of half width `8w + 1` from the
concrete interior responses to the boundary columns, rounded once; zero outside the band. -/
noncomputable def pcSchur (rd : ℝ → ℝ) (I : Finset (ZMod s)) : Matrix (ZMod s) (ZMod s) ℝ :=
  fun i j => if FoldBRel s (univ\I) (2*(4*PhaseCellBand.width p u)+1) i j then
    rd (realMatrix s t p u i j-∑ k∈I, realMatrix s t p u i k*
      pcInterior s t p u rd I (fun l => realMatrix s t p u l j) k)
  else 0

/-- The boundary right-hand side `b_B - A_BI y`, rounded once. -/
noncomputable def pcRes (rd : ℝ → ℝ) (I : Finset (ZMod s)) (b : ZMod s → ℝ) (i : ZMod s) : ℝ :=
  rd (b i-∑ j∈I, realMatrix s t p u i j*pcInterior s t p u rd I b j)

/-- The boundary solve: the machine solve of the computed boundary matrix in folded order. -/
noncomputable def pcBoundary (rd : ℝ → ℝ) (K : ℕ) (I : Finset (ZMod s)) (b : ZMod s → ℝ) :
    ZMod s → ℝ :=
  bandSolveG rd (machMul rd K) (fun c => NewtonRecip.newtonR rd c K) (pcSchur s t p u rd I)
    (univ\I) (bFoldOrder s (univ\I)) (pcRes s t p u rd I b)

/-- The interior right-hand side `b_I - A_IB x_B`, rounded once. -/
noncomputable def pcRecov (rd : ℝ → ℝ) (K : ℕ) (I : Finset (ZMod s)) (b : ZMod s → ℝ)
    (i : ZMod s) : ℝ :=
  rd (b i-couple (realMatrix s t p u) (univ\I) (pcBoundary s t p u rd K I b) i)

/-- **The concrete phase-cell line solve.** -/
noncomputable def pcSolve (rd : ℝ → ℝ) (K : ℕ) (I : Finset (ZMod s)) (b : ZMod s → ℝ) :
    ZMod s → ℝ :=
  glue I (pcInterior s t p u rd I (pcRecov s t p u rd K I b)) (pcBoundary s t p u rd K I b)

omit [NeZero s] in
/-- The size bookkeeping of the concrete solve, in `P = p`, `S = s`, `Q = 2^(8p+2)`, the list
length `L ≤ S` and the rounding `η`. -/
private theorem pc_arith (P S Q L η η' θ e₁ eR εA e₃ errB C₅ e₅ : ℝ)
    (hP : 2≤P) (hS : 1≤S) (hQ : 1≤Q) (hLS : L≤S) (hη : 0≤η)
    (hsmall : 2^44*P^7*Q*S^2*η≤1/2)
    (hη' : η'=η*(1+184320*P^2)) (hθ : θ=184320*P^2*η)
    (he₁ : e₁=η+64*S*η*((1/2+1)*Q)+2*(η+1/2*η))
    (heR : eR=η+64*S*η*((1+1)*Q)+2*(η+1*η))
    (hεA : εA=S*(η'+eR))
    (he₃ : e₃=2^16*P^3*(S*(S*η'+eR+θ))*(1+((1+8*P)*(1/2)+e₁+η)))
    (herrB : errB=e₃+8*P*(e₁+η))
    (hC₅ : C₅=1/2+η+(4*P+errB))
    (he₅ : e₅=η+64*S*η*((C₅+1)*Q)+2*(η+C₅*η)) :
    η≤1 ∧ S*η≤1 ∧ 5*η≤2*(1/(32*P)/4)/9 ∧
      2^13*P^2*(S*(S*η'+eR+θ))≤1 ∧
      2+εA+L*(η'*(S+3))≤3 ∧
      (1/(8*P)-εA)/2+2*L*(η'*(S+3))≤1/(8*P)-εA ∧
      1/(32*P)≤(1/(8*P)-εA)/2 ∧
      0≤e₁ ∧ 0≤eR ∧ 0≤εA ∧ 0≤C₅ ∧ 0≤errB ∧
      errB≤2^44*P^7*Q*S^2*η ∧ e₅+8*P*(η+errB)≤2^44*P^7*Q*S^2*η := by
  have hP0 : 0<P := by linarith only [hP]
  have hS0 : 0<S := by linarith only [hS]
  have hP1 : 1≤P := by linarith only [hP]
  obtain ⟨m, hm⟩ : ∃ m, m=P^2*Q*S^2*η := ⟨_, rfl⟩
  have hZ : P^5*m=P^7*Q*S^2*η := by rw [hm]; ring
  have hsm : 2^44*(P^5*m)≤1/2 := by rw [hZ]; linarith only [hsmall]
  have hP2 : 1≤P^2 := one_le_pow₀ hP1
  have hm0 : 0≤m := by rw [hm]; positivity
  have hP5m : 0≤P^5*m := by positivity
  have hPm : P*m≤P^5*m :=
    mul_le_mul_of_nonneg_right (le_self_pow₀ hP1 (by norm_num)) hm0
  have hP2m : P^2*m≤P^5*m := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hP1 (by norm_num)) hm0
  have hP4m : P^4*m≤P^5*m := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hP1 (by norm_num)) hm0
  have hP14 : P*m≤P^4*m := mul_le_mul_of_nonneg_right (le_self_pow₀ hP1 (by norm_num)) hm0
  have hP4m0 : 0≤P^4*m := by positivity
  have hmP : m≤P*m := le_mul_of_one_le_left hm0 hP1
  -- monomials below `m`
  have hmono (x F : ℝ) (hx : 0≤x) (hF : 1≤F) (he : F*x=m) : x≤m :=
    (le_mul_of_one_le_left hx hF).trans_eq he
  have hQS : 1≤Q*S := one_le_mul_of_one_le_of_one_le hQ hS
  have hS2 : 1≤S^2 := one_le_pow₀ hS
  have f1 : η≤m := hmono η (P^2*Q*S^2) hη
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hP2 hQ) hS2)
    (by rw [hm])
  have f2 : S*η≤m := hmono _ (P^2*Q*S) (by positivity)
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hP2 hQ) hS)
    (by rw [hm]; ring)
  have f3 : S*Q*η≤m := hmono _ (P^2*S) (by positivity) (one_le_mul_of_one_le_of_one_le hP2 hS)
    (by rw [hm]; ring)
  have f4 : S^2*Q*η≤m := hmono _ (P^2) (by positivity) hP2 (by rw [hm]; ring)
  have f6 : P^2*S*η≤m := hmono _ (Q*S) (by positivity) hQS (by rw [hm]; ring)
  have f7 : P^2*S^2*η≤m := hmono _ Q (by positivity) hQ (by rw [hm]; ring)
  have f8 : S^2*η≤m := hmono _ (P^2*Q) (by positivity) (one_le_mul_of_one_le_of_one_le hP2 hQ)
    (by rw [hm]; ring)
  have f9 : P*S*Q*η≤P*m := calc
    P*S*Q*η=P*(S*Q*η) := by ring
    _≤P*m := mul_le_mul_of_nonneg_left f3 hP0.le
  have hPη : P*η≤P*m := mul_le_mul_of_nonneg_left f1 hP0.le
  -- the error terms
  have hη'0 : 0≤η' := by rw [hη']; positivity
  have hθ0 : 0≤θ := by rw [hθ]; positivity
  have he₁le : e₁≤100*m := by rw [he₁]; linarith only [f1, f3]
  have he₁0 : 0≤e₁ := by rw [he₁]; positivity
  have heRle : eR≤133*m := by rw [heR]; linarith only [f1, f3]
  have heR0 : 0≤eR := by rw [heR]; positivity
  have hSX : S*(S*η'+eR+θ)≤2^19*m := by
    rw [hη', hθ, heR]; linarith only [f2, f4, f6, f7, f8, hm0]
  have hεAle : εA≤2^19*m := by rw [hεA, hη', heR]; linarith only [f2, f4, f6, hm0]
  have hεA0 : 0≤εA := by rw [hεA]; positivity
  have hLt : L*(η'*(S+3))≤2^20*m := by
    have h1 := mul_le_mul_of_nonneg_right hLS (by positivity : (0 : ℝ)≤η'*(S+3))
    have h2 : S*(η'*(S+3))≤2^20*m := by rw [hη']; linarith only [f2, f6, f7, f8, hm0]
    linarith only [h1, h2]
  have h8P : 2^23*m≤1/(8*P) := by
    rw [le_div_iff₀ (by positivity)]
    linarith only [hPm, hsm, hP5m]
  have e32 : 1/(32*P)=1/(8*P)/4 := by field_simp; ring
  have e576 : 2*(1/(32*P)/4)/9=1/(576*P) := by field_simp; ring
  -- the boundary error and the recovery bound
  have hF : 1+((1+8*P)*(1/2)+e₁+η)≤5*P := by
    linarith only [he₁le, f1, hmP, hPm, hsm, hP5m, hP]
  have hF0 : 0≤1+((1+8*P)*(1/2)+e₁+η) := by positivity
  have he₃le : e₃≤2^16*P^3*(2^19*m)*(5*P) := by
    rw [he₃]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hSX (by positivity)) hF hF0 (by positivity)
  have he₃' : 2^16*P^3*(2^19*m)*(5*P)=5*2^35*(P^4*m) := by ring
  have herrBle : errB≤2^38*(P^4*m) := by
    have h := mul_le_mul_of_nonneg_left (show e₁+η≤101*m by linarith only [he₁le, f1]) hP0.le
    rw [herrB]; linarith only [he₃le, he₃', h, hP14, hP4m0]
  have herrB0 : 0≤errB := by rw [herrB, he₃]; positivity
  have hC₅le : C₅≤5*P := by
    rw [hC₅]; linarith only [herrBle, hP4m, hsm, hP5m, f1, hmP, hPm, hP]
  have hC₅0 : 0≤C₅ := by rw [hC₅]; positivity
  have he₅le : e₅≤400*(P*m) := by
    have h1 : 64*S*η*((C₅+1)*Q)≤64*S*η*((5*P+1)*Q) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith only [hC₅le])
        (by linarith only [hQ])) (by positivity)
    have h2 : C₅*η≤5*P*η := mul_le_mul_of_nonneg_right hC₅le hη
    rw [he₅]; linarith only [h1, h2, hPη, f1, f3, f9, hmP, hm0]
  have hfin : 8*P*errB≤2^41*(P^5*m) := by
    have h := mul_le_mul_of_nonneg_left herrBle (by positivity : (0 : ℝ)≤8*P)
    have e : 8*P*(2^38*(P^4*m))=2^41*(P^5*m) := by ring
    linarith only [h, e]
  refine ⟨by linarith only [f1, hmP, hPm, hsm, hP5m], by linarith only [f2, hmP, hPm, hsm, hP5m],
    ?_, ?_, by linarith only [hεAle, hLt, hmP, hPm, hsm, hP5m, hm0],
    by linarith only [h8P, hεAle, hLt, hm0], ?_, he₁0, heR0, hεA0, hC₅0, herrB0, ?_, ?_⟩
  · rw [e576, le_div_iff₀ (by positivity)]
    linarith only [hPη, hPm, hsm, hP5m]
  · have h := mul_le_mul_of_nonneg_left hSX (by positivity : (0 : ℝ)≤2^13*P^2)
    have e : 2^13*P^2*(2^19*m)=2^32*(P^2*m) := by ring
    linarith only [h, e, hP2m, hsm, hP5m]
  · rw [e32]; linarith only [h8P, hεAle, hm0]
  · linarith only [herrBle, hP4m, hP5m, hZ]
  · linarith only [he₅le, hfin, hPη, hPm, hmP, hP5m, hZ]

variable [NeZero t]

/-- **The concrete phase-cell solve** is within `2^(8p+46) p⁷ s² η` of the exact solution for
right-hand sides at most `1/2`. -/
theorem pcSolve_error (hst : s<t) {α d : ℝ} (hα : 0<α)
    (hp : 2≤p) (hwidth : 8*p≤2^u) (hαu : α^2=(u : ℝ))
    (hθ : 1/(4*(p : ℝ))≤(t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1)) (hbudget : α^2*d≤p)
    (I : Finset (ZMod s)) (hI : ∀ j, j∈I ↔ Interior s t (PhaseCellBand.width p u) j)
    (rd : ℝ → ℝ) (η : ℝ) (hrd : ∀ x, |rd x-x|≤η) (hrd0 : rd 0=0) (K : ℕ)
    (hK : (1-1/(32*(p : ℝ))/4/2)^(2^K)≤3*(5*η)/(1/(32*(p : ℝ))/4))
    (hsmall : 2^(8*p+46)*(p : ℝ)^7*(s : ℝ)^2*η≤1/2)
    (x b : ZMod s → ℝ) (hx : Matrix.mulVec (realMatrix s t p u) x=b) (hb : ∀ i, |b i|≤1/2)
    (j : ZMod s) :
    |pcSolve s t p u rd K I b j-x j|≤2^(8*p+46)*(p : ℝ)^7*(s : ℝ)^2*η := by
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  have hp0 : 0<p := by omega
  have hu : 1≤u := by
    by_contra h
    have : u=0 := by omega
    simp [this] at hwidth
    omega
  have hθpos : 0<(t : ℝ)/s-1 := (by positivity : 0<1/(4*(p : ℝ))).trans_le hθ
  have hη : 0≤η := le_trans (abs_nonneg _) (hrd 0)
  have hs1 : (1 : ℝ)≤s := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne s)
  have hQ : (1 : ℝ)≤2^(8*p+2) := one_le_pow₀ (by norm_num)
  have hμ : (0 : ℝ)<1/(8*(p : ℝ)) := by positivity
  have hA0 := matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget
  have hAI := dominates_mono _ univ I _ (subset_univ I) hA0
  obtain ⟨R, hR⟩ := exists_solver (realMatrix s t p u) I _ hμ hAI
  have hcardB : (univ\I).card≤s := by
    have := card_le_univ (univ\I)
    rwa [ZMod.card] at this
  have hlen : ((bFoldOrder s (univ\I)).length : ℝ)≤s := by
    rw [bFoldOrder_length]; exact_mod_cast hcardB
  -- The error terms and their bookkeeping.
  obtain ⟨η', hη'⟩ : ∃ e, e=η*(1+184320*(p : ℝ)^2) := ⟨_, rfl⟩
  obtain ⟨θ, hθe⟩ : ∃ e, e=184320*(p : ℝ)^2*η := ⟨_, rfl⟩
  obtain ⟨e₁, he₁⟩ : ∃ e, e=η+64*(s : ℝ)*η*((1/2+1)*2^(8*p+2))+2*(η+1/2*η) := ⟨_, rfl⟩
  obtain ⟨eR, heR⟩ : ∃ e, e=η+64*(s : ℝ)*η*((1+1)*2^(8*p+2))+2*(η+1*η) := ⟨_, rfl⟩
  obtain ⟨εA, hεA⟩ : ∃ e, e=(s : ℝ)*(η'+eR) := ⟨_, rfl⟩
  obtain ⟨e₃, he₃⟩ : ∃ e, e=2^16*(p : ℝ)^3*((s : ℝ)*((s : ℝ)*η'+eR+θ))*
      (1+((1+8*(p : ℝ))*(1/2)+e₁+η)) := ⟨_, rfl⟩
  obtain ⟨errB, herrB⟩ : ∃ e, e=e₃+8*(p : ℝ)*(e₁+η) := ⟨_, rfl⟩
  obtain ⟨C₅, hC₅⟩ : ∃ e, e=1/2+η+(4*(p : ℝ)+errB) := ⟨_, rfl⟩
  obtain ⟨e₅, he₅⟩ : ∃ e, e=η+64*(s : ℝ)*η*((C₅+1)*2^(8*p+2))+2*(η+C₅*η) := ⟨_, rfl⟩
  have hsmall' : 2^44*(p : ℝ)^7*2^(8*p+2)*(s : ℝ)^2*η≤1/2 := by
    have e : (2 : ℝ)^(8*p+46)=2^44*2^(8*p+2) := by ring
    rw [e] at hsmall; linarith
  obtain ⟨hη1, hsη, hηβ, hsmS, hmS, hmuS, hβμ, he₁0, heR0, hεA0, hC₅0, herrB0, hBfin, hIfin⟩ :=
    pc_arith (p : ℝ) (s : ℝ) (2^(8*p+2)) _ η η' θ e₁ eR εA e₃ errB C₅ e₅ hpR hs1 hQ
      hlen hη hsmall' hη' hθe he₁ heR hεA he₃ herrB hC₅ he₅
  have hη'0 : 0≤η' := by rw [hη']; positivity
  have hηη' : η≤η' := by rw [hη']; nlinarith [mul_nonneg hη (sq_nonneg (p : ℝ))]
  have hrd' : ∀ x, |rd x-x|≤η' := fun x => (hrd x).trans hηη'
  -- The guarded reciprocal rules.
  have hβ : (0 : ℝ)<1/(32*(p : ℝ)) := by positivity
  have hβ2 : η*(1+60*3/(1/(32*(p : ℝ)))^2)=η' := by rw [hη']; field_simp; ring
  have hβ3 : 180*η/(1/(32*(p : ℝ)))^2=θ := by rw [hθe]; field_simp; ring
  have hmulR : ∀ a c, |NewtonRecip.recipMul rd 3 (1/(32*(p : ℝ))) K a c-a/c|≤η' := fun a c =>
    (NewtonRecip.recipMul_err rd η hrd 3 _ (by norm_num) hβ hηβ K hK a c).trans (le_of_eq hβ2)
  have hβ16 : 1/(32*(p : ℝ))≤1/(8*(p : ℝ))/2 := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  have hrecR : ∀ c, 1/(8*(p : ℝ))/2≤c → c≤3 →
      |c*NewtonRecip.recipNewton rd (1/(32*(p : ℝ))) K c-1|≤θ := fun c hc hc3 =>
    (NewtonRecip.recipNewton_residual rd η hrd _ hβ hηβ K hK c (hβ16.trans hc) hc3).trans
      (le_of_eq hβ3)
  -- The interior responses.
  have hy : ∀ j∈I, |pcInterior s t p u rd I b j-R b j|≤e₁ := fun j hj => by
    have := pcInterior_error s t p u hst hp0 hu hαu hθpos hgap hbudget I hI (R b) b (hR b) rd η
      hrd hη1 hsη (1/2) (by norm_num) (fun k _ => hb k) j hj
    rwa [←he₁] at this
  have hY : ∀ i∈univ\I, ∀ j∈univ\I, ∀ k∈I, realMatrix s t p u i k≠0 →
      |pcInterior s t p u rd I (fun l => realMatrix s t p u l j) k-
        R (fun l => realMatrix s t p u l j) k|≤eR := fun i _ j hj k hk _ => by
    have := pcInterior_error s t p u hst hp0 hu hαu hθpos hgap hbudget I hI _ _ (hR _) rd η hrd
      hη1 hsη 1 zero_le_one (fun l hl => entry_le_one s t hst hα p u hp hwidth hαu hθ hgap hbudget
        l j (fun h => (mem_sdiff.mp hj).2 (by rw [←h]; exact hl))) k hk
    rwa [←heR] at this
  -- The folded band of the boundary system.
  have hRel : ∀ ks : List (ZMod s), ks.toFinset=I → ∀ i∈univ\I, ∀ j∈univ\I,
      (run (realMatrix s t p u) univ ks).1 i j≠0 →
        FoldBRel s (univ\I) (2*(4*PhaseCellBand.width p u)+1) i j :=
    fun ks hks i hi j hj h => cycRel_foldBRel s _ _ hi hj (schur_cycRel s t hst p u ks
      (fun k hk => (hI k).mp (hks ▸ List.mem_toFinset.mpr hk)) I hI i j h)
  have hSh : ∀ i∈univ\I, ∀ j∈univ\I, FoldBRel s (univ\I) (2*(4*PhaseCellBand.width p u)+1) i j →
      |pcSchur s t p u rd I i j-(realMatrix s t p u i j-∑ k∈I, realMatrix s t p u i k*
        pcInterior s t p u rd I (fun l => realMatrix s t p u l j) k)|≤η' := fun i _ j _ h => by
    unfold pcSchur; rw [ite_eq_left h]; exact hrd' _
  have hSh0 : ∀ i∈univ\I, ∀ j∈univ\I,
      ¬FoldBRel s (univ\I) (2*(4*PhaseCellBand.width p u)+1) i j → pcSchur s t p u rd I i j=0 :=
    fun i _ j _ h => by unfold pcSchur; rw [ite_eq_right h]
  -- The machine rules agree with the guarded ones.
  have hrows : ∀ i∈univ\I, ∑ j∈univ\I, |pcSchur s t p u rd I i j-
      (run (realMatrix s t p u) univ I.toList).1 i j|≤εA := fun i hi =>
    (rounded_schur_rows s t hst hα p u hp hwidth hαu hθ hgap hbudget I R hR I.toList
      (toList_toFinset I) η' eR hη'0 heR0 _ (hRel _ (toList_toFinset I)) _ _ hY hSh hSh0 i hi).trans
      (by rw [hεA]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcardB) (by positivity))
  have hinvSh := stageInv_perturb _ (pcSchur s t p u rd I) _ _ 2 εA
    (schur_stageInv s t hst hα p u hp hwidth hαu hθ hgap hbudget I I.toList (toList_toFinset I))
    hrows
  have hμc : 0<1/(8*(p : ℝ))-εA := by linarith
  have hcong : ∀ b', pcBoundary s t p u rd K I b'=bandSolveG rd
      (NewtonRecip.recipMul rd 3 (1/(32*(p : ℝ))) K) (NewtonRecip.recipNewton rd (1/(32*(p : ℝ))) K)
      (pcSchur s t p u rd I) (univ\I) (bFoldOrder s (univ\I)) (pcRes s t p u rd I b') := by
    intro b'
    unfold pcBoundary
    exact bandSolveG_congr rd (NewtonRecip.recipMul rd 3 _ K) η' hrd' hmulR (machMul rd K)
      (NewtonRecip.recipNewton rd _ K) _ (pcSchur s t p u rd I) (univ\I) _ (2+εA) 3 s hμc
      (by norm_num) (by linarith) hinvSh (by exact_mod_cast hcardB) (bFoldOrder s _)
      (bFoldOrder_toFinset s _) hmS hmuS
      (fun a c ha hc hc3 => by
        simp only [machMul, NewtonRecip.recipMul, hβμ.trans hc, hc3, ha, and_self, ite_true])
      (fun c hc hc3 => by
        simp only [NewtonRecip.recipNewton, hβμ.trans hc, hc3, and_self, ite_true]) _
  -- The boundary values.
  have hr : ∀ i∈univ\I, |pcRes s t p u rd I b i-(b i-∑ j∈I, realMatrix s t p u i j*
      pcInterior s t p u rd I b j)|≤η := fun i _ => hrd _
  have hB := (rounded_inverse s t hst hα p u hp hwidth hαu hθ hgap hbudget I R hR rd _ _ η' θ eR
    hrd' hrd0 hmulR (NewtonRecip.recipMul_zero rd hrd0 3 _ K) hrecR heR0 s hcardB hsmS _ hRel
    (bFoldOrder s _) (bFoldPos s _) (bFoldPos_injective s _) (bFoldOrder_toFinset s _)
    (bFoldOrder_sorted s _) _ (pcSchur s t p u rd I) hY hSh hSh0 b x hx (1/2) hb e₁ η 0 0 he₁0 hη
    _ (pcRes s t p u rd I b) _ (R _) hy hr (fun i _ => by rw [sub_self, abs_zero])
    (fun j _ => by rw [sub_self, abs_zero])).1
  rw [←he₃, ←herrB] at hB
  rw [←hcong] at hB
  -- The recovery right-hand side is at most `C₅`.
  have hx4 : ∀ j, |x j|≤4*p := by
    intro j
    have h := solves_bound _ _ _ hμ hA0 x b (solves_of_mulVec s t p u x b hx) (1/2)
      (fun i _ => hb i) j (mem_univ j)
    rw [div_div_eq_mul_div, div_one] at h
    linarith
  have hxB : ∀ j∈univ\I, |pcBoundary s t p u rd K I b j|≤4*p+errB := fun j hj => by
    have := abs_add_le (pcBoundary s t p u rd K I b j-x j) (x j)
    rw [sub_add_cancel] at this
    linarith [hB j hj, hx4 j]
  have hc5 : ∀ i∈I, |pcRecov s t p u rd K I b i|≤C₅ := by
    intro i hi
    have hmassB : ∑ k∈univ\I, |realMatrix s t p u i k|≤1 :=
      (sum_le_sum_of_subset_of_nonneg (fun k hk => mem_erase.mpr
        ⟨fun h => (mem_sdiff.mp hk).2 (by rw [h]; exact hi), mem_univ k⟩)
        fun _ _ _ => abs_nonneg _).trans
        (offDiag_mass s t hst hα p u hp hwidth hαu hθ hgap hbudget i)
    have h1 := row_bound (realMatrix s t p u) (univ\I) (pcBoundary s t p u rd K I b) i 1 (4*p+errB)
      hmassB (by linarith) hxB
    have h2 := hrd (b i-couple (realMatrix s t p u) (univ\I) (pcBoundary s t p u rd K I b) i)
    have h3 := abs_sub (b i) (couple (realMatrix s t p u) (univ\I) (pcBoundary s t p u rd K I b) i)
    have h4 := abs_add_le (rd (b i-couple (realMatrix s t p u) (univ\I) (pcBoundary s t p u rd K I b) i)-
      (b i-couple (realMatrix s t p u) (univ\I) (pcBoundary s t p u rd K I b) i))
      (b i-couple (realMatrix s t p u) (univ\I) (pcBoundary s t p u rd K I b) i)
    rw [sub_add_cancel] at h4
    unfold pcRecov
    unfold couple at h1 h2 h3 h4 ⊢
    rw [hC₅]
    linarith [hb i]
  have hxI : ∀ j∈I, |pcInterior s t p u rd I (pcRecov s t p u rd K I b) j-
      R (pcRecov s t p u rd K I b) j|≤e₅ := fun j hj => by
    have := pcInterior_error s t p u hst hp0 hu hαu hθpos hgap hbudget I hI _ _ (hR _) rd η hrd
      hη1 hsη C₅ hC₅0 hc5 j hj
    rwa [←he₅] at this
  have hc : ∀ i∈I, |pcRecov s t p u rd K I b i-(b i-couple (realMatrix s t p u) (univ\I)
      (bandSolveG rd (NewtonRecip.recipMul rd 3 (1/(32*(p : ℝ))) K)
        (NewtonRecip.recipNewton rd (1/(32*(p : ℝ))) K) (pcSchur s t p u rd I) (univ\I)
        (bFoldOrder s (univ\I)) (pcRes s t p u rd I b)) i)|≤η := fun i _ => by
    rw [←hcong]; exact hrd _
  have hIb := (rounded_inverse s t hst hα p u hp hwidth hαu hθ hgap hbudget I R hR rd _ _ η' θ eR
    hrd' hrd0 hmulR (NewtonRecip.recipMul_zero rd hrd0 3 _ K) hrecR heR0 s hcardB hsmS _ hRel
    (bFoldOrder s _) (bFoldPos s _) (bFoldPos_injective s _) (bFoldOrder_toFinset s _)
    (bFoldOrder_sorted s _) _ (pcSchur s t p u rd I) hY hSh hSh0 b x hx (1/2) hb e₁ η η e₅ he₁0 hη
    _ (pcRes s t p u rd I b) (pcRecov s t p u rd K I b) _ hy hr hc hxI).2
  rw [←he₃, ←herrB] at hIb
  -- Assemble.
  have e : (2 : ℝ)^(8*p+46)*(p : ℝ)^7*(s : ℝ)^2*η=2^44*(p : ℝ)^7*2^(8*p+2)*(s : ℝ)^2*η := by ring
  rw [e]
  unfold pcSolve glue
  by_cases hj : j∈I
  · rw [ite_eq_left hj]
    have := hIb j hj
    linarith
  · rw [ite_eq_right hj]
    exact (hB j (mem_sdiff.mpr ⟨mem_univ j, hj⟩)).trans hBfin

end IntegerMultBounds.NLogN.PhaseCellMatrix
