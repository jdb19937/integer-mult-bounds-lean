module

public import IntegerMultBounds.NLogN.Approx
public import IntegerMultBounds.MathlibTM2.Mult.Sizes
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-! Precision of the concrete small-gap `B̃₀` at the existing sizes. With
working precision `3p`, normalization `j = ⌈log₂(4p)⌉` and the axis lengths
`s_i ≤ 2^ℓ`, `3ℓ ≤ p`, the conditions of `FastB0.concrete_resampB₀_spec`
hold and its error is at most `p²`. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.Sizes

/-- Rounding toward zero at `P` fractional bits. -/
noncomputable def rdP (P : ℕ) (x : ℝ) : ℝ := (NLogN.rho0 (2^P*x) : ℝ)/2^P

theorem rdP_err (P : ℕ) (x : ℝ) : |rdP P x-x|≤1/2^P := by
  have h := (NLogN.abs_rho0_sub_lt (2^P*x)).le
  have hP : (0 : ℝ)<2^P := by positivity
  unfold rdP
  rw [show (NLogN.rho0 (2^P*x) : ℝ)/2^P-x=((NLogN.rho0 (2^P*x) : ℝ)-2^P*x)/2^P by
    field_simp, abs_div, abs_of_pos hP]
  exact div_le_div_of_nonneg_right h hP.le

theorem rdP_zero (P : ℕ) : rdP P 0=0 := by
  simp [rdP, NLogN.rho0]

private theorem sq_le_two_pow (q : ℕ) (hq : 64≤q) : 2^16*q^2≤2^q := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
    have h2 : (q+1)^2≤2*q^2 := by nlinarith
    calc 2^16*(q+1)^2≤2^16*(2*q^2) := Nat.mul_le_mul_left _ h2
      _=2*(2^16*q^2) := by ring
      _≤2*2^q := Nat.mul_le_mul_left _ ih
      _=2^(q+1) := by rw [pow_succ]; ring

variable {n : ℕ}

theorem Big.s_le_two_pow (h : Big n) (i : Fin (d n)) : s n i≤2^ℓ n := by
  have hlt := h.good.lt i
  have ht : t n i≤2^ℓ n := by
    unfold t; split_ifs
    · exact Nat.pow_le_pow_right (by norm_num) (by omega)
    · exact le_rfl
  omega

theorem Big.three_ℓ_le_p (h : Big n) : 3*ℓ n≤p n := by
  have := h.ℓ_bounds.2
  have := h.one_le_d
  nlinarith

theorem Big.sixty_four_le_p (h : Big n) : 64≤p n := by
  have := h.sixteen_le_b; unfold p; omega

private theorem cube_le_two_pow (q : ℕ) (hq : 64≤q) : 2^20*q^3≤2^q := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
    have h2 : (q+1)^3≤2*q^3 := by
      have hq4 : 4≤q := by omega
      have hc : q^2*4≤q^2*q := Nat.mul_le_mul_left (q^2) hq4
      have hl : 3*q+1≤q^2 := by nlinarith
      have e : (q+1)^3=q^3+3*q^2+3*q+1 := by ring
      have e3 : q^3=q^2*q := by ring
      rw [e, e3]; linarith
    calc 2^20*(q+1)^3≤2^20*(2*q^3) := Nat.mul_le_mul_left _ h2
      _=2*(2^20*q^3) := by ring
      _≤2*2^q := Nat.mul_le_mul_left _ ih
      _=2^(q+1) := by rw [pow_succ]; ring

/-- The precision conditions and the final error of the machine-faithful
concrete `B̃₀` at working precision `3p`. -/
theorem Big.concreteB0M_conditions (h : Big n) (i : Fin (d n)) :
    2^16*(p n : ℝ)^2*(s n i : ℝ)^2*(1/2^(3*p n))≤1 ∧
    2*(62000*(p n : ℝ)^3*(s n i : ℝ)^2*(1/2^(3*p n)))+2/2^p n+
        (32*(p n : ℝ)^2/(2 : ℝ)^(45*p n))/2≤1/2 ∧
    6+2^p n*((2*(62000*(p n : ℝ)^3*(s n i : ℝ)^2*(1/2^(3*p n)))+2/2^p n)+
        (32*(p n : ℝ)^2/(2 : ℝ)^(45*p n))/2)≤(p n : ℝ)^2 := by
  set q := p n with hq
  have hq64 : 64≤q := h.sixty_four_le_p
  have hroom3 : (2 : ℝ)^20*(q : ℝ)^3≤2^q := by exact_mod_cast cube_le_two_pow q hq64
  have hP0 : (0 : ℝ)<2^q := by positivity
  set X : ℝ := 1/2^q with hX
  have hX0 : 0<X := by positivity
  have hX3 : (1 : ℝ)/2^(3*q)=X^3 := by rw [hX, one_div_pow, ←pow_mul, mul_comm]
  have hX45 : (1 : ℝ)/(2 : ℝ)^(45*q)≤X := by
    rw [hX]; exact one_div_le_one_div_of_le hP0 (pow_le_pow_right₀ (by norm_num) (by omega))
  have hq3X : (q : ℝ)^3*X≤1/2^20 := by
    rw [hX, mul_one_div, div_le_div_iff₀ hP0 (by positivity)]; linarith
  have hqR : (64 : ℝ)≤q := by exact_mod_cast hq64
  have hq23 : (q : ℝ)^2≤(q : ℝ)^3 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hq2X : (q : ℝ)^2*X≤1/2^20 := le_trans (mul_le_mul_of_nonneg_right hq23 hX0.le) hq3X
  have hX1 : X≤1 := by rw [hX]; exact div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) hP0.le
  have hs : (s n i : ℝ)^2*X≤1 := by
    have h1 : (s n i : ℝ)≤2^ℓ n := by exact_mod_cast h.s_le_two_pow i
    have h0 : (0 : ℝ)≤s n i := by positivity
    have h2 : ((2 : ℝ)^ℓ n)^2≤2^q := by
      rw [←pow_mul]; exact pow_le_pow_right₀ (by norm_num) (by have := h.three_ℓ_le_p; omega)
    have h3 : (s n i : ℝ)^2≤2^q := (pow_le_pow_left₀ h0 h1 2).trans h2
    rw [hX, mul_one_div, div_le_one hP0]; exact h3
  have hsX3 : (s n i : ℝ)^2*X^3≤X^2 := by
    have e : (s n i : ℝ)^2*X^3=((s n i : ℝ)^2*X)*X^2 := by ring
    rw [e]; exact mul_le_of_le_one_left (sq_nonneg X) hs
  rw [hX3]
  have hmul : (2 : ℝ)^q*X=1 := by rw [hX]; field_simp
  have hY : (2 : ℝ)^q*(1/(2 : ℝ)^(45*q))≤X := by
    have e : (2 : ℝ)^q*(1/(2 : ℝ)^(45*q))=1/2^(44*q) := by
      rw [show 45*q=q+44*q by ring, pow_add]; field_simp
    rw [e, hX]
    exact one_div_le_one_div_of_le hP0 (pow_le_pow_right₀ (by norm_num) (by omega))
  have hT : (q : ℝ)^3*(s n i : ℝ)^2*X^3≤(q : ℝ)^3*X*X := by
    have := mul_le_mul_of_nonneg_left hsX3 (by positivity : (0 : ℝ)≤(q : ℝ)^3)
    have e1 : (q : ℝ)^3*((s n i : ℝ)^2*X^3)=(q : ℝ)^3*(s n i : ℝ)^2*X^3 := by ring
    have e2 : (q : ℝ)^3*X^2=(q : ℝ)^3*X*X := by ring
    linarith
  have hT2 : (q : ℝ)^2*(s n i : ℝ)^2*X^3≤(q : ℝ)^2*X*X := by
    have := mul_le_mul_of_nonneg_left hsX3 (by positivity : (0 : ℝ)≤(q : ℝ)^2)
    have e1 : (q : ℝ)^2*((s n i : ℝ)^2*X^3)=(q : ℝ)^2*(s n i : ℝ)^2*X^3 := by ring
    have e2 : (q : ℝ)^2*X^2=(q : ℝ)^2*X*X := by ring
    linarith
  have hXX : (q : ℝ)^3*X*X≤(1/2^20)*X := mul_le_mul_of_nonneg_right hq3X hX0.le
  have hXX2 : (q : ℝ)^2*X*X≤(1/2^20)*X := mul_le_mul_of_nonneg_right hq2X hX0.le
  have hXs : X≤1/2^64 := by
    rw [hX]; exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hq64)
  have hD : 32*(q : ℝ)^2/(2 : ℝ)^(45*q)≤32*((q : ℝ)^2*X) := by
    rw [mul_div_assoc, div_eq_mul_one_div ((q : ℝ)^2)]
    have := mul_le_mul_of_nonneg_left hX45 (sq_nonneg (q : ℝ))
    linarith
  have h2q : (2 : ℝ)/2^q=2*X := by rw [hX]; ring
  refine ⟨?_, ?_, ?_⟩
  · have e : 2^16*(q : ℝ)^2*(s n i : ℝ)^2*X^3=2^16*((q : ℝ)^2*(s n i : ℝ)^2*X^3) := by ring
    rw [e]
    have : (1/2^20 : ℝ)*X≤1/2^20 := mul_le_of_le_one_right (by positivity) hX1
    have h16 : (2 : ℝ)^16*(1/2^20)≤1 := by norm_num
    nlinarith
  · rw [h2q]
    have e : 2*(62000*(q : ℝ)^3*(s n i : ℝ)^2*X^3)=124000*((q : ℝ)^3*(s n i : ℝ)^2*X^3) := by ring
    rw [e]
    have hq2X' : (q : ℝ)^2*X≤1/2^20 := hq2X
    have : (124000 : ℝ)*((1/2^20)*(1/2^64))+2*(1/2^64)+32*(1/2^20)/2≤1/2 := by norm_num
    nlinarith
  · rw [h2q]
    have e : (2 : ℝ)^q*((2*(62000*(q : ℝ)^3*(s n i : ℝ)^2*X^3)+2*X)+
        32*(q : ℝ)^2/(2 : ℝ)^(45*q)/2)=
        124000*((2 : ℝ)^q*((q : ℝ)^3*(s n i : ℝ)^2*X^3))+2*((2 : ℝ)^q*X)+
          (2 : ℝ)^q*(32*(q : ℝ)^2/(2 : ℝ)^(45*q))/2 := by ring
    rw [e, hmul]
    have hA1 : (2 : ℝ)^q*((q : ℝ)^3*(s n i : ℝ)^2*X^3)≤(q : ℝ)^3*X := by
      have := mul_le_mul_of_nonneg_left hT hP0.le
      have e2 : (2 : ℝ)^q*((q : ℝ)^3*X*X)=(q : ℝ)^3*X := by
        rw [show (2 : ℝ)^q*((q : ℝ)^3*X*X)=(q : ℝ)^3*X*((2 : ℝ)^q*X) by ring, hmul, mul_one]
      linarith
    have hA2 : (2 : ℝ)^q*(32*(q : ℝ)^2/(2 : ℝ)^(45*q))≤32*((q : ℝ)^2*X) := by
      have e : (2 : ℝ)^q*(32*(q : ℝ)^2/(2 : ℝ)^(45*q))=
          32*(q : ℝ)^2*((2 : ℝ)^q*(1/(2 : ℝ)^(45*q))) := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_left hY (by positivity : (0 : ℝ)≤32*(q : ℝ)^2)
      linarith
    have hq2 : (4096 : ℝ)≤(q : ℝ)^2 := by nlinarith
    have : (124000 : ℝ)*(1/2^20)+32*(1/2^20)/2≤1 := by norm_num
    nlinarith

/-- Newton iteration count for the pivot reciprocals at precision `5p`. -/
def newtonK (q : ℕ) : ℕ := 2*(Nat.log 2 q+1)+11

private theorem one_sub_pow_le (x : ℝ) (hx0 : 0≤x) (hx1 : x≤1) (m : ℕ) :
    (1-x)^m*(1+m*x)≤1 := by
  have hb := one_add_mul_le_pow (show (-2 : ℝ)≤x by linarith) m
  have h1 : (1-x)^m*(1+x)^m≤1 := by
    rw [← mul_pow]; exact pow_le_one₀ (by nlinarith) (by nlinarith)
  exact le_trans (mul_le_mul_of_nonneg_left hb (pow_nonneg (by linarith) _)) h1

/-- The Newton conditions at precision `5p` with floor `β = 1/(32p)` and
`newtonK p` iterations, and the effective rounding `η(1+180/β²) ≤ 2^-4p`. -/
theorem Big.newton_conditions (h : Big n) :
    let q := p n
    let η : ℝ := 1/2^(5*q)
    let β : ℝ := 1/(32*(q : ℝ))
    0<β ∧ β≤1/(8*(2*(q : ℝ)))/2 ∧ 5*η≤2*(β/4)/9 ∧ (1-β/4/2)^(2^newtonK q)≤3*(5*η)/(β/4) ∧
      η*(1+60*3/β^2)≤1/2^(4*q) := by
  intro q η β
  have hq64 : 64≤q := h.sixty_four_le_p
  have hqR : (64 : ℝ)≤q := by exact_mod_cast hq64
  have hroom3 : (2 : ℝ)^20*(q : ℝ)^3≤2^q := by exact_mod_cast cube_le_two_pow q hq64
  have hP0 : (0 : ℝ)<2^q := by positivity
  have hβ0 : 0<β := by positivity
  have e5 : (2 : ℝ)^(5*q)=2^q*2^(4*q) := by rw [← pow_add]; congr 1; ring
  have h4 : (0 : ℝ)<2^(4*q) := by positivity
  have h2 : (1 : ℝ)≤(q : ℝ)^2 := by nlinarith
  have hq3 : (q : ℝ)≤(q : ℝ)^3 := by
    have := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ)≤q by linarith)
    linarith [show (q : ℝ)*(q : ℝ)^2=(q : ℝ)^3 by ring]
  refine ⟨hβ0, le_of_eq (by simp only [β]; field_simp; ring), ?_, ?_, ?_⟩
  · simp only [η, β]
    rw [e5]
    have h1 : (1 : ℝ)≤2^(4*q) := one_le_pow₀ (by norm_num)
    have hl : 5*(1/(2^q*2^(4*q)))≤5/(2 : ℝ)^q := by
      rw [show 5*(1/((2 : ℝ)^q*2^(4*q)))=5/2^q/2^(4*q) by ring]
      exact div_le_self (by positivity) h1
    have hr : 2*(1/(32*(q : ℝ))/4)/9=1/(576*(q : ℝ)) := by field_simp; ring
    rw [hr]
    refine hl.trans ?_
    rw [div_le_div_iff₀ hP0 (by positivity)]
    nlinarith
  · -- `(1-x)^(256q) ≤ 1/2` with `x = 1/(256q)`, raised to the power `5q`
    have hx : β/4/2=1/(256*(q : ℝ)) := by simp only [β]; field_simp; ring
    rw [hx]
    set x : ℝ := 1/(256*(q : ℝ)) with hxdef
    have hx0 : 0≤x := by positivity
    have hx1 : x≤1 := by rw [hxdef, div_le_one (by positivity)]; linarith
    have hhalf : (1-x)^(256*q)≤1/2 := by
      have := one_sub_pow_le x hx0 hx1 (256*q)
      have e : (1 : ℝ)+((256*q : ℕ) : ℝ)*x=2 := by
        rw [hxdef]; push_cast; field_simp; ring
      rw [e] at this; linarith
    have hpow : 256*q*(5*q)≤2^newtonK q := by
      have hs := Nat.lt_pow_succ_log_self (by norm_num : 1<2) q
      have : q*q<2^(Nat.log 2 q+1)*2^(Nat.log 2 q+1) := Nat.mul_lt_mul'' hs hs
      have e : 2^newtonK q=2^(Nat.log 2 q+1)*2^(Nat.log 2 q+1)*2048 := by
        simp only [newtonK]; rw [pow_add, two_mul, pow_add]; norm_num
      rw [e]
      calc 256*q*(5*q)=1280*(q*q) := by ring
        _≤2048*(q*q) := Nat.mul_le_mul_right _ (by norm_num)
        _≤2048*(2^(Nat.log 2 q+1)*2^(Nat.log 2 q+1)) := Nat.mul_le_mul_left _ this.le
        _=_ := by ring
    have hmono : (1-x)^(2^newtonK q)≤(1-x)^(256*q*(5*q)) :=
      pow_le_pow_of_le_one (by linarith) (by linarith) hpow
    have h2' : (1-x)^(256*q*(5*q))≤(1/2)^(5*q) := by
      rw [pow_mul]; exact pow_le_pow_left₀ (pow_nonneg (by linarith) _) hhalf _
    refine hmono.trans (h2'.trans ?_)
    simp only [η, β]
    rw [one_div_pow]
    have e : (3 : ℝ)*(5*(1/2^(5*q)))/(1/(32*(q : ℝ))/4)=1920*(q : ℝ)/2^(5*q) := by
      field_simp; ring
    rw [e, div_le_div_iff_of_pos_right (by positivity)]
    linarith
  · simp only [η, β]
    have e : (1 : ℝ)/2^(5*q)*(1+60*3/(1/(32*(q : ℝ)))^2)=(1+184320*(q : ℝ)^2)/2^q*(1/2^(4*q)) := by
      rw [e5]; field_simp; ring
    rw [e]
    have hc : (1+184320*(q : ℝ)^2)/2^q≤1 := by
      rw [div_le_one hP0]; nlinarith
    calc _≤1*(1/2^(4*q)) := mul_le_mul_of_nonneg_right hc (by positivity)
      _=_ := one_mul _

section PCore
variable (q S X Y Z η' ε : ℝ) (hq : 64≤q) (hX0 : 0<X) (hXs : X≤1/2^64) (hq3X : q^3*X≤1/2^20)
  (hs : S^2*X≤1) (hη0 : 0≤η') (hη : η'≤X^4) (hε0 : 0≤ε) (hε : ε≤X^3) (hYX : Y*X=1)
  (hZ : Z≤X) (hYZ : Y*Z≤X)

include hq hX0 hq3X in
private theorem pcore_q2X : q^2*X≤1/2^20 := by
  have hq23 : q^2≤q^3 := by nlinarith
  exact (mul_le_mul_of_nonneg_right hq23 hX0.le).trans hq3X

include hq hX0 hq3X hs hη hε in
private theorem pcore_T : 62000*(2*q)^3*S^2*η'+64*q^2*ε≤X^2/2 := by
  have hq23 : q^2≤q^3 := by nlinarith
  have hsη : S^2*η'≤X^3 := by
    calc S^2*η'≤S^2*X^4 := mul_le_mul_of_nonneg_left hη (sq_nonneg S)
      _=(S^2*X)*X^3 := by ring
      _≤1*X^3 := mul_le_mul_of_nonneg_right hs (by positivity)
      _=X^3 := one_mul _
  have e : 62000*(2*q)^3*S^2*η'=496000*(q^3*(S^2*η')) := by ring
  have h1 := mul_le_mul_of_nonneg_left hsη (show (0 : ℝ)≤q^3 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hε (show (0 : ℝ)≤q^2 by positivity)
  have h3 := mul_le_mul_of_nonneg_right hq23 (show (0 : ℝ)≤X^3 by positivity)
  have hqX3 : q^3*X^3≤(1/2^20)*X^2 := by
    have e : q^3*X^3=(q^3*X)*X^2 := by ring
    rw [e]; exact mul_le_mul_of_nonneg_right hq3X (by positivity)
  rw [e]; linarith [h1, h2, h3, hqX3, sq_nonneg X]

include hq hX0 hXs hq3X hε in
private theorem pcore_1 : ε≤1/(32*q) := by
  refine hε.trans ?_
  rw [le_div_iff₀ (by positivity)]
  have h1 : q*X≤1/2^20 := by
    have hq2 : 1≤q^2 := by nlinarith
    have hq1 : q≤q^3 := by
      have := mul_le_mul_of_nonneg_left hq2 (show (0 : ℝ)≤q by linarith)
      linarith [show q*q^2=q^3 by ring]
    have := mul_le_mul_of_nonneg_right hq1 hX0.le
    linarith
  have hX1 : X≤1 := hXs.trans (by norm_num)
  have hX2 : X^2≤1 := by nlinarith
  have h3 : X^3*(32*q)=32*(X^2*(q*X)) := by ring
  have h4 : X^2*(q*X)≤1*(1/2^20) := mul_le_mul hX2 h1 (by positivity) (by norm_num)
  linarith

include hq hX0 hXs hq3X hs hη in
private theorem pcore_2 : 2^16*(2*q)^2*S^2*η'≤1 := by
  have hsη : S^2*η'≤X^3 := by
    calc S^2*η'≤S^2*X^4 := mul_le_mul_of_nonneg_left hη (sq_nonneg S)
      _=(S^2*X)*X^3 := by ring
      _≤1*X^3 := mul_le_mul_of_nonneg_right hs (by positivity)
      _=X^3 := one_mul _
  have hq2X := pcore_q2X q X hq hX0 hq3X
  have e : 2^16*(2*q)^2*S^2*η'=2^18*(q^2*(S^2*η')) := by ring
  rw [e]
  have h1 := mul_le_mul_of_nonneg_left hsη (show (0 : ℝ)≤q^2 by positivity)
  have h2 : q^2*X^3≤(1/2^20)*X^2 := by
    have e2 : q^2*X^3=(q^2*X)*X^2 := by ring
    rw [e2]; exact mul_le_mul_of_nonneg_right hq2X (by positivity)
  have hX1 : X≤1 := hXs.trans (by norm_num)
  have h3 : X^2≤1 := by nlinarith
  have h4 := mul_le_mul_of_nonneg_left (h1.trans h2) (show (0 : ℝ)≤2^18 by norm_num)
  linarith

include hq hX0 hXs hq3X hs hη hε hZ in
private theorem pcore_3 : 2*(62000*(2*q)^3*S^2*η'+64*q^2*ε)+2*X+32*q^2*Z/2≤1/2 := by
  have hT := pcore_T q S X η' ε hq hX0 hq3X hs hη hε
  have hq2X := pcore_q2X q X hq hX0 hq3X
  have hX1 : X≤1 := hXs.trans (by norm_num)
  have hX2 : X^2≤X := by nlinarith
  have hD : q^2*Z≤q^2*X := mul_le_mul_of_nonneg_left hZ (sq_nonneg q)
  linarith

include hq hX0 hXs hq3X hs hη hε hYX hYZ in
private theorem pcore_4 : 6+Y*((2*(62000*(2*q)^3*S^2*η'+64*q^2*ε)+2*X)+32*q^2*Z/2)≤q^2 := by
  have hT := pcore_T q S X η' ε hq hX0 hq3X hs hη hε
  have hq2X := pcore_q2X q X hq hX0 hq3X
  have hY0 : 0≤Y := by
    by_contra hneg; push Not at hneg; nlinarith
  have e : Y*((2*(62000*(2*q)^3*S^2*η'+64*q^2*ε)+2*X)+32*q^2*Z/2)=
      2*(Y*(62000*(2*q)^3*S^2*η'+64*q^2*ε))+2*(Y*X)+16*q^2*(Y*Z) := by ring
  rw [e, hYX]
  have hA1 : Y*(62000*(2*q)^3*S^2*η'+64*q^2*ε)≤X/2 := by
    have h1 := mul_le_mul_of_nonneg_left hT hY0
    have e2 : Y*(X^2/2)=X/2*(Y*X) := by ring
    rw [e2, hYX] at h1; linarith
  have hA2 : q^2*(Y*Z)≤q^2*X := mul_le_mul_of_nonneg_left hYZ (sq_nonneg q)
  have hq2' : (4096 : ℝ)≤q^2 := by nlinarith
  have hX1 : X≤1 := hXs.trans (by norm_num)
  linarith

end PCore

/-- The conditions of `FastB0.concrete_resampB₀_specP` at precision `5p` for a
matrix perturbation `ε ≤ 2^-3p`, with final error at most `p²`. -/
theorem Big.concreteB0P_conditions (h : Big n) (i : Fin (d n)) (ε : ℝ) (_hε0 : 0≤ε)
    (hε : ε≤1/2^(3*p n)) :
    ε≤1/(32*(p n : ℝ)) ∧
    2^16*(2*(p n : ℝ))^2*(s n i : ℝ)^2*(1/2^(5*p n)*(1+60*3/(1/(32*(p n : ℝ)))^2))≤1 ∧
    2*(62000*(2*(p n : ℝ))^3*(s n i : ℝ)^2*(1/2^(5*p n)*(1+60*3/(1/(32*(p n : ℝ)))^2))+
        64*(p n : ℝ)^2*ε)+2/2^p n+(32*(p n : ℝ)^2/(2 : ℝ)^(45*p n))/2≤1/2 ∧
    6+2^p n*((2*(62000*(2*(p n : ℝ))^3*(s n i : ℝ)^2*(1/2^(5*p n)*(1+60*3/(1/(32*(p n : ℝ)))^2))+
        64*(p n : ℝ)^2*ε)+2/2^p n)+(32*(p n : ℝ)^2/(2 : ℝ)^(45*p n))/2)≤(p n : ℝ)^2 := by
  obtain ⟨-, -, -, -, hη⟩ := h.newton_conditions
  set q := p n with hq
  set η' : ℝ := 1/2^(5*q)*(1+60*3/(1/(32*(q : ℝ)))^2) with hη'
  have hq64 : 64≤q := h.sixty_four_le_p
  have hqR : (64 : ℝ)≤q := by exact_mod_cast hq64
  have hroom3 : (2 : ℝ)^20*(q : ℝ)^3≤2^q := by exact_mod_cast cube_le_two_pow q hq64
  have hP0 : (0 : ℝ)<2^q := by positivity
  set X : ℝ := 1/2^q with hX
  have hX0 : 0<X := by positivity
  have hmul : (2 : ℝ)^q*X=1 := by rw [hX]; field_simp
  have hX3 : (1 : ℝ)/2^(3*q)=X^3 := by rw [hX, one_div_pow, ←pow_mul, mul_comm]
  have hX4 : (1 : ℝ)/2^(4*q)=X^4 := by rw [hX, one_div_pow, ←pow_mul, mul_comm]
  rw [hX4] at hη
  rw [hX3] at hε
  have hη0 : 0≤η' := by positivity
  have hq3X : (q : ℝ)^3*X≤1/2^20 := by
    rw [hX, mul_one_div, div_le_div_iff₀ hP0 (by positivity)]; linarith
  have hXs : X≤1/2^64 := by
    rw [hX]; exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hq64)
  have hs : (s n i : ℝ)^2*X≤1 := by
    have h1 : (s n i : ℝ)≤2^ℓ n := by exact_mod_cast h.s_le_two_pow i
    have h0 : (0 : ℝ)≤s n i := by positivity
    have h2 : ((2 : ℝ)^ℓ n)^2≤2^q := by
      rw [←pow_mul]; exact pow_le_pow_right₀ (by norm_num) (by have := h.three_ℓ_le_p; omega)
    have h3 : (s n i : ℝ)^2≤2^q := (pow_le_pow_left₀ h0 h1 2).trans h2
    rw [hX, mul_one_div, div_le_one hP0]; exact h3
  have hY : (2 : ℝ)^q*(1/(2 : ℝ)^(45*q))≤X := by
    have e : (2 : ℝ)^q*(1/(2 : ℝ)^(45*q))=1/2^(44*q) := by
      rw [show 45*q=q+44*q by ring, pow_add]; field_simp
    rw [e, hX]
    exact one_div_le_one_div_of_le hP0 (pow_le_pow_right₀ (by norm_num) (by omega))
  have hX45 : (1 : ℝ)/(2 : ℝ)^(45*q)≤X := by
    rw [hX]; exact one_div_le_one_div_of_le hP0 (pow_le_pow_right₀ (by norm_num) (by omega))
  have h2q : (2 : ℝ)/2^q=2*X := by rw [hX]; ring
  have eD : 32*(q : ℝ)^2/(2 : ℝ)^(45*q)/2=32*(q : ℝ)^2*(1/(2 : ℝ)^(45*q))/2 := by ring
  rw [h2q, eD]
  exact ⟨pcore_1 q X ε hqR hX0 hXs hq3X hε,
    pcore_2 q (s n i) X η' hqR hX0 hXs hq3X hs hη,
    pcore_3 q (s n i) X _ η' ε hqR hX0 hXs hq3X hs hη hε hX45,
    pcore_4 q (s n i) X _ _ η' ε hqR hX0 hXs hq3X hs hη hε hmul hY⟩

/-- The window-matrix perturbation at entry precision `5q`: with `2w+1 ≤ 2^q`
and `q ≥ 2`, `(2w+1)·2/2^(5q) + 2^-46q + 2^-45q ≤ 2^-3q`. -/
theorem window_eps_le (q w : ℕ) (hq : 2≤q) (hw : (2*w+1 : ℝ)≤2^q) :
    (2*w+1 : ℝ)*(2/2^(5*q))+1/(2 : ℝ)^(46*q)+1/(2 : ℝ)^(45*q)≤1/2^(3*q) := by
  have hP0 : (0 : ℝ)<2^q := by positivity
  set X : ℝ := 1/2^q with hX
  have hX0 : 0<X := by positivity
  have hpow : ∀ k, (1 : ℝ)/2^(k*q)=X^k := fun k => by rw [hX, one_div_pow, ← pow_mul, mul_comm]
  have hX4 : X≤1/4 := by
    rw [hX]; exact one_div_le_one_div_of_le (by norm_num)
      (by calc (4 : ℝ)=2^2 := by norm_num
            _≤2^q := pow_le_pow_right₀ (by norm_num) hq)
  have e5 : (2 : ℝ)/2^(5*q)=2*X^5 := by rw [← hpow 5]; ring
  rw [e5, hpow 46, hpow 45, hpow 3]
  have hwX : (2*w+1 : ℝ)*X≤1 := by
    rw [hX, mul_one_div, div_le_one hP0]; exact hw
  have h1 : (2*w+1 : ℝ)*(2*X^5)=2*X^4*((2*w+1 : ℝ)*X) := by ring
  have h2 : (2*w+1 : ℝ)*(2*X^5)≤2*X^4 := by
    rw [h1]; exact mul_le_of_le_one_right (by positivity) hwX
  have h3 : X^46≤X^45 := pow_le_pow_of_le_one hX0.le (by linarith) (by norm_num)
  have h4 : X^45≤X^4 := pow_le_pow_of_le_one hX0.le (by linarith) (by norm_num)
  have h5 : X^4=X*X^3 := by ring
  have h6 : X*X^3≤(1/4)*X^3 := mul_le_mul_of_nonneg_right hX4 (by positivity)
  nlinarith

end IntegerMultBounds.MathlibTM2.Mult.Sizes
