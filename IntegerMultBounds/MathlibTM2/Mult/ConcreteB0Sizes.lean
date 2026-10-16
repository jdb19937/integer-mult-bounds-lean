module

public import IntegerMultBounds.MathlibTM2.Mult.SmallGapSizes
public import IntegerMultBounds.NLogN.Approx

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

/-- The normalization exponent `j = ⌈log₂(4p)⌉`. -/
def jSG (n : ℕ) : ℕ := Nat.clog 2 (4*p n)

theorem four_p_le_two_pow_jSG (n : ℕ) : 4*(p n : ℝ)≤2^jSG n := by
  have := Nat.le_pow_clog one_lt_two (4*p n)
  exact_mod_cast this

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

/-- The precision conditions and the final error of the concrete `B̃₀`. -/
theorem Big.concreteB0_conditions (h : Big n) (i : Fin (d n)) :
    128*(p n : ℝ)*(s n i : ℝ)^2*(1/2^(3*p n))≤1 ∧
    2*(2700*(s n i : ℝ)^2*(p n : ℝ)^2*(1/2^(3*p n)))+2/2^p n+
        (32*(p n : ℝ)^2/(2 : ℝ)^(45*p n))/2≤1/2 ∧
    6+2^p n*((2*(2700*(s n i : ℝ)^2*(p n : ℝ)^2*(1/2^(3*p n)))+2/2^p n)+
        (32*(p n : ℝ)^2/(2 : ℝ)^(45*p n))/2)≤(p n : ℝ)^2 := by
  set q := p n with hq
  have hq64 : 64≤q := h.sixty_four_le_p
  have hroom : (2 : ℝ)^16*(q : ℝ)^2≤2^q := by exact_mod_cast sq_le_two_pow q hq64
  have hP0 : (0 : ℝ)<2^q := by positivity
  set X : ℝ := 1/2^q with hX
  have hX0 : 0<X := by positivity
  have hX3 : (1 : ℝ)/2^(3*q)=X^3 := by rw [hX, one_div_pow, ←pow_mul, mul_comm]
  have hX45 : (1 : ℝ)/(2 : ℝ)^(45*q)≤X := by
    rw [hX]; exact one_div_le_one_div_of_le hP0 (pow_le_pow_right₀ (by norm_num) (by omega))
  have hqX : (q : ℝ)^2*X≤1/2^16 := by
    rw [hX, mul_one_div, div_le_div_iff₀ hP0 (by positivity)]; linarith
  have hqR : (64 : ℝ)≤q := by exact_mod_cast hq64
  have hqq : (q : ℝ)≤(q : ℝ)^2 := by nlinarith
  have hXs : X≤1/2^16 := by
    have : X*(q : ℝ)^2≤1/2^16 := by linarith
    nlinarith
  have hs : (s n i : ℝ)^2*X≤1 := by
    have h1 : (s n i : ℝ)≤2^ℓ n := by exact_mod_cast h.s_le_two_pow i
    have h0 : (0 : ℝ)≤s n i := by positivity
    have h2 : ((2 : ℝ)^ℓ n)^2≤2^q := by
      rw [←pow_mul]; exact pow_le_pow_right₀ (by norm_num) (by have := h.three_ℓ_le_p; omega)
    have h3 : (s n i : ℝ)^2≤2^q := (pow_le_pow_left₀ h0 h1 2).trans h2
    rw [hX, mul_one_div, div_le_one hP0]; exact h3
  have hS0 : (0 : ℝ)≤(s n i : ℝ)^2 := sq_nonneg _
  -- `s² X³ ≤ X²`
  have hsX3 : (s n i : ℝ)^2*X^3≤X^2 := by
    have : (s n i : ℝ)^2*X^3=((s n i : ℝ)^2*X)*X^2 := by ring
    rw [this]; nlinarith [sq_nonneg X]
  rw [hX3]
  have hD : 32*(q : ℝ)^2/(2 : ℝ)^(45*q)≤32*((q : ℝ)^2*X) := by
    rw [mul_div_assoc, div_eq_mul_one_div ((q : ℝ)^2)]
    have := mul_le_mul_of_nonneg_left hX45 (sq_nonneg (q : ℝ))
    linarith
  have hT1 : (q : ℝ)*(s n i : ℝ)^2*X^3≤(q : ℝ)^2*X*X := by
    have := mul_le_mul_of_nonneg_left hsX3 (by positivity : (0 : ℝ)≤q)
    have : (q : ℝ)*X^2≤(q : ℝ)^2*X*X := by nlinarith
    nlinarith
  have hT2 : (s n i : ℝ)^2*(q : ℝ)^2*X^3≤(q : ℝ)^2*X*X := by
    have := mul_le_mul_of_nonneg_left hsX3 (sq_nonneg (q : ℝ))
    nlinarith
  have h2q : (2 : ℝ)/2^q=2*X := by rw [hX]; ring
  have hmul : (2 : ℝ)^q*X=1 := by rw [hX]; field_simp
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · rw [h2q]; nlinarith
  · rw [h2q]
    have e : (2 : ℝ)^q*((2*(2700*(s n i : ℝ)^2*(q : ℝ)^2*X^3)+2*X)+32*(q : ℝ)^2/(2 : ℝ)^(45*q)/2)=
        5400*((2 : ℝ)^q*((s n i : ℝ)^2*(q : ℝ)^2*X^3))+2*((2 : ℝ)^q*X)+
          (2 : ℝ)^q*(32*(q : ℝ)^2/(2 : ℝ)^(45*q))/2 := by ring
    rw [e, hmul]
    have hA1 : (2 : ℝ)^q*((s n i : ℝ)^2*(q : ℝ)^2*X^3)≤(q : ℝ)^2*X := by
      have := mul_le_mul_of_nonneg_left hT2 hP0.le
      have e2 : (2 : ℝ)^q*((q : ℝ)^2*X*X)=(q : ℝ)^2*X := by
        rw [show (2 : ℝ)^q*((q : ℝ)^2*X*X)=(q : ℝ)^2*X*((2 : ℝ)^q*X) by ring, hmul, mul_one]
      linarith
    have hY : (2 : ℝ)^q*(1/(2 : ℝ)^(45*q))≤X := by
      have e : (2 : ℝ)^q*(1/(2 : ℝ)^(45*q))=1/2^(44*q) := by
        rw [show 45*q=q+44*q by ring, pow_add]; field_simp
      rw [e, hX]
      exact one_div_le_one_div_of_le hP0 (pow_le_pow_right₀ (by norm_num) (by omega))
    have hA2 : (2 : ℝ)^q*(32*(q : ℝ)^2/(2 : ℝ)^(45*q))≤32*((q : ℝ)^2*X) := by
      have e : (2 : ℝ)^q*(32*(q : ℝ)^2/(2 : ℝ)^(45*q))=32*(q : ℝ)^2*((2 : ℝ)^q*(1/(2 : ℝ)^(45*q))) := by
        ring
      rw [e]
      have := mul_le_mul_of_nonneg_left hY (by positivity : (0 : ℝ)≤32*(q : ℝ)^2)
      linarith
    have hq2 : (4096 : ℝ)≤(q : ℝ)^2 := by nlinarith
    nlinarith

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

end IntegerMultBounds.MathlibTM2.Mult.Sizes
