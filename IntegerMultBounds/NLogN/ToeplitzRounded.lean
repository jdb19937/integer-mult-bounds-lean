module

public import IntegerMultBounds.NLogN.ToeplitzApply

/-! Rounded Gohberg–Semencul application. With coefficient masses at most two,
corner `x₀ ≥ 1/2`, rounded factors and reciprocal within `η`, and each of the
five computed stages rounded within `η`, the computed inverse application is
within `64 L η V` of the exact one for inputs bounded by `V ≥ 1`, when
`L η ≤ 1`. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.ToeplitzInverse

open scoped BigOperators
open Finset

theorem upper_sub_coeff (L : ℕ) (x x' v : ℕ → ℝ) (i : ℕ) :
    upper L x v i-upper L x' v i=upper L (x-x') v i := by
  simp only [upper, Pi.sub_apply, sub_mul, sum_sub_distrib]

theorem upper_sub_vec (L : ℕ) (x v v' : ℕ → ℝ) (i : ℕ) :
    upper L x v i-upper L x v' i=upper L x (v-v') i := by
  simp only [upper, Pi.sub_apply, mul_sub, sum_sub_distrib]

theorem lower_sub_coeff (x x' v : ℕ → ℝ) (i : ℕ) :
    lower x v i-lower x' v i=lower (x-x') v i := by
  simp only [lower, Pi.sub_apply, sub_mul, sum_sub_distrib]

theorem lower_sub_vec (x v v' : ℕ → ℝ) (i : ℕ) :
    lower x v i-lower x v' i=lower x (v-v') i := by
  simp only [lower, Pi.sub_apply, mul_sub, sum_sub_distrib]

theorem upper_bound (L : ℕ) (x v : ℕ → ℝ) (X V : ℝ) (hV : 0≤V)
    (hx : ∑ k∈range L, |x k|≤X) (hv : ∀ j∈range L, |v j|≤V) (i : ℕ) :
    |upper L x v i|≤X*V := by
  unfold upper
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j∈Ico i L, |x (j-i)*v j|≤∑ j∈Ico i L, |x (j-i)| * V := sum_le_sum fun j hj => by
        rw [abs_mul]
        have := mem_Ico.mp hj
        exact mul_le_mul_of_nonneg_left (hv j (mem_range.mpr this.2)) (abs_nonneg _)
    _=(∑ k∈range (L-i), |x k|) * V := by
        rw [←sum_mul, sum_Ico_eq_sum_range]
        simp
    _≤X*V := by
        refine mul_le_mul_of_nonneg_right ((sum_le_sum_of_subset_of_nonneg ?_
          fun _ _ _ => abs_nonneg _).trans hx) hV
        exact range_subset_range.mpr (Nat.sub_le L i)

theorem lower_bound (L : ℕ) (x v : ℕ → ℝ) (X V : ℝ) (hV : 0≤V)
    (hx : ∑ k∈range L, |x k|≤X) (hv : ∀ j∈range L, |v j|≤V) (i : ℕ) (hi : i<L) :
    |lower x v i|≤X*V := by
  unfold lower
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k∈range (i+1), |x (i-k)*v k|≤∑ k∈range (i+1), |x (i-k)| * V :=
        sum_le_sum fun k hk => by
          rw [abs_mul]
          have := mem_range.mp hk
          exact mul_le_mul_of_nonneg_left (hv k (mem_range.mpr (by omega))) (abs_nonneg _)
    _=(∑ k∈range (i+1), |x k|) * V := by
        rw [←sum_mul, ←sum_range_reflect (fun k => |x k|)]
        congr 1
    _≤X*V := by
        refine mul_le_mul_of_nonneg_right ((sum_le_sum_of_subset_of_nonneg ?_
          fun _ _ _ => abs_nonneg _).trans hx) hV
        exact range_subset_range.mpr (by omega)

/-- One rounded lower/upper branch `L(x̂)(round L(x̂)ᵀ v)`. -/
theorem branch_error (L : ℕ) (x xh v u₁ u₂ : ℕ → ℝ) (η V : ℝ) (hη : 0≤η) (hV : 1≤V)
    (hLη : L*η≤1) (hx : ∑ k∈range L, |x k|≤2) (hxh : ∀ k∈range L, |xh k-x k|≤η)
    (hv : ∀ j∈range L, |v j|≤V)
    (hu₁ : ∀ j∈range L, |u₁ j-upper L xh v j|≤η)
    (hu₂ : ∀ i∈range L, |u₂ i-lower xh u₁ i|≤η) (i : ℕ) (hi : i<L) :
    |u₂ i-lower x (upper L x v) i|≤9*L*η*V := by
  have hV0 : 0≤V := by linarith
  have hL : (1 : ℝ)≤L := by exact_mod_cast (show 1≤L by omega)
  have hdm : ∑ k∈range L, |(xh-x) k|≤L*η := by
    calc _≤∑ k∈range L, η := sum_le_sum fun k hk => hxh k hk
      _=L*η := by simp
  have hLV : (1 : ℝ)≤L*V := by nlinarith
  have hηV : η≤L*η*V := by nlinarith [mul_le_mul_of_nonneg_left hLV hη]
  -- First stage: `u₁` is within `2LηV` of the exact upper product.
  have he₁ : ∀ j∈range L, |u₁ j-upper L x v j|≤2*L*η*V := by
    intro j hj
    have hc := upper_bound L (xh-x) v (L*η) V hV0 hdm hv j
    rw [←upper_sub_coeff] at hc
    calc |u₁ j-upper L x v j|=|(u₁ j-upper L xh v j)+(upper L xh v j-upper L x v j)| := by
          ring_nf
      _≤η+L*η*V := (abs_add_le _ _).trans (add_le_add (hu₁ j hj) hc)
      _≤2*L*η*V := by linarith
  have hb₁ : ∀ j∈range L, |u₁ j|≤4*V := by
    intro j hj
    have h0 := upper_bound L x v 2 V hV0 hx hv j
    have h1 := he₁ j hj
    have : |u₁ j|≤|u₁ j-upper L x v j|+|upper L x v j| := by
      simpa using abs_add_le (u₁ j-upper L x v j) (upper L x v j)
    nlinarith
  have hc₂ := lower_bound L (xh-x) u₁ (L*η) (4*V) (by linarith) hdm hb₁ i hi
  rw [←lower_sub_coeff] at hc₂
  have hd₂ := lower_bound L x (u₁-upper L x v) 2 (2*L*η*V) (by positivity) hx
    (fun j hj => by simpa only [Pi.sub_apply] using he₁ j hj) i hi
  rw [←lower_sub_vec] at hd₂
  have h₂ := hu₂ i (mem_range.mpr hi)
  calc |u₂ i-lower x (upper L x v) i|
      =|(u₂ i-lower xh u₁ i)+(lower xh u₁ i-lower x u₁ i)+
          (lower x u₁ i-lower x (upper L x v) i)| := by ring_nf
    _≤|u₂ i-lower xh u₁ i|+|lower xh u₁ i-lower x u₁ i|+
          |lower x u₁ i-lower x (upper L x v) i| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _) |>.trans_eq (by ring)
    _≤η+L*η*(4*V)+2*(2*L*η*V) := add_le_add (add_le_add h₂ hc₂) hd₂
    _≤9*L*η*V := by linarith

/-- Rounded Gohberg–Semencul application. `T` is the exact inverse
application, given through `x₀ T = L(x)L(x)ᵀv - L(z)L(z)ᵀv`. -/
theorem rounded_apply (L : ℕ) (x z xh zh v u₁ u₂ u₃ u₄ out T : ℕ → ℝ) (x₀ w η V : ℝ)
    (hη : 0≤η) (hV : 1≤V) (hLη : L*η≤1) (hx₀ : 1/2≤x₀)
    (hx : ∑ k∈range L, |x k|≤2) (hz : ∑ k∈range L, |z k|≤2)
    (hxh : ∀ k∈range L, |xh k-x k|≤η) (hzh : ∀ k∈range L, |zh k-z k|≤η)
    (hw : |w-1/x₀|≤η) (hv : ∀ j∈range L, |v j|≤V)
    (hu₁ : ∀ j∈range L, |u₁ j-upper L xh v j|≤η)
    (hu₂ : ∀ i∈range L, |u₂ i-lower xh u₁ i|≤η)
    (hu₃ : ∀ j∈range L, |u₃ j-upper L zh v j|≤η)
    (hu₄ : ∀ i∈range L, |u₄ i-lower zh u₃ i|≤η)
    (hout : ∀ i∈range L, |out i-w*(u₂ i-u₄ i)|≤η)
    (hT : ∀ i∈range L, x₀*T i=lower x (upper L x v) i-lower z (upper L z v) i)
    (i : ℕ) (hi : i<L) : |out i-T i|≤64*L*η*V := by
  have hV0 : 0≤V := by linarith
  have hL : (1 : ℝ)≤L := by exact_mod_cast (show 1≤L by omega)
  have hLV : (1 : ℝ)≤L*V := by nlinarith
  have hηV : η≤L*η*V := by nlinarith [mul_le_mul_of_nonneg_left hLV hη]
  have hbx := branch_error L x xh v u₁ u₂ η V hη hV hLη hx hxh hv hu₁ hu₂ i hi
  have hbz := branch_error L z zh v u₃ u₄ η V hη hV hLη hz hzh hv hu₃ hu₄ i hi
  have hux := lower_bound L x (upper L x v) 2 (2*V) (by linarith) hx
    (fun j _ => upper_bound L x v 2 V hV0 hx hv j) i hi
  have huz := lower_bound L z (upper L z v) 2 (2*V) (by linarith) hz
    (fun j _ => upper_bound L z v 2 V hV0 hz hv j) i hi
  set D := lower x (upper L x v) i-lower z (upper L z v) i with hDdef
  have hD : |D|≤8*V := by
    have := abs_sub (lower x (upper L x v) i) (lower z (upper L z v) i)
    linarith
  have hx₀pos : 0<x₀ := by linarith
  have hTi : T i=D/x₀ := by
    rw [eq_div_iff hx₀pos.ne', mul_comm]
    exact hT i (mem_range.mpr hi)
  have hdiff : |(u₂ i-u₄ i)-D|≤18*L*η*V := by
    have := abs_sub (u₂ i-lower x (upper L x v) i) (u₄ i-lower z (upper L z v) i)
    calc |(u₂ i-u₄ i)-D|=|(u₂ i-lower x (upper L x v) i)-(u₄ i-lower z (upper L z v) i)| := by
          congr 1
          rw [hDdef]
          ring
      _≤_ := this
      _≤_ := by linarith
  have hinv : 1/x₀≤2 := by
    rw [div_le_iff₀ hx₀pos]
    linarith
  have hη1 : η≤1 := by nlinarith
  have hwb : |w|≤3 := by
    have := abs_add_le (w-1/x₀) (1/x₀)
    rw [sub_add_cancel, abs_of_pos (by positivity : 0<1/x₀)] at this
    linarith
  have hDx : D/x₀=1/x₀*D := by ring
  rw [hTi, hDx]
  have h1 := hout i (mem_range.mpr hi)
  have h2 : |w*((u₂ i-u₄ i)-D)|≤3*(18*L*η*V) := by
    rw [abs_mul]
    exact mul_le_mul hwb hdiff (abs_nonneg _) (by norm_num)
  have h3 : |(w-1/x₀)*D|≤η*(8*V) := by
    rw [abs_mul]
    exact mul_le_mul hw hD (abs_nonneg _) hη
  calc |out i-1/x₀*D|=|(out i-w*(u₂ i-u₄ i))+w*((u₂ i-u₄ i)-D)+(w-1/x₀)*D| := by ring_nf
    _≤|out i-w*(u₂ i-u₄ i)|+|w*((u₂ i-u₄ i)-D)|+|(w-1/x₀)*D| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _) |>.trans_eq (by ring)
    _≤η+3*(18*L*η*V)+η*(8*V) := add_le_add (add_le_add h1 h2) h3
    _≤64*L*η*V := by nlinarith

end IntegerMultBounds.NLogN.ToeplitzInverse
