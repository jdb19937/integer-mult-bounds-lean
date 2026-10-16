module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-! Rounded Newton iteration for reciprocals, using multiplications only.
From `r₀` with `0 ≤ e₀ = 1 - b r₀ ≤ 1 - κ`, each step `r ← r (2 - b r)` with
perturbation `δ` gives `e' = e² - b δ`. While the error stays at most `1 - κ`
it contracts geometrically until it is quadratically small; the final relative
error is bounded by the accumulated perturbations. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.NewtonRecip

/-- The exact error recursion of a perturbed Newton step. -/
theorem step_error (b r δ : ℝ) :
    1-b*(r*(2-b*r)+δ)=(1-b*r)^2-b*δ := by ring

/-- One step keeps a two-sided error bound. -/
theorem step_bound (b r δ ε E : ℝ) (he : |1-b*r|≤E) (hδ : |b*δ|≤ε) :
    |1-b*(r*(2-b*r)+δ)|≤E^2+ε := by
  rw [step_error]
  calc |(1-b*r)^2-b*δ|≤|(1-b*r)^2|+|b*δ| := abs_sub _ _
    _≤E^2+ε := by
        rw [abs_pow]
        have := abs_nonneg (1-b*r)
        exact add_le_add (pow_le_pow_left₀ this he 2) hδ

/-- Error sequence: `E (k+1) = E k ^ 2 + ε`. -/
def errSeq (E₀ ε : ℝ) : ℕ → ℝ
  | 0 => E₀
  | k+1 => errSeq E₀ ε k^2+ε

/-- Iterating the step: the error after `k` perturbed steps is at most `errSeq`. -/
theorem iter_bound (b : ℝ) (hb : 0≤b) (r : ℕ → ℝ) (δ : ℕ → ℝ) (E₀ ε : ℝ)
    (hr : ∀ k, r (k+1)=r k*(2-b*r k)+δ k) (hδ : ∀ k, |b*δ k|≤ε) (h₀ : |1-b*r 0|≤E₀) :
    ∀ k, |1-b*r k|≤errSeq E₀ ε k
  | 0 => h₀
  | k+1 => by
      rw [hr k]
      exact step_bound b (r k) (δ k) ε _ (iter_bound b hb r δ E₀ ε hr hδ h₀ k) (hδ k)

/-- Quadratic convergence with perturbations: with `ε ≤ 2κ/9`, `0 < κ ≤ 1` and
`0 ≤ E₀ ≤ 1-κ`, either `(1+κ/2) E_k ≤ (1-κ/2)^(2^k)` or `E_k ≤ 3ε/κ`. -/
theorem errSeq_quad (E₀ ε κ : ℝ) (hκ : 0<κ) (hκ1 : κ≤1) (hε : 0≤ε) (hεκ : ε≤2*κ/9)
    (hE₀ : 0≤E₀) (hE₀1 : E₀≤1-κ) :
    ∀ k, 0≤errSeq E₀ ε k ∧
      ((1+κ/2)*errSeq E₀ ε k≤(1-κ/2)^(2^k) ∨ errSeq E₀ ε k≤3*ε/κ) := by
  intro k
  induction k with
  | zero =>
    refine ⟨by simp [errSeq, hE₀], Or.inl ?_⟩
    simp only [errSeq, pow_zero, pow_one]
    nlinarith
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨by simp only [errSeq]; positivity, ?_⟩
    simp only [errSeq]
    set E := errSeq E₀ ε k
    have hfloor : (3*ε/κ)^2+ε≤3*ε/κ := by
      rw [div_pow, ← sub_nonneg]
      have e : 3*ε/κ-((3*ε)^2/κ^2+ε)=ε*(3*κ-9*ε-κ^2)/κ^2 := by field_simp; ring
      rw [e]
      apply div_nonneg _ (by positivity)
      apply mul_nonneg hε
      nlinarith
    rcases h1 with h1 | h1
    · by_cases hq : ε≤κ/2*E^2
      · left
        have hc0 : 0≤(1+κ/2)*E := by positivity
        have : (1+κ/2)*(E^2+ε)≤((1+κ/2)*E)^2 := by nlinarith
        calc (1+κ/2)*(E^2+ε)≤((1+κ/2)*E)^2 := this
          _≤((1-κ/2)^(2^k))^2 := pow_le_pow_left₀ hc0 h1 2
          _=(1-κ/2)^(2^(k+1)) := by rw [← pow_mul, pow_succ]
      · right
        push Not at hq
        have hE2 : E^2<2*ε/κ := by rw [lt_div_iff₀ hκ]; nlinarith
        have : ε≤ε/κ := by rw [le_div_iff₀ hκ]; nlinarith
        have h3 : 2*ε/κ+ε≤3*ε/κ := by
          have e : 3*ε/κ=2*ε/κ+ε/κ := by ring
          linarith
        linarith
    · right
      have hsq : E^2≤(3*ε/κ)^2 := pow_le_pow_left₀ h0 h1 2
      linarith

/-- After `K` steps with `(1-κ/2)^(2^K) ≤ 3ε/κ`, the error is at most `3ε/κ`. -/
theorem errSeq_final (E₀ ε κ : ℝ) (hκ : 0<κ) (hκ1 : κ≤1) (hε : 0≤ε) (hεκ : ε≤2*κ/9)
    (hE₀ : 0≤E₀) (hE₀1 : E₀≤1-κ) (K : ℕ) (hK : (1-κ/2)^(2^K)≤3*ε/κ) :
    errSeq E₀ ε K≤3*ε/κ := by
  obtain ⟨h0, h1 | h1⟩ := errSeq_quad E₀ ε κ hκ hκ1 hε hεκ hE₀ hE₀1 K
  · have : errSeq E₀ ε K≤(1+κ/2)*errSeq E₀ ε K := by nlinarith
    linarith
  · exact h1

/-- The rounded Newton iterates for `1/b` from `1/4`. -/
noncomputable def newtonR (rd : ℝ → ℝ) (b : ℝ) : ℕ → ℝ
  | 0 => 1/4
  | k+1 => rd (newtonR rd b k*(2-rd (b*newtonR rd b k)))

/-- Rounded Newton for `b ∈ [β, 3]`: the error stays within the perturbed error
sequence with `ε = 5η` and `κ = β/4`. -/
theorem newtonR_err (rd : ℝ → ℝ) (η : ℝ) (hrd : ∀ x, |rd x-x|≤η) (β b : ℝ) (hβ : 0<β)
    (hβb : β≤b) (hb3 : b≤3) (hη : 5*η≤2*(β/4)/9) :
    ∀ k, |1-b*newtonR rd b k|≤errSeq (1-b/4) (5*η) k := by
  have hb : 0<b := lt_of_lt_of_le hβ hβb
  have hη0 : 0≤η := le_trans (abs_nonneg _) (hrd 0)
  have hκ1 : β/4≤1 := by linarith
  have hE₀ : 0≤1-b/4 := by linarith
  have hE₀1 : 1-b/4≤1-β/4 := by linarith
  intro k
  induction k with
  | zero =>
    simp only [newtonR, errSeq]
    rw [abs_of_nonneg (by linarith)]; linarith
  | succ k ih =>
    -- the current error is at most one, so `0 ≤ b r ≤ 2`
    have hseq := errSeq_quad (1-b/4) (5*η) (β/4) (by positivity) hκ1 (by positivity) hη hE₀ hE₀1 k
    have hE1 : errSeq (1-b/4) (5*η) k≤1 := by
      rcases hseq.2 with h | h
      · have hp : (1-β/4/2)^(2^k)≤1 := pow_le_one₀ (by linarith) (by linarith)
        nlinarith [hseq.1]
      · have : 3*(5*η)/(β/4)≤1 := by rw [div_le_one (by positivity)]; linarith
        linarith
    set r := newtonR rd b k
    have hbr : |1-b*r|≤1 := ih.trans hE1
    have hr : |r|≤2/b := by
      rw [le_div_iff₀ hb]
      have h := abs_le.mp hbr
      have hr0 : 0≤r := by nlinarith
      rw [abs_of_nonneg hr0]; nlinarith
    -- the perturbation of the step
    set δ := rd (r*(2-rd (b*r)))-r*(2-b*r)
    have hδ : |b*δ|≤5*η := by
      have h1 := hrd (r*(2-rd (b*r)))
      have h2 := hrd (b*r)
      have e : δ=(rd (r*(2-rd (b*r)))-r*(2-rd (b*r)))-r*(rd (b*r)-b*r) := by simp only [δ]; ring
      rw [e, abs_mul, abs_of_pos hb]
      have h3 : |r*(rd (b*r)-b*r)|≤2/b*η := by
        rw [abs_mul]; exact mul_le_mul hr h2 (abs_nonneg _) (by positivity)
      have h4 := abs_sub (rd (r*(2-rd (b*r)))-r*(2-rd (b*r))) (r*(rd (b*r)-b*r))
      calc b*|(rd (r*(2-rd (b*r)))-r*(2-rd (b*r)))-r*(rd (b*r)-b*r)|≤b*(η+2/b*η) :=
            mul_le_mul_of_nonneg_left (h4.trans (add_le_add h1 h3)) hb.le
        _=b*η+2*η := by field_simp
        _≤5*η := by nlinarith
    have hnext : newtonR rd b (k+1)=r*(2-b*r)+δ := by simp only [newtonR, δ, r]; ring
    rw [hnext]
    exact step_bound b r δ (5*η) _ ih hδ

/-- The reciprocal error after enough steps. -/
theorem newtonR_recip (rd : ℝ → ℝ) (η : ℝ) (hrd : ∀ x, |rd x-x|≤η) (β b : ℝ) (hβ : 0<β)
    (hβb : β≤b) (hb3 : b≤3) (hη : 5*η≤2*(β/4)/9) (K : ℕ)
    (hK : (1-β/4/2)^(2^K)≤3*(5*η)/(β/4)) :
    |newtonR rd b K-1/b|≤60*η/β^2 := by
  have hb : 0<b := lt_of_lt_of_le hβ hβb
  have hη0 : 0≤η := le_trans (abs_nonneg _) (hrd 0)
  have he := (newtonR_err rd η hrd β b hβ hβb hb3 hη K).trans
    (errSeq_final (1-b/4) (5*η) (β/4) (by positivity) (by linarith) (by positivity) hη
      (by linarith) (by linarith) K hK)
  have e : newtonR rd b K-1/b=-(1-b*newtonR rd b K)/b := by field_simp; ring
  rw [e, abs_div, abs_neg, abs_of_pos hb, div_le_iff₀ hb]
  have h1 : 3*(5*η)/(β/4)=60*η/β := by field_simp; ring
  rw [h1] at he
  have h2 : 60*η/β≤60*η/β^2*b := by
    calc 60*η/β=60*η/β^2*β := by field_simp
      _≤60*η/β^2*b := mul_le_mul_of_nonneg_left hβb (by positivity)
  linarith

/-- Multipliers through a Newton reciprocal on the working range `β ≤ b ≤ 3`,
`|a| ≤ M`; outside the range (never met by dominant elimination) rounded
division stands in, so the rule is total. -/
noncomputable def recipMul (rd : ℝ → ℝ) (M β : ℝ) (K : ℕ) (a b : ℝ) : ℝ :=
  if β≤b ∧ b≤3 ∧ |a|≤M then rd (a*newtonR rd b K) else rd (a/b)

theorem recipMul_zero (rd : ℝ → ℝ) (hrd0 : rd 0=0) (M β : ℝ) (K : ℕ) (b : ℝ) :
    recipMul rd M β K 0 b=0 := by
  unfold recipMul; split <;> simp [hrd0]

/-- The reciprocal multiplier rule is within `η(1+60M/β²)` of exact division. -/
theorem recipMul_err (rd : ℝ → ℝ) (η : ℝ) (hrd : ∀ x, |rd x-x|≤η) (M β : ℝ) (hM : 0≤M)
    (hβ : 0<β) (hη : 5*η≤2*(β/4)/9) (K : ℕ) (hK : (1-β/4/2)^(2^K)≤3*(5*η)/(β/4))
    (a b : ℝ) : |recipMul rd M β K a b-a/b|≤η*(1+60*M/β^2) := by
  have hη0 : 0≤η := le_trans (abs_nonneg _) (hrd 0)
  have hextra : 0≤η*(60*M/β^2) := by positivity
  unfold recipMul
  split
  · rename_i h
    obtain ⟨hβb, hb3, ha⟩ := h
    have hr := newtonR_recip rd η hrd β b hβ hβb hb3 hη K hK
    have h1 := hrd (a*newtonR rd b K)
    have e : rd (a*newtonR rd b K)-a/b=(rd (a*newtonR rd b K)-a*newtonR rd b K)+
        a*(newtonR rd b K-1/b) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have h2 : |a*(newtonR rd b K-1/b)|≤M*(60*η/β^2) := by
      rw [abs_mul]; exact mul_le_mul ha hr (abs_nonneg _) hM
    have e2 : η*(1+60*M/β^2)=η+M*(60*η/β^2) := by ring
    rw [e2]; linarith
  · have := hrd (a/b)
    nlinarith

end IntegerMultBounds.NLogN.NewtonRecip
