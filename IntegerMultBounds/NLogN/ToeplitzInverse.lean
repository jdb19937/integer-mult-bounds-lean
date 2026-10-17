module

public import Mathlib.Tactic

/-! The Gohberg–Semencul formula for the two-sided inverse of a symmetric
Toeplitz matrix of size `n`. With first column `x` of the inverse and its
reversal `z` (shifted by one, with `z₀ = 0`),
`x₀ M = L(x) L(x)ᵀ - L(z) L(z)ᵀ`, so applying the inverse costs four
triangular Toeplitz products. Matrices are natural-indexed functions supported
on `range n`; no positive-definiteness is assumed, only `x₀ ≠ 0`. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.ToeplitzInverse

open scoped BigOperators
open Finset
variable {K : Type*} [Field K]

/-- Distance between natural indices. -/
def gap (i k : ℕ) : ℕ := i-k+(k-i)

theorem gap_comm (i k : ℕ) : gap i k=gap k i := by
  unfold gap
  omega

/-- `m` is the two-sided inverse of the symmetric Toeplitz matrix with
coefficients `g`, and vanishes outside `range n`. -/
structure IsInverse (n : ℕ) (g : ℕ → K) (m : ℕ → ℕ → K) : Prop where
  supp : ∀ i j, (n ≤ i ∨ n ≤ j) → m i j=0
  right : ∀ i j, i<n → j<n → ∑ k∈range n, g (gap i k)*m k j=if i=j then 1 else 0
  left : ∀ i j, i<n → j<n → ∑ k∈range n, m i k*g (gap k j)=if i=j then 1 else 0

variable {n : ℕ} {g : ℕ → K} {m : ℕ → ℕ → K}

/-- Applying the matrix and then its inverse recovers any vector on `range n`. -/
theorem recover (h : IsInverse n g m) (w : ℕ → K) (a : ℕ) (ha : a<n) :
    w a=∑ l∈range n, m a l*∑ k∈range n, g (gap l k)*w k := by
  simp_rw [mul_sum]
  rw [sum_comm]
  simp_rw [←mul_assoc, ←sum_mul]
  rw [sum_congr rfl fun k hk => by rw [h.left a k ha (mem_range.mp hk)]]
  simp [ha]

theorem symm (h : IsInverse n g m) (i j : ℕ) : m j i=m i j := by
  by_cases hij : i<n ∧ j<n
  · obtain ⟨hi, hj⟩ := hij
    rw [recover h (fun k => m j k) i hi]
    rw [sum_congr rfl fun l hl => by
      rw [show (∑ k∈range n, g (gap l k)*m j k)=if j=l then 1 else 0 by
        rw [←h.left j l hj (mem_range.mp hl)]
        exact sum_congr rfl fun k _ => by rw [gap_comm, mul_comm]]]
    simp [hj]
  · rw [h.supp i j (by omega), h.supp j i (by omega)]

private theorem dist_reflect {l k : ℕ} (hl : l<n) (hk : k<n) :
    gap l (n-1-k)=gap (n-1-l) k := by
  unfold gap
  omega

/-- The inverse is persymmetric, since reversal fixes a Toeplitz matrix. -/
theorem persymm (h : IsInverse n g m) (i j : ℕ) (hi : i<n) (hj : j<n) :
    m (n-1-i) (n-1-j)=m i j := by
  rw [recover h (fun k => m (n-1-k) (n-1-j)) i hi]
  rw [sum_congr rfl fun l hl => by
    have hl' := mem_range.mp hl
    rw [show (∑ k∈range n, g (gap l k)*m (n-1-k) (n-1-j))=if l=j then 1 else 0 by
      rw [←sum_range_reflect]
      rw [sum_congr rfl fun k hk => by
        have hk' := mem_range.mp hk
        rw [show n-1-(n-1-k)=k by omega, dist_reflect hl' hk']]
      rw [h.right _ _ (by omega) (by omega)]
      congr 1
      exact propext ⟨fun e => by omega, fun e => by omega⟩]]
  simp [hj]

private theorem dist_succ (l k : ℕ) : gap (l+1) (k+1)=gap l k := by
  unfold gap
  omega

/-- Multiplying a column shifted up by one. -/
private theorem shifted_column (h : IsInverse n g m) (l c : ℕ) (hl : l+1<n) (hc : c<n) :
    ∑ k∈range n, g (gap l k)*m (k+1) c=
      (if l+1=c then 1 else 0)-g (l+1)*m 0 c := by
  have hr := h.right (l+1) c hl hc
  have h0 : gap (l+1) 0=l+1 := by unfold gap; omega
  have e := (sum_range_succ' (fun k => g (gap (l+1) k)*m k c) n).symm.trans
    (sum_range_succ _ n)
  simp only [dist_succ, h0, h.supp n c (Or.inl le_rfl), mul_zero, add_zero] at e
  linear_combination e+hr

/-- Trench recurrence along diagonals of the inverse. -/
theorem shift (h : IsInverse n g m) (hx : m 0 0≠0) (i j : ℕ) (hi : i+1<n) (hj : j+1<n) :
    m 0 0*(m (i+1) (j+1)-m i j)=m (i+1) 0*m (j+1) 0-m i (n-1)*m j (n-1) := by
  set w : ℕ → K := fun k => m 0 0*(m (k+1) (j+1)-m k j)-m (j+1) 0*m (k+1) 0 with hw
  have hT : ∀ l, l+1<n → ∑ k∈range n, g (gap l k)*w k=0 := by
    intro l hl
    have e1 := shifted_column h l (j+1) hl hj
    have e2 := shifted_column h l 0 hl (by omega)
    have e3 := h.right l j (by omega) (by omega)
    have hsym := symm h (j+1) 0
    simp only [hw, mul_sub, sum_sub_distrib]
    simp_rw [mul_left_comm (g _) (m 0 0), mul_left_comm (g _) (m (j+1) 0), ←mul_sum]
    rw [e1, e2, e3]
    simp only [add_left_inj, Nat.succ_ne_zero, ite_false]
    rw [hsym]
    split <;> ring
  obtain ⟨n', rfl⟩ : ∃ n', n=n'+1 := ⟨n-1, by omega⟩
  have hrec (a : ℕ) (ha : a<n'+1) :
      w a=m a n'*∑ k∈range (n'+1), g (gap n' k)*w k := by
    rw [recover h w a ha, sum_range_succ, sum_eq_zero fun l hl =>
      by rw [hT l (by have := mem_range.mp hl; omega), mul_zero], zero_add]
  have hlast := hrec n' (by omega)
  have hw' : w n'=-(m 0 0*m n' j) := by
    simp only [hw, h.supp (n'+1) (j+1) (by omega), h.supp (n'+1) 0 (by omega)]
    ring
  have hcorner : m n' n'=m 0 0 := by
    simpa using persymm h 0 0 (by omega) (by omega)
  rw [hw', hcorner] at hlast
  have hlam : ∑ k∈range (n'+1), g (gap n' k)*w k=-m n' j := by
    apply mul_left_cancel₀ hx
    linear_combination -hlast
  have hi' := hrec i (by omega)
  rw [hlam, hw] at hi'
  simp only [Nat.add_sub_cancel]
  rw [symm h j n'] at hi'
  simp only at hi'
  linear_combination hi'

/-- First column of the inverse. -/
def col (m : ℕ → ℕ → K) (a : ℕ) : K := m a 0

/-- Last column shifted down by one, with zero first entry. -/
def rev (n : ℕ) (m : ℕ → ℕ → K) : ℕ → K
  | 0 => 0
  | a+1 => m a (n-1)

/-- The shifted last column is the reversed first column. -/
theorem rev_eq (h : IsInverse n g m) (a : ℕ) (ha : a<n) : rev n m (a+1)=col m (n-1-a) := by
  simp only [rev, col]
  rw [←persymm h a (n-1) ha (by omega), show n-1-(n-1)=0 by omega]

/-- Gohberg–Semencul: `x₀ M = L(x) L(x)ᵀ - L(z) L(z)ᵀ`, written along the
diagonal through `(a,b)` with `a=0` or `b=0`. -/
theorem gohberg_semencul (h : IsInverse n g m) (hx : m 0 0≠0) (a b : ℕ) (hab : a=0 ∨ b=0) :
    ∀ d, a+d<n → b+d<n → m 0 0*m (a+d) (b+d)=
      ∑ k∈range (d+1), (col m (a+k)*col m (b+k)-rev n m (a+k)*rev n m (b+k)) := by
  intro d
  induction d with
  | zero =>
    intro _ _
    simp only [zero_add, sum_range_one, add_zero, col]
    rcases hab with rfl | rfl
    · have hsym := symm h 0 b
      simp only [rev, zero_mul, sub_zero]
      rw [hsym]
    · simp only [rev, mul_zero, sub_zero]
      rw [mul_comm]
  | succ d ih =>
    intro ha hb
    rw [sum_range_succ, ←ih (by omega) (by omega)]
    have hs := shift h hx (a+d) (b+d) (by omega) (by omega)
    simp only [col, rev, ←add_assoc]
    linear_combination hs

/-- Entrywise form for any `i, j < n`. -/
theorem entry (h : IsInverse n g m) (hx : m 0 0≠0) (i j : ℕ) (hi : i<n) (hj : j<n) :
    m 0 0*m i j=∑ k∈range (min i j+1),
      (col m (i-min i j+k)*col m (j-min i j+k)-rev n m (i-min i j+k)*rev n m (j-min i j+k)) := by
  have hd := gohberg_semencul h hx (i-min i j) (j-min i j) (by omega) (min i j)
    (by omega) (by omega)
  rwa [show i-min i j+min i j=i by omega, show j-min i j+min i j=j by omega] at hd

end IntegerMultBounds.NLogN.ToeplitzInverse
