module

public import IntegerMultBounds.NLogN.ToeplitzInverse

/-! Gohberg–Semencul as an operator identity: applying the inverse of a
symmetric Toeplitz block is `(L(x) L(x)ᵀ v - L(z) L(z)ᵀ v) / x₀`, where
`L(x) v` is the truncated lower convolution and `L(x)ᵀ v` its upper
correlation. Each factor's row sums are bounded by the coefficient mass. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.ToeplitzInverse

open scoped BigOperators
open Finset
variable {K : Type*} [Field K]

/-- Lower triangular Toeplitz product `L(x) v`. -/
def lower (x v : ℕ → K) (i : ℕ) : K := ∑ k∈range (i+1), x (i-k)*v k

/-- Upper triangular Toeplitz product `L(x)ᵀ v` of length `L`. -/
def upper (L : ℕ) (x v : ℕ → K) (i : ℕ) : K := ∑ j∈Ico i L, x (j-i)*v j

variable {n : ℕ} {g : ℕ → K} {m : ℕ → ℕ → K}

/-- The Gohberg–Semencul diagonal sum in convolution order. -/
theorem entry_conv (h : IsInverse n g m) (hx : m 0 0≠0) (i j : ℕ) (hi : i<n) (hj : j<n) :
    m 0 0*m i j=∑ k∈range (min i j+1),
      (col m (i-k)*col m (j-k)-rev n m (i-k)*rev n m (j-k)) := by
  rw [entry h hx i j hi hj, ←sum_range_reflect]
  refine sum_congr rfl fun k hk => ?_
  have hk' := mem_range.mp hk
  rw [show i-min i j+(min i j+1-1-k)=i-k by omega, show j-min i j+(min i j+1-1-k)=j-k by omega]

private theorem triangle (L i : ℕ) (f : ℕ → ℕ → K) :
    ∑ k∈range (i+1), ∑ j∈Ico k L, f k j=∑ j∈range L, ∑ k∈range (min i j+1), f k j := by
  apply sum_comm'
  intro k j
  simp only [mem_range, mem_Ico]
  omega

theorem lower_upper (L : ℕ) (x v : ℕ → K) (i : ℕ) :
    lower x (upper L x v) i=∑ j∈range L, (∑ k∈range (min i j+1), x (i-k)*x (j-k))*v j := by
  simp only [lower, upper, mul_sum]
  rw [triangle L i (fun k j => x (i-k)*(x (j-k)*v j))]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_mul]
  exact sum_congr rfl fun k _ => by ring

/-- Applying the inverse by four triangular Toeplitz products. -/
theorem apply_four (h : IsInverse n g m) (hx : m 0 0≠0) (v : ℕ → K) (i : ℕ) (hi : i<n) :
    m 0 0*∑ j∈range n, m i j*v j=
      lower (col m) (upper n (col m) v) i-lower (rev n m) (upper n (rev n m) v) i := by
  rw [lower_upper n _ v i, lower_upper n _ v i, ←sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [←mul_assoc, entry_conv h hx i j hi (mem_range.mp hj), ←sub_mul, ←sum_sub_distrib]

end IntegerMultBounds.NLogN.ToeplitzInverse
