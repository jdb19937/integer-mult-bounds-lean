module

public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Balanced chunk widths of the positional transform layout

The balanced positional layout (`Balanced/DESIGN.md`, M5a) splits the `n = ℓ - 1` common named
bit slots of every axis into `q` consecutive chunks: the first `n % q` chunks have width
`n / q + 1`, the others `n / q`. Every round of a chunk group then sees one common width.

* `balWidth n q j`: the width of chunk `j`. `balOff n q j`: its offset, the total width of the
  chunks before it (`balOff_succ`, `balOff_eq_sum`, `balOff_top`).
* `balWidth_sum`: the widths of the `q` chunks add up to `n`.
* `le_balWidth`, `balWidth_lt`: at `q = n / K` with `1 ≤ K ≤ n`, every width lies in `[K, 2K)`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Balanced

/-- The width of chunk `j` when `n` slots are split into `q` balanced chunks. -/
def balWidth (n q j : ℕ) : ℕ := n / q + if j < n % q then 1 else 0

/-- The offset of chunk `j`: the total width of the chunks `0, …, j - 1`. -/
def balOff (n q j : ℕ) : ℕ := j * (n / q) + min j (n % q)

theorem balOff_zero (n q : ℕ) : balOff n q 0 = 0 := by
  simp [balOff]

theorem balOff_succ (n q j : ℕ) : balOff n q (j + 1) = balOff n q j + balWidth n q j := by
  unfold balOff balWidth
  split_ifs with hj
  · rw [min_eq_left (by omega : j + 1 ≤ n % q), min_eq_left hj.le]
    ring
  · rw [min_eq_right (by omega : n % q ≤ j + 1), min_eq_right (by omega : n % q ≤ j)]
    ring

theorem balOff_eq_sum (n q j : ℕ) : balOff n q j = ∑ i ∈ Finset.range j, balWidth n q i := by
  induction j with
  | zero => simp [balOff_zero]
  | succ j ih => rw [balOff_succ, ih, Finset.sum_range_succ]

/-- The offset after the last chunk is the whole axis. -/
theorem balOff_top {n q : ℕ} (hq : 0 < q) : balOff n q q = n := by
  unfold balOff
  rw [min_eq_right (Nat.mod_lt n hq).le]
  exact Nat.div_add_mod n q

/-- The `q` chunk widths add up to the axis. -/
theorem balWidth_sum {n q : ℕ} (hq : 0 < q) : ∑ j ∈ Finset.range q, balWidth n q j = n := by
  rw [← balOff_eq_sum, balOff_top hq]

/-- Consecutive chunks are disjoint and in order. -/
theorem balOff_mono (n q : ℕ) {i j : ℕ} (hij : i ≤ j) : balOff n q i ≤ balOff n q j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => rw [balOff_succ]; omega

section Bounds

variable {n K : ℕ} (hK : 0 < K) (hKn : K ≤ n)
include hK hKn

/-- There is at least one chunk. -/
theorem balQ_pos : 0 < n / K := Nat.div_pos hKn hK

/-- Every balanced chunk is at least `K` wide. -/
theorem le_balWidth (j : ℕ) : K ≤ balWidth n (n / K) j := by
  have hq := balQ_pos hK hKn
  have hqK : K * (n / K) ≤ n := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_le_self n K
  have hL : K ≤ n / (n / K) := (Nat.le_div_iff_mul_le hq).mpr hqK
  unfold balWidth
  exact hL.trans (Nat.le_add_right _ _)

/-- Every balanced chunk is less than `2 K` wide. -/
theorem balWidth_lt (j : ℕ) : balWidth n (n / K) j < 2 * K := by
  have hq := balQ_pos hK hKn
  have hL := Nat.div_add_mod n (n / K)
  have ht := Nat.mod_lt n hq
  have hnK := Nat.div_add_mod n K
  have hr := Nat.mod_lt n hK
  unfold balWidth
  set q := n / K
  set L := n / q
  set t := n % q
  split_ifs with hj
  · by_contra hc
    have hmul : q * (2 * K) ≤ q * (L + 1) := Nat.mul_le_mul_left q (by omega)
    have hcross : K + q ≤ K * q + 1 := by nlinarith
    linarith
  · by_contra hc
    have hmul : q * (2 * K) ≤ q * L := Nat.mul_le_mul_left q (by omega)
    have hcross : K ≤ K * q := Nat.le_mul_of_pos_right K hq
    linarith

end Bounds

end IntegerMultBounds.MathlibTM2.Balanced
