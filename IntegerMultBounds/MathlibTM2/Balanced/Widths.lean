module

public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Balanced chunk widths of the positional transform layout

The positional layout (`Fast/LayoutMath.lean`) cuts the `n = ℓ - 1` common named bit slots of
every axis into chunks of one width `K` and leaves the `n mod K` lowest slots to the prefix. At
`K = ⌊d^c⌋` that remainder can be almost `K` slots per axis, which costs `d K` single-bit moves
and up to `K` prefix rounds.

* `balWidth n q j`, `balOff n q j`: the split of `n` slots into `q` chunks of widths `n / q` and
  `n / q + 1` (`balOff_succ`, `balOff_eq_sum`, `balOff_top`, `balWidth_sum`); at `q = n / K`
  with `1 ≤ K ≤ n` every width lies in `[K, 2K)` (`le_balWidth`, `balWidth_lt`).
* `unifWidth n K = max K (n / ⌊n/K⌋)`: one width for all chunks. For `1 ≤ K ≤ n` it is the
  narrow balanced width `n / ⌊n/K⌋`, in `[K, 2K)` and at most `n` (`unifWidth_eq`,
  `le_unifWidth`, `unifWidth_le_two_mul`, `unifWidth_le`), and the remainder it leaves is below
  the number of chunks: `n mod unifWidth n K < ⌊n/K⌋` (`mod_unifWidth_lt`). The prefix then
  holds fewer than `n / K` slots per axis.
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

/-! ### One uniform width -/

/-- The uniform chunk width `n / ⌊n/K⌋`, and `K` when `n < K`. -/
def unifWidth (n K : ℕ) : ℕ := max K (n / (n / K))

theorem le_unifWidth (n K : ℕ) : K ≤ unifWidth n K := le_max_left _ _

/-- The uniform width is at most `2 K` for every `n`. -/
theorem unifWidth_le_two_mul (n K : ℕ) : unifWidth n K ≤ 2 * K := by
  unfold unifWidth
  rcases Nat.eq_zero_or_pos (n / K) with hq | hq
  · rw [hq, Nat.div_zero]
    omega
  · have hK : 0 < K := Nat.pos_of_ne_zero fun h => by simp [h] at hq
    have hKn : K ≤ n := by
      by_contra hc
      rw [Nat.div_eq_of_lt (by omega)] at hq
      omega
    have h := balWidth_lt hK hKn (n / K)
    have hmod := Nat.mod_lt n hq
    simp only [balWidth, show ¬ n / K < n % (n / K) by omega, ↓reduceIte, Nat.add_zero] at h
    omega

section Uniform

variable {n K : ℕ} (hK : 0 < K) (hKn : K ≤ n)
include hK hKn

theorem unifWidth_eq : unifWidth n K = n / (n / K) := by
  have h := le_balWidth hK hKn (n / K)
  have hmod := Nat.mod_lt n (balQ_pos hK hKn)
  simp only [balWidth, show ¬ n / K < n % (n / K) by omega, ↓reduceIte, Nat.add_zero] at h
  unfold unifWidth
  exact max_eq_right h

theorem unifWidth_le : unifWidth n K ≤ n := by
  rw [unifWidth_eq hK hKn]
  exact Nat.div_le_self _ _

/-- **The remainder of the uniform width.** Cutting `n` slots into chunks of `n / ⌊n/K⌋`
leaves fewer than `⌊n/K⌋` slots: `n = w q + r` with `r = n mod q < q`, and
`n mod w = r mod w ≤ r`. -/
theorem mod_unifWidth_lt : n % unifWidth n K < n / K := by
  have hq := balQ_pos hK hKn
  rw [unifWidth_eq hK hKn]
  set q := n / K
  have hsplit := Nat.div_add_mod n q
  have hr := Nat.mod_lt n hq
  calc n % (n / q) = (n % q + (n / q) * q) % (n / q) := by
        congr 1
        rw [Nat.mul_comm]
        omega
    _ = n % q % (n / q) := Nat.add_mul_mod_self_left _ _ _
    _ ≤ n % q := Nat.mod_le _ _
    _ < q := hr

end Uniform

end IntegerMultBounds.MathlibTM2.Balanced
