module

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Pairwise coprime odd source lengths

An elementary choice of the source lengths `s_i` of the multidimensional transform: odd,
pairwise coprime, and within a factor `1 - 1/(4d)` of the axis lengths. No primality is
needed. Fix `d ≥ 2` and an odd `N` divisible by every odd prime below `4d` (for example
`oddProd d = 1 · 3 ⋯ (4d - 1)`). For an even `x₀` put

* group A: `u_i = N (x₀ + 2i) + 1`,
* group B: `v_j = N (2x₀ + 1 + 2j) + 2`.

All of them are odd and, for indices below `d`, pairwise coprime. A prime `q` dividing two of
them is odd and does not divide `N`, so `q > 4d`. It divides `2N (i - i')` or `2N (j - j')`
(same group), hence `i - i'` or `j - j'`, or it divides
`y (N x + 1) - x (N y + 2) = y - 2x = 1 + 2j - 4i` (one from each group). These numbers are
nonzero and smaller than `4d` in absolute value, which is impossible.

With `x₀ = start d N R` and `8 d² N + 4d ≤ R` the A lengths lie in
`((1 - 2η) R, (1 - η) R]` and the B lengths in `((1 - 2η) 2R, (1 - η) 2R]`, `η = 1/(4d)`.
For the axis lengths `t_i = 2^e` (first `a` axes) and `t_i = 2^(e+1)` (the others, `R = 2^e`)
this gives `s_i < t_i`, `gcd(s_i, t_i) = 1`, and, by Bernoulli's inequality
`(1 - 1/(2d))^d ≥ 1/2`, the product bounds `T/2 < S < T`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Mult.Moduli

open Finset
open scoped Function

/-! ### The odd product -/

/-- The product of the odd numbers below `4d`. -/
def oddProd (d : ℕ) : ℕ := ∏ i ∈ range (2 * d), (2 * i + 1)

theorem odd_prod_range (m : ℕ) : Odd (∏ i ∈ range m, (2 * i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ]
    exact ih.mul (odd_two_mul_add_one m)

theorem oddProd_odd (d : ℕ) : Odd (oddProd d) := odd_prod_range _

theorem oddProd_pos (d : ℕ) : 0 < oddProd d := (oddProd_odd d).pos

/-- Every odd number below `4d` divides `oddProd d`. -/
theorem dvd_oddProd {d m : ℕ} (hm : Odd m) (hm4 : m < 4 * d) : m ∣ oddProd d := by
  obtain ⟨k, rfl⟩ := hm
  exact dvd_prod_of_mem (fun i => 2 * i + 1) (mem_range.2 (by omega))

/-- Every odd prime below `4d` divides `oddProd d`. -/
theorem prime_dvd_oddProd {d : ℕ} :
    ∀ q, q.Prime → q ≠ 2 → q < 4 * d → q ∣ oddProd d :=
  fun _ hq h2 hq4 => dvd_oddProd (hq.odd_of_ne_two h2) hq4

theorem oddProd_le (d : ℕ) : oddProd d ≤ (4 * d) ^ (2 * d) := by
  unfold oddProd
  calc ∏ i ∈ range (2 * d), (2 * i + 1) ≤ (4 * d) ^ (range (2 * d)).card :=
        prod_le_pow_card _ _ _ fun i hi => by rw [mem_range] at hi; omega
    _ = (4 * d) ^ (2 * d) := by rw [card_range]

/-! ### The two groups -/

/-- Group A: `N (x₀ + 2i) + 1`. -/
def modA (N x₀ i : ℕ) : ℕ := N * (x₀ + 2 * i) + 1

/-- Group B: `N (2x₀ + 1 + 2j) + 2`. -/
def modB (N x₀ j : ℕ) : ℕ := N * (2 * x₀ + 1 + 2 * j) + 2

/-- The `i`-th length: group A for `i < a`, group B (index `i - a`) otherwise. -/
def modulus (N x₀ a i : ℕ) : ℕ := if i < a then modA N x₀ i else modB N x₀ (i - a)

/-- The `i`-th axis length: `2^e` for `i < a`, `2^(e+1)` otherwise. -/
def axisLen (e a i : ℕ) : ℕ := if i < a then 2 ^ e else 2 ^ (e + 1)

/-- The even starting point `x₀ = 2 (⌊(2d - 1) R / (4 d N)⌋ + 1)`. -/
def start (d N R : ℕ) : ℕ := 2 * ((2 * d - 1) * R / (4 * d * N) + 1)

theorem modA_odd {N x₀ : ℕ} (hx : Even x₀) (i : ℕ) : Odd (modA N x₀ i) := by
  obtain ⟨c, rfl⟩ := hx
  exact ⟨N * (c + i), by unfold modA; ring⟩

theorem modB_odd {N x₀ : ℕ} (hN : Odd N) (j : ℕ) : Odd (modB N x₀ j) := by
  have h1 : Odd (2 * x₀ + 1 + 2 * j) := by
    rw [show 2 * x₀ + 1 + 2 * j = 2 * (x₀ + j) + 1 by ring]
    exact odd_two_mul_add_one _
  exact (hN.mul h1).add_even even_two

theorem coprime_modA (N x₀ i : ℕ) : Nat.Coprime N (modA N x₀ i) := by
  unfold modA; simp

theorem coprime_modB {N : ℕ} (hN : Odd N) (x₀ j : ℕ) : Nat.Coprime N (modB N x₀ j) := by
  unfold modB
  rw [Nat.coprime_mul_left_add_right]
  exact Nat.coprime_two_right.2 hN

theorem start_even (d N R : ℕ) : Even (start d N R) :=
  ⟨(2 * d - 1) * R / (4 * d * N) + 1, by unfold start; ring⟩

/-! ### Coprimality -/

/-- Coprimality from a small combination. Let `u` be odd and coprime to `N`, let `N` be
divisible by every odd prime below `4d`, and let every odd prime that divides `u` and `v` but
not `N` divide a fixed integer `z ≠ 0` with `|z| < 4d`. Then `u` and `v` are coprime. -/
theorem coprime_of_small {u v N d : ℕ} (z : ℤ) (hu : Odd u) (hNu : Nat.Coprime N u)
    (hN : ∀ q, q.Prime → q ≠ 2 → q < 4 * d → q ∣ N) (hz0 : z ≠ 0) (hz : z.natAbs < 4 * d)
    (hcomb : ∀ q, q.Prime → q ≠ 2 → ¬ q ∣ N → q ∣ u → q ∣ v → (q : ℤ) ∣ z) :
    Nat.Coprime u v := by
  apply Nat.coprime_of_dvd
  intro q hq hqu hqv
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hu) (even_iff_two_dvd.2 hqu)
  have hqN : ¬ q ∣ N := fun hqN =>
    hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hqN hNu) hqu)
  have hqz := hcomb q hq hq2 hqN hqu hqv
  have hle : q ≤ z.natAbs := by
    have h := Int.natAbs_dvd_natAbs.2 hqz
    rw [Int.natAbs_natCast] at h
    exact Nat.le_of_dvd (Int.natAbs_pos.2 hz0) h
  exact hqN (hN q hq hq2 (by omega))

theorem int_dvd_of_dvd_two_mul {q N : ℕ} {z : ℤ} (hq : q.Prime) (h2 : q ≠ 2) (hN : ¬ q ∣ N)
    (h : (q : ℤ) ∣ 2 * N * z) : (q : ℤ) ∣ z := by
  rcases Int.Prime.dvd_mul' hq h with h | h
  · exfalso
    have h' : q ∣ 2 * N := Int.natCast_dvd_natCast.1 (by exact_mod_cast h)
    rcases (Nat.Prime.dvd_mul hq).1 h' with h'' | h''
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h'')
    · exact hN h''
  · exact h

theorem int_dvd_sub {q u v : ℕ} (hu : q ∣ u) (hv : q ∣ v) : (q : ℤ) ∣ (u : ℤ) - v :=
  dvd_sub (Int.natCast_dvd_natCast.2 hu) (Int.natCast_dvd_natCast.2 hv)

variable {d N x₀ : ℕ}

theorem coprime_AA (hx : Even x₀) (hN : ∀ q, q.Prime → q ≠ 2 → q < 4 * d → q ∣ N)
    {i i' : ℕ} (hi : i < d) (hi' : i' < d) (hne : i ≠ i') :
    Nat.Coprime (modA N x₀ i) (modA N x₀ i') := by
  refine coprime_of_small ((i : ℤ) - i') (modA_odd hx i) (coprime_modA N x₀ i) hN
    (by omega) (by omega) ?_
  intro q hq h2 hqN hu hv
  apply int_dvd_of_dvd_two_mul hq h2 hqN
  have h := int_dvd_sub hu hv
  have e : ((modA N x₀ i : ℕ) : ℤ) - (modA N x₀ i' : ℕ) = 2 * N * ((i : ℤ) - i') := by
    unfold modA; push_cast; ring
  rwa [e] at h

theorem coprime_BB (hNo : Odd N) (hN : ∀ q, q.Prime → q ≠ 2 → q < 4 * d → q ∣ N)
    {j j' : ℕ} (hj : j < d) (hj' : j' < d) (hne : j ≠ j') :
    Nat.Coprime (modB N x₀ j) (modB N x₀ j') := by
  refine coprime_of_small ((j : ℤ) - j') (modB_odd hNo j) (coprime_modB hNo x₀ j) hN
    (by omega) (by omega) ?_
  intro q hq h2 hqN hu hv
  apply int_dvd_of_dvd_two_mul hq h2 hqN
  have h := int_dvd_sub hu hv
  have e : ((modB N x₀ j : ℕ) : ℤ) - (modB N x₀ j' : ℕ) = 2 * N * ((j : ℤ) - j') := by
    unfold modB; push_cast; ring
  rwa [e] at h

theorem coprime_AB (hx : Even x₀) (hN : ∀ q, q.Prime → q ≠ 2 → q < 4 * d → q ∣ N)
    {i j : ℕ} (hi : i < d) (hj : j < d) :
    Nat.Coprime (modA N x₀ i) (modB N x₀ j) := by
  refine coprime_of_small (1 + 2 * (j : ℤ) - 4 * i) (modA_odd hx i) (coprime_modA N x₀ i) hN
    (by omega) (by omega) ?_
  intro q hq _ _ hu hv
  have h : (q : ℤ) ∣ (2 * x₀ + 1 + 2 * j : ℕ) * (modA N x₀ i : ℕ) -
      (x₀ + 2 * i : ℕ) * (modB N x₀ j : ℕ) :=
    dvd_sub (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.2 hu) _)
      (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.2 hv) _)
  have e : ((2 * x₀ + 1 + 2 * j : ℕ) : ℤ) * (modA N x₀ i : ℕ) -
      (x₀ + 2 * i : ℕ) * (modB N x₀ j : ℕ) = 1 + 2 * (j : ℤ) - 4 * i := by
    unfold modA modB; push_cast; ring
  rwa [e] at h

theorem modulus_odd (hNo : Odd N) (hx : Even x₀) (a i : ℕ) : Odd (modulus N x₀ a i) := by
  unfold modulus; split_ifs
  · exact modA_odd hx i
  · exact modB_odd hNo _

theorem modulus_pairwise (hNo : Odd N) (hx : Even x₀)
    (hN : ∀ q, q.Prime → q ≠ 2 → q < 4 * d → q ∣ N) (a : ℕ) :
    Pairwise (Nat.Coprime on (fun i : Fin d => modulus N x₀ a i)) := by
  intro i j hij
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  have hi := i.isLt
  have hj := j.isLt
  simp only [Function.onFun, modulus]
  split_ifs with h1 h2 h2
  · exact coprime_AA hx hN hi hj hij'
  · exact coprime_AB hx hN hi (by omega)
  · exact (coprime_AB hx hN hj (by omega)).symm
  · exact coprime_BB hNo hN (by omega) (by omega) (by omega)

/-! ### Interval bounds -/

theorem start_bounds {d N R : ℕ} (hd : 1 ≤ d) (hN : 1 ≤ N) :
    2 * d * R < 2 * d * (N * start d N R) + R ∧
      2 * d * (N * start d N R) + R ≤ 2 * d * R + 4 * d * N := by
  have hpos : 0 < 4 * d * N := by positivity
  set Q := (2 * d - 1) * R / (4 * d * N) with hQ
  have h1 := Nat.lt_mul_div_succ ((2 * d - 1) * R) hpos
  have h2 := Nat.mul_div_le ((2 * d - 1) * R) (4 * d * N)
  rw [← hQ] at h1 h2
  have e : 2 * d * (N * start d N R) = 4 * d * N * (Q + 1) := by
    simp only [start, ← hQ]; ring
  have e2 : (2 * d - 1) * R + R = 2 * d * R := by
    have : 2 * d = (2 * d - 1) + 1 := by omega
    calc (2 * d - 1) * R + R = ((2 * d - 1) + 1) * R := by ring
      _ = 2 * d * R := by rw [← this]
  rw [e]
  constructor
  · nlinarith
  · nlinarith

/-- The length bounds of one axis in subtraction-free form: with `η = 1/(4d)`,
`(1 - 2η) t < s` is `2 d t < 2 d s + t` and `s ≤ (1 - η) t` is `4 d s + t ≤ 4 d t`. -/
structure AxisBounds (d s t : ℕ) : Prop where
  lower : 2 * d * t < 2 * d * s + t
  upper : 4 * d * s + t ≤ 4 * d * t

theorem modA_bounds {d N R i : ℕ} (hd : 1 ≤ d) (hN : 1 ≤ N) (hi : i < d)
    (hR : 8 * d ^ 2 * N + 4 * d ≤ R) : AxisBounds d (modA N (start d N R) i) R := by
  obtain ⟨hl, hu⟩ := start_bounds (R := R) hd hN
  set x := start d N R
  have hii : d * N * (i + 1) ≤ d * N * d := Nat.mul_le_mul_left _ hi
  constructor
  · unfold modA; nlinarith
  · unfold modA; nlinarith

theorem modB_bounds {d N R j : ℕ} (hd : 2 ≤ d) (hN : 1 ≤ N) (hj : j < d)
    (hR : 8 * d ^ 2 * N + 4 * d ≤ R) : AxisBounds d (modB N (start d N R) j) (2 * R) := by
  obtain ⟨hl, hu⟩ := start_bounds (d := d) (N := N) (R := R) (by omega) hN
  set x := start d N R
  have hjj : d * N * (j + 1) ≤ d * N * d := Nat.mul_le_mul_left _ hj
  have hdd : d * N * 2 ≤ d * N * d := Nat.mul_le_mul_left _ hd
  constructor
  · unfold modB; nlinarith
  · unfold modB; nlinarith

theorem AxisBounds.lt {d s t : ℕ} (h : AxisBounds d s t) (ht : 0 < t) : s < t := by
  have := h.upper
  by_contra hc
  have : 4 * d * t ≤ 4 * d * s := Nat.mul_le_mul_left _ (not_lt.1 hc)
  omega

/-- The real form `(1 - 2η) t < s ≤ (1 - η) t`, `η = 1/(4d)`. -/
theorem AxisBounds.real {d s t : ℕ} (h : AxisBounds d s t) (hd : 1 ≤ d) :
    (1 - 2 * (1 / (4 * (d : ℝ)))) * t < s ∧ (s : ℝ) ≤ (1 - 1 / (4 * (d : ℝ))) * t := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hl : (2 * d * t : ℝ) < 2 * d * s + t := by exact_mod_cast h.lower
  have hu : (4 * d * s + t : ℝ) ≤ 4 * d * t := by exact_mod_cast h.upper
  constructor
  · have e : (1 - 2 * (1 / (4 * (d : ℝ)))) * t = (2 * d * t - t) / (2 * d) := by
      field_simp; ring
    rw [e, div_lt_iff₀ (by positivity)]
    linarith
  · have e : (1 - 1 / (4 * (d : ℝ))) * t = (4 * d * t - t) / (4 * d) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    linarith

/-! ### The family -/

/-- The source lengths: `modulus` at `x₀ = start d N 2^e`. -/
def src (d N a e : ℕ) (i : Fin d) : ℕ := modulus N (start d N (2 ^ e)) a i

/-- The axis lengths: `2^e` on the first `a` axes, `2^(e+1)` on the others. -/
def box (d a e : ℕ) (i : Fin d) : ℕ := axisLen e a i

/-- What the transform needs from the source and axis lengths. -/
structure Good {d : ℕ} (s t : Fin d → ℕ) : Prop where
  odd : ∀ i, Odd (s i)
  lt : ∀ i, s i < t i
  coprime : ∀ i, Nat.Coprime (s i) (t i)
  pairwise : Pairwise (Nat.Coprime on s)
  bounds : ∀ i, AxisBounds d (s i) (t i)
  prod_lt : ∏ i, s i < ∏ i, t i
  prod_gt : ∏ i, t i < 2 * ∏ i, s i

/-- Bernoulli: `(2d)^d ≤ 2 (2d - 1)^d`, i.e. `(1 - 1/(2d))^d ≥ 1/2`. -/
theorem bernoulli_half {d : ℕ} (hd : 1 ≤ d) :
    (1 / 2 : ℝ) ≤ (1 - 1 / (2 * (d : ℝ))) ^ d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h := one_add_mul_le_pow (a := -(1 / (2 * (d : ℝ)))) (by
    have : 1 / (2 * (d : ℝ)) ≤ 1 / 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    linarith) d
  have e : 1 + (d : ℝ) * -(1 / (2 * d)) = 1 / 2 := by field_simp; ring
  rw [e, ← sub_eq_add_neg] at h
  exact h

/-- From the axis bounds: `∏ t < 2 ∏ s`. -/
theorem prod_gt_of_bounds {d : ℕ} (hd : 1 ≤ d) {s t : Fin d → ℕ}
    (hb : ∀ i, AxisBounds d (s i) (t i)) (ht : ∀ i, 0 < t i) :
    ∏ i, t i < 2 * ∏ i, s i := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set c : ℝ := 1 - 1 / (2 * (d : ℝ))
  have hc0 : 0 < c := by
    have : 1 / (2 * (d : ℝ)) ≤ 1 / 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    simp only [c]; linarith
  have key : ∀ i ∈ (univ : Finset (Fin d)), c * t i < s i := by
    intro i _
    have h := (hb i).lower
    have h' : (2 * d * t i : ℝ) < 2 * d * s i + t i := by exact_mod_cast h
    have e : c * t i = (2 * d * t i - t i) / (2 * d) := by
      simp only [c]; field_simp
    rw [e, div_lt_iff₀ (by positivity)]
    linarith
  have hne : (univ : Finset (Fin d)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
  have hprod := prod_lt_prod_of_nonempty₀ (fun i _ => mul_pos hc0 (by exact_mod_cast ht i)) key hne
  rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin] at hprod
  have hB := bernoulli_half hd
  have hT : (0 : ℝ) ≤ ∏ i, (t i : ℝ) := Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
  have : (∏ i, (t i : ℝ)) < 2 * ∏ i, (s i : ℝ) := by nlinarith
  exact_mod_cast this

/-- **The moduli.** For `d ≥ 2`, any `a`, an odd `N` divisible by every odd prime below `4d`,
and `8 d² N + 4d ≤ 2^e`, the lengths `src d N a e` and `box d a e` are `Good`. -/
theorem src_good {d N a e : ℕ} (hd : 2 ≤ d) (hNo : Odd N)
    (hN : ∀ q, q.Prime → q ≠ 2 → q < 4 * d → q ∣ N)
    (hR : 8 * d ^ 2 * N + 4 * d ≤ 2 ^ e) : Good (src d N a e) (box d a e) := by
  have hN1 : 1 ≤ N := hNo.pos
  have hbd : ∀ i, AxisBounds d (src d N a e i) (box d a e i) := by
    intro i
    simp only [src, box, modulus, axisLen]
    split_ifs
    · exact modA_bounds (by omega) hN1 i.isLt hR
    · rw [pow_succ, mul_comm]
      exact modB_bounds hd hN1 (by omega) hR
  have hpos : ∀ i, 0 < box d a e i := by
    intro i; simp only [box, axisLen]; split_ifs <;> positivity
  have hlt : ∀ i, src d N a e i < box d a e i := fun i => (hbd i).lt (hpos i)
  refine ⟨fun i => modulus_odd hNo (start_even _ _ _) a i, hlt, ?_,
    modulus_pairwise hNo (start_even _ _ _) hN a, hbd, ?_, prod_gt_of_bounds (by omega) hbd hpos⟩
  · intro i
    have ho := modulus_odd hNo (start_even d N (2 ^ e)) a i
    simp only [src, box, axisLen]
    split_ifs
    · exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 ho)
    · exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 ho)
  · have hne : (univ : Finset (Fin d)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
    exact prod_lt_prod_of_nonempty₀ (fun i _ => (modulus_odd hNo (start_even _ _ _) a i).pos)
      (fun i _ => hlt i) hne

/-- The instance `N = oddProd d`. -/
theorem src_good_oddProd {d a e : ℕ} (hd : 2 ≤ d)
    (hR : 8 * d ^ 2 * oddProd d + 4 * d ≤ 2 ^ e) :
    Good (src d (oddProd d) a e) (box d a e) :=
  src_good hd (oddProd_odd d) prime_dvd_oddProd hR

end IntegerMultBounds.MathlibTM2.Mult.Moduli
