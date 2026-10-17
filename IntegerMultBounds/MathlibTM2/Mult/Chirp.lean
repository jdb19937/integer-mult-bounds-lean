module

public import IntegerMultBounds.MathlibTM2.Mult.ComplexConv
public import IntegerMultBounds.NLogN.ResamplingPermuted
public import IntegerMultBounds.Resampling.WeightTable
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Pi.Bounds
public import IntegerMultBounds.Machine

/-!
# The computed chirp kernel from axis tables

Paper §8, "Chirp and source-transform procedures". The kernel of the computed chirp transform
approximates `conj (chirpW t s j) = ∏_i conj (chirpS (t i) (s i) (j i))`; it is built from one
table per axis and a truncated product per tensor address. `chirpProd_ha'` is the hypothesis
`ha'` of `SourceErr.sourceErr_of_components` and `SourceErr.exact_product_of_components` for
`a' = chirpProd p g t s`.

Conventions as in `ComplexConv`: `Q_q` is `NLogN.rhoC q` (componentwise truncation toward zero
to `2^{-q} ℤ`). The table precision is `p + g` with `g` guard bits.

## Axis tables

* `chirpNum N s j`: `s j² mod 2N`, reduced exactly in `ℕ` and centered into `(-N, N]`;
  `conj_chirpS_eq`: `conj (chirpS N s j) = e^{-iπ·num/N}`.
* `angleNum`, `axisAngle`: with `P = p + g + 4` (`anglePrec`) and `piQ P ≈ 2^{5P} π`
  (Machin's formula, `Resampling.WeightTable.piQ`, error at most `100P + 1`), the integer
  `Y = ⌊piQ P · num / N⌋` and the angle `x = -Y/2^{5P}`; `axisAngle_err`:
  `2^{p+g+4} |x + π num/N| ≤ 1`.
* `axisTaylor`: `taylorExpI (p + g + 2 + gT) x nT` with `nT = p + g + 14` terms
  (`taylorTerms`) and `gT = ⌈log₂ nT⌉ + 4` Taylor guard bits (`taylorGuard`);
  `ComplexConv.taylorExpI_err` bounds its error by `(5/32) 2^{-(p+g)}`.
* `roundC q`: componentwise rounding to nearest on `2^{-q} ℤ`, error at most `(3/4) 2^{-q}`
  (`norm_roundC_sub_le`).
* `axisPhase p g N s j = roundC (p + g) (axisTaylor p g N s j)`. `axisPhase_spec`: on the
  `2^{-(p+g)}` grid, within `2^{-(p+g)}` of `conj (chirpS N s j)` (budget
  `3/4 + 5/32 + 1/16 = 31/32`), modulus at most `1 + 2^{-(p+g)}`. Valid for all `p, g, s` and
  `N ≠ 0`.

## Products

* `truncProd q [a₀, …, a_{d-1}] = Q_q(⋯Q_q(Q_q(a₀ a₁) a₂)⋯ a_{d-1})`, and `1` for `d = 0`.
  `norm_truncProd_ofFn_sub_le`: entries within `δ = 2^{-q}` of unit phases and `4dδ ≤ 1` give
  error at most `4dδ` (each step adds `√2 δ` for `Q_q` and `2δ` for the entry, the running
  product having modulus at most `2`).
* `chirpProd p g t s j = diskPhase p (truncProd (p + g) [axisPhase p g (t i) (s i) (j i)]ᵢ)`.
  `chirpProd_spec`: for `16 d ≤ 2^g` the truncated product is within `2^{-(p+2)}` of
  `conj (chirpW t s j)`, so `ComplexConv.diskPhase_spec` gives a disk-grid phase with
  `2^p ‖chirpProd j − conj (chirpW t s j)‖ < 2`.
* `chirpProd_ha'`: the hypothesis `ha'` verbatim, for `16 d ≤ 2^g`;
  `chirpProd_ha'_explicit`: the guard `g = chirpGuard d = ⌈log₂ d⌉ + 4`.

## Operation counts

* `axisTable p g N s : (Σ i, ZMod (N i)) → ℂ` collects the tables. `card_axisTable_dom`: they
  have `∑_i N i` entries; `axisTable_eq`: each is one `taylorExpI` with `p + g + 14` terms
  (`O(p)` terms for `g = O(log d)`) followed by one rounding.
* `chirpProd_eq_table`: `chirpProd` reads only table entries.
* `truncProdM` counts multiplications; `truncProdM_eq`: a list of length `ℓ` costs `ℓ − 1`.
  `chirpProd_mulCount`: `d − 1` truncated multiplications per tensor address, then one
  `diskPhase p`.
-/

@[expose] public section


open IntegerMultBounds IntegerMultBounds.NLogN Complex
open IntegerMultBounds.MathlibTM2.Mult.ComplexConv
open IntegerMultBounds.Resampling.WeightTable (piQ piQ_err fdiv_err)

namespace IntegerMultBounds.MathlibTM2.Mult.Chirp

/-! ### Exact numerator reduction -/

/-- The chirp numerator `s j² mod 2N`, reduced exactly in `ℕ` and centered into `(-N, N]`. -/
def chirpNum (N s : ℕ) (j : ZMod N) : ℤ :=
  if (s * j.val ^ 2) % (2 * N) ≤ N then (((s * j.val ^ 2) % (2 * N) : ℕ) : ℤ)
  else (((s * j.val ^ 2) % (2 * N) : ℕ) : ℤ) - 2 * N

theorem abs_chirpNum_le (N s : ℕ) [NeZero N] (j : ZMod N) : |chirpNum N s j| ≤ N := by
  have hN := NeZero.pos N
  have hlt : (s * j.val ^ 2) % (2 * N) < 2 * N := Nat.mod_lt _ (by omega)
  unfold chirpNum
  generalize (s * j.val ^ 2) % (2 * N) = m at hlt ⊢
  split_ifs with h
  · rw [abs_le]; constructor <;> omega
  · rw [abs_le]; constructor <;> omega

theorem chirpNum_cong (N s : ℕ) (j : ZMod N) :
    ∃ k : ℤ, (s : ℤ) * (j.val : ℤ) ^ 2 = chirpNum N s j + 2 * N * k := by
  have h := Nat.mod_add_div (s * j.val ^ 2) (2 * N)
  have hc : (s : ℤ) * (j.val : ℤ) ^ 2 = ((s * j.val ^ 2 : ℕ) : ℤ) := by push_cast; ring
  unfold chirpNum
  rw [hc]
  generalize s * j.val ^ 2 = x at h ⊢
  generalize x % (2 * N) = m at h ⊢
  generalize x / (2 * N) = q at h ⊢
  subst h
  split_ifs
  · exact ⟨q, by push_cast; ring⟩
  · exact ⟨q + 1, by push_cast; ring⟩

/-- `conj (chirpS N s j) = e^{-iπ·num/N}` with the reduced numerator `num = chirpNum N s j`. -/
theorem conj_chirpS_eq (N s : ℕ) [NeZero N] (j : ZMod N) :
    starRingEnd ℂ (chirpS N s j) =
      Complex.exp (((-(Real.pi * chirpNum N s j / N)) : ℝ) * I) := by
  obtain ⟨k, hk⟩ := chirpNum_cong N s j
  unfold chirpS
  rw [hk, chirpExp_add_mul, chirpExp_conj]
  unfold chirpExp
  congr 1
  push_cast
  ring

theorem norm_conj_chirpS (N s : ℕ) [NeZero N] (j : ZMod N) :
    ‖starRingEnd ℂ (chirpS N s j)‖ = 1 := by
  rw [conj_chirpS_eq]
  exact Complex.norm_exp_ofReal_mul_I _

/-! ### The angle -/

/-- Angle precision `P = p + g + 4`; the angle lies on `2^{-5P} ℤ`. -/
def anglePrec (p g : ℕ) : ℕ := p + g + 4

/-- `Y = ⌊piQ P · num / N⌋ ≈ 2^{5P} π num / N`, with `piQ P ≈ 2^{5P} π` from Machin's
formula (`Resampling.WeightTable.piQ`). -/
def angleNum (p g N s : ℕ) (j : ZMod N) : ℤ :=
  (piQ (anglePrec p g) * chirpNum N s j) / N

/-- The computed angle `x = -Y / 2^{5P} ≈ -π num / N`. -/
noncomputable def axisAngle (p g N s : ℕ) (j : ZMod N) : ℝ :=
  -((angleNum p g N s j : ℝ) / 2 ^ (5 * anglePrec p g))

theorem lin_le_pow_four (P : ℕ) (hP : 2 ≤ P) : 100 * P + 2 ≤ 2 ^ (4 * P) := by
  induction P, hP using Nat.le_induction with
  | base => norm_num
  | succ n _ ih => rw [show 4 * (n + 1) = 4 * n + 4 by ring, pow_add]; omega

/-- The angle is within `2^{-(p+g+4)}` of `-π num / N`. -/
theorem axisAngle_err (p g N s : ℕ) [NeZero N] (j : ZMod N) :
    2 ^ (p + g + 4) * |axisAngle p g N s j - (-(Real.pi * chirpNum N s j / N))| ≤ 1 := by
  have hPdef : anglePrec p g = p + g + 4 := rfl
  set P := anglePrec p g with hP
  rw [← hPdef]
  have hP2 : 2 ≤ P := by omega
  set c : ℤ := chirpNum N s j with hc
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hcN : |(c : ℝ)| ≤ N := by exact_mod_cast abs_chirpNum_le N s j
  have h1 := fdiv_err (piQ P * c) N (by exact_mod_cast NeZero.pos N)
  have h2 := piQ_err P (by omega)
  have hcN1 : |(c : ℝ) / N| ≤ 1 := by
    rw [abs_div, abs_of_pos hN, div_le_one hN]; exact hcN
  have h3 : |(angleNum p g N s j : ℝ) - 2 ^ (5 * P) * Real.pi * c / N| ≤ 100 * P + 2 := by
    have e : (angleNum p g N s j : ℝ) - 2 ^ (5 * P) * Real.pi * c / N =
        ((((piQ P * c / N : ℤ) : ℝ)) - ((piQ P * c : ℤ) : ℝ) / ((N : ℤ) : ℝ)) +
          ((c : ℝ) / N) * ((piQ P : ℝ) - 2 ^ (5 * P) * Real.pi) := by
      unfold angleNum
      rw [← hP]
      push_cast
      field_simp
      ring
    rw [e]
    have h4 : |(c : ℝ) / N * ((piQ P : ℝ) - 2 ^ (5 * P) * Real.pi)| ≤ 1 * (20 * (5 * P) + 1) := by
      rw [abs_mul]
      exact mul_le_mul hcN1 h2 (abs_nonneg _) zero_le_one
    calc _ ≤ |(((piQ P * c / N : ℤ) : ℝ)) - ((piQ P * c : ℤ) : ℝ) / ((N : ℤ) : ℝ)| +
          |(c : ℝ) / N * ((piQ P : ℝ) - 2 ^ (5 * P) * Real.pi)| := abs_add_le _ _
      _ ≤ 1 + 1 * (20 * (5 * P) + 1) := add_le_add h1 h4
      _ = 100 * P + 2 := by ring
  have hpow : (100 * (P : ℝ) + 2) ≤ 2 ^ (4 * P) := by exact_mod_cast lin_le_pow_four P hP2
  have e2 : axisAngle p g N s j - (-(Real.pi * c / N)) =
      -(((angleNum p g N s j : ℝ) - 2 ^ (5 * P) * Real.pi * c / N) / 2 ^ (5 * P)) := by
    unfold axisAngle
    rw [← hP]
    field_simp
    ring
  have h5 : (2 : ℝ) ^ (5 * P) = 2 ^ P * 2 ^ (4 * P) := by rw [← pow_add]; ring_nf
  rw [e2, abs_neg, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (5 * P))]
  set A := |(angleNum p g N s j : ℝ) - 2 ^ (5 * P) * Real.pi * c / N| with hA
  rw [h5, mul_div_assoc', div_le_one (by positivity)]
  have : (0 : ℝ) < 2 ^ P := by positivity
  nlinarith

/-! ### Rounding to nearest -/

/-- Componentwise rounding to nearest on `2^{-q} ℤ`. -/
noncomputable def roundC (q : ℕ) (z : ℂ) : ℂ :=
  ⟨(round (2 ^ q * z.re) : ℝ) / 2 ^ q, (round (2 ^ q * z.im) : ℝ) / 2 ^ q⟩

theorem isFixed_roundC (q : ℕ) (z : ℂ) : IsFixed q (roundC q z) := ⟨_, _, rfl⟩

/-- Rounding to nearest moves a complex number by at most `(√2/2) 2^{-q} < (3/4) 2^{-q}`. -/
theorem norm_roundC_sub_le (q : ℕ) (z : ℂ) : 2 ^ q * ‖roundC q z - z‖ ≤ 3 / 4 := by
  have hq : (0 : ℝ) < 2 ^ q := by positivity
  have hre : |2 ^ q * (roundC q z - z).re| ≤ 1 / 2 := by
    have e : 2 ^ q * (roundC q z - z).re = (round (2 ^ q * z.re) : ℝ) - 2 ^ q * z.re := by
      simp only [Complex.sub_re, roundC]
      field_simp
    rw [e, abs_sub_comm]
    exact abs_sub_round _
  have him : |2 ^ q * (roundC q z - z).im| ≤ 1 / 2 := by
    have e : 2 ^ q * (roundC q z - z).im = (round (2 ^ q * z.im) : ℝ) - 2 ^ q * z.im := by
      simp only [Complex.sub_im, roundC]
      field_simp
    rw [e, abs_sub_comm]
    exact abs_sub_round _
  have a1 : (2 ^ q * (roundC q z - z).re) ^ 2 ≤ 1 / 4 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (2 ^ q * (roundC q z - z).re)]
  have a2 : (2 ^ q * (roundC q z - z).im) ^ 2 ≤ 1 / 4 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (2 ^ q * (roundC q z - z).im)]
  have hsq : (2 ^ q * ‖roundC q z - z‖) ^ 2 ≤ 1 / 2 := by
    rw [mul_pow, Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  have h0 : 0 ≤ 2 ^ q * ‖roundC q z - z‖ := by positivity
  nlinarith

/-! ### Axis tables -/

/-- Taylor terms per axis entry: `nT = p + g + 14`. -/
def taylorTerms (p g : ℕ) : ℕ := p + g + 14

/-- Taylor guard bits `gT = ⌈log₂ nT⌉ + 4`, so that `16 nT ≤ 2^gT`. -/
def taylorGuard (p g : ℕ) : ℕ := Nat.clog 2 (taylorTerms p g) + 4

theorem sixteen_taylorTerms_le (p g : ℕ) : 16 * taylorTerms p g ≤ 2 ^ taylorGuard p g := by
  unfold taylorGuard
  rw [pow_add]
  have := Nat.le_pow_clog (b := 2) (by norm_num) (taylorTerms p g)
  omega

/-- The fixed-point Taylor sum of `e^{ix}` for the computed angle, at `p + g + 2 + gT` bits. -/
noncomputable def axisTaylor (p g N s : ℕ) (j : ZMod N) : ℂ :=
  taylorExpI (p + g + 2 + taylorGuard p g) (axisAngle p g N s j) (taylorTerms p g)

/-- The table entry for `conj (chirpS N s j)` at `p + g` bits. -/
noncomputable def axisPhase (p g N s : ℕ) (j : ZMod N) : ℂ :=
  roundC (p + g) (axisTaylor p g N s j)

theorem abs_axisAngle_le (p g N s : ℕ) [NeZero N] (j : ZMod N) : |axisAngle p g N s j| ≤ 4 := by
  have h := axisAngle_err p g N s j
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hcN : |(chirpNum N s j : ℝ)| ≤ N := by exact_mod_cast abs_chirpNum_le N s j
  have h16 : (16 : ℝ) ≤ 2 ^ (p + g + 4) :=
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (p + g + 4) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hd : |axisAngle p g N s j - (-(Real.pi * chirpNum N s j / N))| ≤ 1 / 16 := by
    have := abs_nonneg (axisAngle p g N s j - (-(Real.pi * chirpNum N s j / N)))
    nlinarith
  have hx0 : |(-(Real.pi * chirpNum N s j / N))| ≤ Real.pi := by
    rw [abs_neg, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hN, div_le_iff₀ hN]
    exact mul_le_mul_of_nonneg_left hcN Real.pi_pos.le
  have hpi := Real.pi_lt_d2
  have := abs_sub_abs_le_abs_sub (axisAngle p g N s j) (-(Real.pi * chirpNum N s j / N))
  linarith

/-- The axis table entry is within `2^{-(p+g)}` of the conjugate chirp factor:
`3/4` (rounding) `+ 5/32` (Taylor) `+ 1/16` (angle) `≤ 1` in units of `2^{-(p+g)}`. -/
theorem axisPhase_err (p g N s : ℕ) [NeZero N] (j : ZMod N) :
    2 ^ (p + g) * ‖axisPhase p g N s j - starRingEnd ℂ (chirpS N s j)‖ ≤ 1 := by
  set x := axisAngle p g N s j with hx
  set x0 : ℝ := -(Real.pi * chirpNum N s j / N) with hx0
  have hA : 2 ^ (p + g + 4) * |x - x0| ≤ 1 := axisAngle_err p g N s j
  have hT : 2 ^ (p + g + 2) * ‖axisTaylor p g N s j - Complex.exp (x * I)‖ ≤ 5 / 8 :=
    taylorExpI_err (abs_axisAngle_le p g N s j) (by unfold taylorTerms; omega)
      (sixteen_taylorTerms_le p g)
  have hR := norm_roundC_sub_le (p + g) (axisTaylor p g N s j)
  have hE : ‖Complex.exp (x * I) - Complex.exp (x0 * I)‖ ≤ |x - x0| :=
    norm_exp_mul_I_sub_le x x0
  have hpg : (0 : ℝ) < 2 ^ (p + g) := by positivity
  have e2 : (2 : ℝ) ^ (p + g + 2) = 2 ^ (p + g) * 4 := by rw [pow_add]; norm_num
  have e4 : (2 : ℝ) ^ (p + g + 4) = 2 ^ (p + g) * 16 := by rw [pow_add]; norm_num
  rw [e2] at hT
  rw [e4] at hA
  rw [conj_chirpS_eq, ← hx0]
  unfold axisPhase
  calc 2 ^ (p + g) * ‖roundC (p + g) (axisTaylor p g N s j) - Complex.exp (x0 * I)‖
      ≤ 2 ^ (p + g) * ‖roundC (p + g) (axisTaylor p g N s j) - axisTaylor p g N s j‖ +
        2 ^ (p + g) * ‖axisTaylor p g N s j - Complex.exp (x * I)‖ +
        2 ^ (p + g) * ‖Complex.exp (x * I) - Complex.exp (x0 * I)‖ := by
        rw [← mul_add, ← mul_add]
        gcongr
        refine (norm_sub_le_norm_sub_add_norm_sub _ (axisTaylor p g N s j) _).trans ?_
        rw [add_assoc]
        gcongr
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 3 / 4 + 5 / 32 + 1 / 16 := by
        gcongr
        · nlinarith [norm_nonneg (axisTaylor p g N s j - Complex.exp (x * I))]
        · nlinarith [abs_nonneg (x - x0)]
    _ ≤ 1 := by norm_num

/-- Deliverable form: `axisPhase` lies on the `2^{-(p+g)}` grid, is within `2^{-(p+g)}` of
`conj (chirpS N s j)`, and has modulus at most `1 + 2^{-(p+g)}`. -/
theorem axisPhase_spec (p g N s : ℕ) [NeZero N] (j : ZMod N) :
    IsFixed (p + g) (axisPhase p g N s j) ∧
      ‖axisPhase p g N s j - starRingEnd ℂ (chirpS N s j)‖ ≤ 1 / 2 ^ (p + g) ∧
      ‖axisPhase p g N s j‖ ≤ 1 + 1 / 2 ^ (p + g) := by
  have hpg : (0 : ℝ) < 2 ^ (p + g) := by positivity
  have h : ‖axisPhase p g N s j - starRingEnd ℂ (chirpS N s j)‖ ≤ 1 / 2 ^ (p + g) := by
    rw [le_div_iff₀ hpg, mul_comm]; exact axisPhase_err p g N s j
  refine ⟨isFixed_roundC _ _, h, ?_⟩
  have := norm_le_norm_sub_add (axisPhase p g N s j) (starRingEnd ℂ (chirpS N s j))
  rw [norm_conj_chirpS] at this
  linarith

/-! ### Truncated products -/

/-- The left-to-right product truncated to `2^{-q} ℤ` after each multiplication,
`[a₀, a₁, …, a_{d-1}] ↦ Q_q(⋯Q_q(Q_q(a₀ a₁) a₂)⋯ a_{d-1})`, and `1` for the empty list. -/
noncomputable def truncProd (q : ℕ) : List ℂ → ℂ
  | [] => 1
  | a :: l => l.foldl (fun acc b => rhoC q (acc * b)) a

/-- One truncated multiplication by an entry within `2^{-q}` of a unit phase adds at most
`4·2^{-q}` to the error, while the running product has modulus at most `2`. -/
theorem foldl_truncProd_err (q : ℕ) :
    ∀ (l : List (ℂ × ℂ)) (acc E : ℂ) (ε : ℝ), ‖acc - E‖ ≤ ε → ‖E‖ = 1 →
      (∀ x ∈ l, ‖x.1 - x.2‖ ≤ 1 / 2 ^ q ∧ ‖x.2‖ = 1) →
      ε + 4 * l.length / 2 ^ q ≤ 1 →
      ‖(l.map Prod.fst).foldl (fun acc b => rhoC q (acc * b)) acc -
          E * (l.map Prod.snd).prod‖ ≤ ε + 4 * l.length / 2 ^ q
  | [], acc, E, ε, h, _, _, _ => by simpa using h
  | x :: l, acc, E, ε, h, hE, hl, hlen => by
      have hq : (0 : ℝ) < 2 ^ q := by positivity
      have hx := hl x (by simp)
      have hl' : ∀ y ∈ l, ‖y.1 - y.2‖ ≤ 1 / 2 ^ q ∧ ‖y.2‖ = 1 :=
        fun y hy => hl y (List.mem_cons_of_mem _ hy)
      simp only [List.map_cons, List.foldl_cons, List.prod_cons, List.length_cons] at hlen ⊢
      push_cast at hlen
      have hlen0 : (0 : ℝ) ≤ 4 * (l.length : ℝ) / 2 ^ q := by positivity
      have hε1 : ε ≤ 1 := by
        have : (0 : ℝ) ≤ 4 * ((l.length : ℝ) + 1) / 2 ^ q := by positivity
        linarith
      have hacc : ‖acc‖ ≤ 2 := by
        have := norm_le_norm_sub_add acc E
        linarith
      have hstep : ‖rhoC q (acc * x.1) - E * x.2‖ ≤ ε + 4 / 2 ^ q := by
        have e : rhoC q (acc * x.1) - E * x.2 =
            (rhoC q (acc * x.1) - acc * x.1) + (acc * (x.1 - x.2) + (acc - E) * x.2) := by ring
        rw [e]
        have h1 := norm_rhoC_sub_le_two q (acc * x.1)
        have h2 : ‖acc * (x.1 - x.2)‖ ≤ 2 * (1 / 2 ^ q) := by
          rw [norm_mul]; exact mul_le_mul hacc hx.1 (norm_nonneg _) zero_le_two
        have h3 : ‖(acc - E) * x.2‖ ≤ ε := by rw [norm_mul, hx.2, mul_one]; exact h
        calc _ ≤ ‖rhoC q (acc * x.1) - acc * x.1‖ + (‖acc * (x.1 - x.2)‖ + ‖(acc - E) * x.2‖) :=
              (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
          _ ≤ 2 / 2 ^ q + (2 * (1 / 2 ^ q) + ε) := by gcongr
          _ = ε + 4 / 2 ^ q := by ring
      have hrec := foldl_truncProd_err q l (rhoC q (acc * x.1)) (E * x.2) (ε + 4 / 2 ^ q) hstep
        (by rw [norm_mul, hE, hx.2, one_mul]) hl' (by
          have : ε + 4 / 2 ^ q + 4 * (l.length : ℝ) / 2 ^ q = ε + 4 * ((l.length : ℝ) + 1) / 2 ^ q := by
            ring
          rw [this]; exact hlen)
      rw [← mul_assoc]
      refine hrec.trans (le_of_eq ?_)
      push_cast
      ring

/-- Entries within `δ = 2^{-q}` of unit phases and `4|l|δ ≤ 1`: the truncated product is within
`4|l|δ` of the exact product. -/
theorem norm_truncProd_sub_le (q : ℕ) (l : List (ℂ × ℂ))
    (hl : ∀ x ∈ l, ‖x.1 - x.2‖ ≤ 1 / 2 ^ q ∧ ‖x.2‖ = 1) (hlen : (4 * l.length / 2 ^ q : ℝ) ≤ 1) :
    ‖truncProd q (l.map Prod.fst) - (l.map Prod.snd).prod‖ ≤ 4 * l.length / 2 ^ q := by
  cases l with
  | nil => simp [truncProd]
  | cons x l =>
    have hx := hl x (by simp)
    have hl' : ∀ y ∈ l, ‖y.1 - y.2‖ ≤ 1 / 2 ^ q ∧ ‖y.2‖ = 1 :=
      fun y hy => hl y (List.mem_cons_of_mem _ hy)
    simp only [List.map_cons, truncProd, List.prod_cons, List.length_cons] at hlen ⊢
    push_cast at hlen ⊢
    have hq : (0 : ℝ) < 2 ^ q := by positivity
    have e : 1 / 2 ^ q + 4 * (l.length : ℝ) / 2 ^ q ≤ 4 * ((l.length : ℝ) + 1) / 2 ^ q := by
      rw [← add_div, div_le_div_iff_of_pos_right hq]; linarith
    exact (foldl_truncProd_err q l x.1 x.2 (1 / 2 ^ q) hx.1 hx.2 hl' (e.trans hlen)).trans e

/-- The same for `d` entries indexed by `Fin d`. -/
theorem norm_truncProd_ofFn_sub_le {d : ℕ} (q : ℕ) (a e : Fin d → ℂ)
    (ha : ∀ i, ‖a i - e i‖ ≤ 1 / 2 ^ q) (he : ∀ i, ‖e i‖ = 1) (hd : (4 * d / 2 ^ q : ℝ) ≤ 1) :
    ‖truncProd q (List.ofFn a) - ∏ i, e i‖ ≤ 4 * d / 2 ^ q := by
  have h := norm_truncProd_sub_le q (List.ofFn fun i => (a i, e i)) (by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact ⟨ha i, he i⟩) (by rw [List.length_ofFn]; exact hd)
  simpa [List.map_ofFn, List.prod_ofFn, Function.comp_def] using h

/-! ### The chirp kernel -/

/-- The computed kernel entry at tensor address `j`: the `d` axis table entries multiplied left
to right with `Q_{p+g}` after each multiplication, then rounded to the `p`-bit disk by
`diskPhase p`. -/
noncomputable def chirpProd (p g : ℕ) {d : ℕ} (t s : Fin d → ℕ)
    (j : (i : Fin d) → ZMod (t i)) : ℂ :=
  diskPhase p (truncProd (p + g) (List.ofFn fun i => axisPhase p g (t i) (s i) (j i)))

/-- For `16 d ≤ 2^g`, `chirpProd` is a disk-grid phase within `2·2^{-p}` of
`conj (chirpW t s j)`. -/
theorem chirpProd_spec {d : ℕ} (t s : Fin d → ℕ) [∀ i, NeZero (t i)] {p g : ℕ}
    (hg : 16 * d ≤ 2 ^ g) (j : (i : Fin d) → ZMod (t i)) :
    IsFixed p (chirpProd p g t s j) ∧ ‖chirpProd p g t s j‖ ≤ 1 ∧
      2 ^ p * ‖chirpProd p g t s j - starRingEnd ℂ (chirpW t s j)‖ < 2 := by
  have he : starRingEnd ℂ (chirpW t s j) = ∏ i, starRingEnd ℂ (chirpS (t i) (s i) (j i)) := by
    unfold chirpW; rw [map_prod]
  have hn : ∀ i, ‖starRingEnd ℂ (chirpS (t i) (s i) (j i))‖ = 1 := fun i => norm_conj_chirpS _ _ _
  have hd16 : (16 * d : ℝ) ≤ 2 ^ g := by exact_mod_cast hg
  have hg0 : (0 : ℝ) < 2 ^ g := by positivity
  have hp0 : (0 : ℝ) < 2 ^ p := by positivity
  have hd : (4 * d / 2 ^ (p + g) : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity), pow_add]
    have : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
    nlinarith
  have hP := norm_truncProd_ofFn_sub_le (p + g) (fun i => axisPhase p g (t i) (s i) (j i))
    (fun i => starRingEnd ℂ (chirpS (t i) (s i) (j i))) (fun i => (axisPhase_spec _ _ _ _ _).2.1)
    hn hd
  have hE1 : ‖starRingEnd ℂ (chirpW t s j)‖ = 1 := by
    rw [he, norm_prod]; exact Finset.prod_eq_one fun i _ => hn i
  unfold chirpProd
  apply diskPhase_spec hE1
  rw [he]
  calc 2 ^ (p + 2) * ‖truncProd (p + g) (List.ofFn fun i => axisPhase p g (t i) (s i) (j i)) -
        ∏ i, starRingEnd ℂ (chirpS (t i) (s i) (j i))‖
      ≤ 2 ^ (p + 2) * (4 * d / 2 ^ (p + g)) := by gcongr
    _ = 16 * d / 2 ^ g := by rw [pow_add, pow_add]; field_simp; ring
    _ ≤ 1 := by rw [div_le_one hg0]; exact hd16

/-- The hypothesis `ha'` of `SourceErr.sourceErr_of_components` and
`SourceErr.exact_product_of_components` for `a' = chirpProd p g t s`, when `16 d ≤ 2^g`. -/
theorem chirpProd_ha' {d : ℕ} (t s : Fin d → ℕ) [∀ i, NeZero (t i)] {p g : ℕ}
    (hg : 16 * d ≤ 2 ^ g) :
    ∀ j, 2 ^ p * ‖chirpProd p g t s j - starRingEnd ℂ (chirpW t s j)‖ ≤ 2 ∧
      ‖chirpProd p g t s j‖ ≤ 1 := fun j =>
  ⟨(chirpProd_spec t s hg j).2.2.le, (chirpProd_spec t s hg j).2.1⟩

/-- The explicit product guard `g = ⌈log₂ d⌉ + 4`. -/
def chirpGuard (d : ℕ) : ℕ := Nat.clog 2 d + 4

theorem sixteen_mul_le_chirpGuard (d : ℕ) : 16 * d ≤ 2 ^ chirpGuard d := by
  unfold chirpGuard
  rw [pow_add]
  have := Nat.le_pow_clog (b := 2) (by norm_num) d
  omega

/-- `ha'` with the explicit guard `g = ⌈log₂ d⌉ + 4`. -/
theorem chirpProd_ha'_explicit {d : ℕ} (t s : Fin d → ℕ) [∀ i, NeZero (t i)] (p : ℕ) :
    ∀ j, 2 ^ p * ‖chirpProd p (chirpGuard d) t s j - starRingEnd ℂ (chirpW t s j)‖ ≤ 2 ∧
      ‖chirpProd p (chirpGuard d) t s j‖ ≤ 1 :=
  chirpProd_ha' t s (sixteen_mul_le_chirpGuard d)

/-! ### Operation counts -/

/-- All axis tables together, indexed by `Σ i, ZMod (N i)`. -/
noncomputable def axisTable (p g : ℕ) {d : ℕ} (N s : Fin d → ℕ) :
    (Σ i : Fin d, ZMod (N i)) → ℂ :=
  fun x => axisPhase p g (N x.1) (s x.1) x.2

/-- The tables have `∑_i N i` entries. -/
theorem card_axisTable_dom {d : ℕ} (N : Fin d → ℕ) [∀ i, NeZero (N i)] :
    Fintype.card (Σ i : Fin d, ZMod (N i)) = ∑ i, N i := by
  rw [Fintype.card_sigma]
  simp only [ZMod.card]

/-- Each table entry is one rounded Taylor evaluation with `taylorTerms p g = p + g + 14`
terms. -/
theorem axisTable_eq {d : ℕ} (p g : ℕ) (N s : Fin d → ℕ) (x : Σ i : Fin d, ZMod (N i)) :
    axisTable p g N s x = roundC (p + g) (taylorExpI (p + g + 2 + taylorGuard p g)
      (axisAngle p g (N x.1) (s x.1) x.2) (taylorTerms p g)) := rfl

/-- `chirpProd` reads only table entries. -/
theorem chirpProd_eq_table {d : ℕ} (p g : ℕ) (t s : Fin d → ℕ) (j : (i : Fin d) → ZMod (t i)) :
    chirpProd p g t s j =
      diskPhase p (truncProd (p + g) (List.ofFn fun i => axisTable p g t s ⟨i, j i⟩)) := rfl

/-- `truncProd` with a counter of the multiplications. -/
noncomputable def truncProdM (q : ℕ) : List ℂ → ℂ × ℕ
  | [] => (1, 0)
  | a :: l => l.foldl (fun acc b => (rhoC q (acc.1 * b), acc.2 + 1)) (a, 0)

theorem foldl_truncProdM (q : ℕ) : ∀ (l : List ℂ) (a : ℂ) (n : ℕ),
    l.foldl (fun acc b => (rhoC q (acc.1 * b), acc.2 + 1)) (a, n) =
      (l.foldl (fun acc b => rhoC q (acc * b)) a, n + l.length)
  | [], a, n => rfl
  | b :: l, a, n => by
      simp only [List.foldl_cons, List.length_cons]
      rw [foldl_truncProdM q l]
      congr 1
      omega

/-- `truncProd` performs `|l| - 1` multiplications. -/
theorem truncProdM_eq (q : ℕ) (l : List ℂ) : truncProdM q l = (truncProd q l, l.length - 1) := by
  cases l with
  | nil => rfl
  | cons a l =>
    simp only [truncProdM, truncProd, foldl_truncProdM, List.length_cons]
    congr 1
    omega

/-- Each kernel entry costs `d - 1` truncated multiplications, then one `diskPhase p`. -/
theorem chirpProd_mulCount {d : ℕ} (p g : ℕ) (t s : Fin d → ℕ) (j : (i : Fin d) → ZMod (t i)) :
    (truncProdM (p + g) (List.ofFn fun i => axisPhase p g (t i) (s i) (j i))).2 = d - 1 := by
  rw [truncProdM_eq, List.length_ofFn]

end IntegerMultBounds.MathlibTM2.Mult.Chirp
