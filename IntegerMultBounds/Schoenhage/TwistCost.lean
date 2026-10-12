module

public import IntegerMultBounds.Schoenhage.PaperSigma
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The cost of a slot round's twist against the round budget `O(M r w)`. The
descriptor program spends `|table| · O(n + r)` per record; the table has at
most `D ℓ` entries and the address has `n ≤ D ℓ` bits, both at most a constant
times `w` on admissible instances (`d ℓ ≤ C_l p`, `p + 2 ≤ w`). The remaining
quadratic term `w²` fits once `w ≤ r`, which holds on every admissible instance
beyond a cutoff because `r = 2^ℓ ≥ 2^(a_r p / d)` with `d ≤ b_d p^ε`, `ε < 1`
(`eventually_w_le_r`). Then the whole twist is at most a constant times `M r w`
(`slotTwistCost_le`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Spec.SignedRingProduct TwistDescriptors Filter

/-- The step count of `runs_slotTwist` for `M` records. -/
def slotTwistCost (n r w M : ℕ) (es : List Entry) : ℕ :=
  M * (recordCost n r es [] + 2) + 1 + (M * (4 * r + 6) + 20 + M * (2 * r * (25 * w + 200) + 50 * r + 402))

/-- `slotTwistCost_le`: with at most `A w` address bits and table entries and `w ≤ r`, the twist of
a slot round costs at most `2200 (A + 1)² M r w + 21` steps. -/
theorem slotTwistCost_le {n r w M A : ℕ} {es : List Entry} (hn : n ≤ A * w) (hes : es.length ≤ A * w)
    (hr : 1 ≤ r) (hw : 1 ≤ w) (hwr : w ≤ r) :
    slotTwistCost n r w M es ≤ 2200 * (A + 1) ^ 2 * M * r * w + 21 := by
  unfold slotTwistCost recordCost
  simp only [List.length_nil, add_zero]
  have hrw : 1 ≤ r * w := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hA : 1 ≤ (A + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  set X := (A + 1) ^ 2 * (r * w) with hX
  have hX1 : 1 ≤ X := by rw [hX]; nlinarith
  have hrX : r ≤ X := by
    rw [hX]; calc r ≤ 1 * (r * w) := by nlinarith
      _ ≤ (A + 1) ^ 2 * (r * w) := Nat.mul_le_mul_right _ hA
  have hwX : (A + 1) * w ≤ X := by
    rw [hX]
    calc (A + 1) * w ≤ (A + 1) * (A + 1) * (r * w) := by
          apply Nat.mul_le_mul (by nlinarith) (by nlinarith)
      _ = (A + 1) ^ 2 * (r * w) := by ring
  have hnX : n ≤ X := by have : A * w ≤ (A + 1) * w := Nat.mul_le_mul_right _ (by omega); omega
  -- the per-record cost
  have h1 : es.length * (10 * n + 210 * r + 320) ≤ 540 * X := by
    have hn' : n ≤ (A + 1) * r := by
      have := Nat.mul_le_mul_left (A + 1) hwr
      have : A * w ≤ (A + 1) * w := Nat.mul_le_mul_right _ (by omega)
      omega
    calc es.length * (10 * n + 210 * r + 320)
        ≤ ((A + 1) * w) * (10 * ((A + 1) * r) + 210 * r + 320 * r) := by
          apply Nat.mul_le_mul
          · have : A * w ≤ (A + 1) * w := Nat.mul_le_mul_right _ (by omega)
            omega
          · nlinarith
      _ ≤ ((A + 1) * w) * (540 * (A + 1) * r) := by
          apply Nat.mul_le_mul_left; nlinarith
      _ = 540 * X := by rw [hX]; ring
  have hrec : es.length * (10 * n + 210 * r + 320) + 10 * n + 160 * r + 500 + 2 ≤ 1212 * X := by
    linarith
  -- the array monomial
  have h3 : (4 * r + 6) + (2 * r * (25 * w + 200) + 50 * r + 402) ≤ 912 * X := by
    have : (4 * r + 6) + (2 * r * (25 * w + 200) + 50 * r + 402) ≤ 912 * (r * w) := by nlinarith
    have : r * w ≤ X := by rw [hX]; exact Nat.le_mul_of_pos_left _ (by omega)
    linarith
  calc M * (es.length * (10 * n + 210 * r + 320) + 10 * n + 160 * r + 500 + 2) + 1 +
        (M * (4 * r + 6) + 20 + M * (2 * r * (25 * w + 200) + 50 * r + 402))
      = M * (es.length * (10 * n + 210 * r + 320) + 10 * n + 160 * r + 500 + 2) +
        M * ((4 * r + 6) + (2 * r * (25 * w + 200) + 50 * r + 402)) + 21 := by ring
    _ ≤ M * (1212 * X) + M * (912 * X) + 21 := by gcongr
    _ ≤ 2200 * (A + 1) ^ 2 * M * r * w + 21 := by rw [hX]; nlinarith

/-- The table of a slot round has one entry per participating axis and lower slot. -/
theorem length_slotTableP (ts : List ℕ) (ℓ K r : ℕ) (Is : List ℕ) (h : ℕ) :
    (slotTableP ts ℓ K r Is h).length = Is.length * h := by
  unfold slotTableP
  rw [List.length_flatMap]
  simp [List.sum_replicate, Nat.mul_comm]

/-- On admissible instances the address and every slot table fit `C_l w` (rounded up). -/
theorem admissible_size {P : TransformParams} {p d ℓ K w : ℕ} {ts : List ℕ}
    (h : Admissible P p d ℓ K w ts) : d * ℓ ≤ ⌈P.Cl⌉₊ * w := by
  obtain ⟨-, -, -, -, -, -, -, hdl, -, -, -, -, hpw, -⟩ := h
  have h1 : ((d * ℓ : ℕ) : ℝ) ≤ ⌈P.Cl⌉₊ * p := by
    have hdl' := hdl
    push_cast at hdl' ⊢
    refine hdl'.trans ?_
    have hp : (0 : ℝ) ≤ p := by positivity
    by_cases hc : 0 ≤ P.Cl
    · exact mul_le_mul_of_nonneg_right (Nat.le_ceil _) hp
    · push Not at hc
      nlinarith [Nat.cast_nonneg (α := ℝ) ⌈P.Cl⌉₊]
  have h2 : ((d * ℓ : ℕ) : ℝ) ≤ (⌈P.Cl⌉₊ * w : ℕ) := by
    have h1' := h1
    push_cast at h1' ⊢
    refine h1'.trans ?_
    gcongr
    exact_mod_cast (by omega : p ≤ w)
  exact_mod_cast h2

/-- Beyond a cutoff, admissible instances have `w ≤ r = 2^ℓ`. -/
theorem eventually_w_le_r (P : TransformParams) (hε : P.ε < 1) (har : 0 < P.ar) (hbd : 0 < P.bd) :
    ∃ p₁ : ℕ, ∀ p d ℓ K w ts, p₁ ≤ p → Admissible P p d ℓ K w ts → w ≤ 2 ^ ℓ := by
  set δ := 1 - P.ε with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set c := P.ar / P.bd with hc
  have hcpos : 0 < c := div_pos har hbd
  set Cw := ((P.Cw : ℝ) + 1) with hCw
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set κ := c * Real.log 2 / 2 with hκ
  have hκpos : 0 < κ := by positivity
  -- eventually log x ≤ κ x^δ and log Cw ≤ κ x^δ
  have e1 : ∀ᶠ x : ℝ in atTop, Real.log x ≤ κ * x ^ δ := by
    have := (isLittleO_log_rpow_atTop hδpos).bound hκpos
    filter_upwards [this, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl, abs_of_nonneg (by positivity)] at hx
    exact hx
  have e2 : ∀ᶠ x : ℝ in atTop, Real.log Cw ≤ κ * x ^ δ := by
    have := (tendsto_rpow_atTop hδpos).const_mul_atTop hκpos
    exact this.eventually_ge_atTop _
  obtain ⟨X, hX⟩ := (e1.and (e2.and (eventually_ge_atTop (1 : ℝ)))).exists_forall_of_atTop
  refine ⟨⌈X⌉₊, fun p d ℓ K w ts hp hadm => ?_⟩
  obtain ⟨had, hbd', har', -, hd2, -, -, -, -, -, -, -, -, hwp⟩ := hadm
  have hpX : X ≤ (p : ℝ) := (Nat.le_ceil X).trans (by exact_mod_cast hp)
  obtain ⟨hl1, hl2, hp1⟩ := hX p hpX
  have hp0 : (0 : ℝ) < p := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  -- `c p^δ ≤ a_r p / d`
  have hpe : (0 : ℝ) < (p : ℝ) ^ P.ε := Real.rpow_pos_of_pos hp0 _
  have hsplit : (p : ℝ) = (p : ℝ) ^ P.ε * (p : ℝ) ^ δ := by
    rw [← Real.rpow_add hp0, hδ, show P.ε + (1 - P.ε) = 1 by ring, Real.rpow_one]
  have hexp : c * (p : ℝ) ^ δ ≤ P.ar * p / d := by
    rw [le_div_iff₀ hd0, hc]
    calc P.ar / P.bd * (p : ℝ) ^ δ * d ≤ P.ar / P.bd * (p : ℝ) ^ δ * (P.bd * (p : ℝ) ^ P.ε) := by
          gcongr
      _ = P.ar * ((p : ℝ) ^ P.ε * (p : ℝ) ^ δ) := by field_simp
      _ = P.ar * p := by rw [← hsplit]
  -- `w ≤ (C_w + 1) p ≤ 2^(c p^δ) ≤ 2^ℓ`
  have hlogw : Real.log (Cw * p) ≤ c * (p : ℝ) ^ δ * Real.log 2 := by
    rw [Real.log_mul (by positivity) hp0.ne']
    have : κ * (p : ℝ) ^ δ + κ * (p : ℝ) ^ δ = c * (p : ℝ) ^ δ * Real.log 2 := by rw [hκ]; ring
    linarith
  have hw1 : (w : ℝ) ≤ Cw * p := by
    have : (w : ℝ) ≤ P.Cw * p := by exact_mod_cast hwp
    rw [hCw]; nlinarith
  have hw2 : Cw * p ≤ (2 : ℝ) ^ (c * (p : ℝ) ^ δ) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < Cw * p), Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    linarith
  have hw3 : (2 : ℝ) ^ (c * (p : ℝ) ^ δ) ≤ (2 : ℝ) ^ ((ℓ : ℕ) : ℝ) := by
    apply le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
    rw [Real.rpow_natCast]
    exact har'
  have : (w : ℝ) ≤ ((2 ^ ℓ : ℕ) : ℝ) := by
    push_cast
    rw [← Real.rpow_natCast]
    linarith
  exact_mod_cast this

end IntegerMultBounds.Schoenhage
