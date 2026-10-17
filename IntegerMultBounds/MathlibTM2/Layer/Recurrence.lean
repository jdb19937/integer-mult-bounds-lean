module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Tactic

/-!
# The normalized cost recurrence of a simultaneous butterfly layer

Real-number bounds for the unrolled layer recurrence of §5 ("Where the rows come from",
"Unrolling the recurrence", and the cost part of `prop:simultaneous-layer`). Nothing here
refers to a machine: the cost of a piece is an arbitrary function `G : ℕ → ℝ` of the base-`m`
exponent of its chunk count, constrained only by the recurrence inequalities.

A network invocation on `e` selected chunks makes `s` child calls on `e/m` chunks, each on a
role stream of volume `1/W` of its parent, so the volume-normalized cost obeys
`F(e) ≤ a F(e/m) + C₁((e K)^τ + 1)` with `a = s/W`, and `F(e) ≤ C₀ e` at a leaf.

* `unroll_geom`, `cost_invariant`: the geometric-series unrolling.
* `recurrence_closed` (deliverable 1): for `max(τ, log_m a) < λ`,
  `F j ≤ C (m^j u)^λ K^τ + C a^j u` with `C = recConst a m λ C₀ C₁`.
* `leaf_le` (deliverable 2): `a ≤ m^σ` gives `a^j u ≤ (m^j u)^σ u^(1-σ)`.
* `layer_total_le`, `layer_total_le_absorbed`, `layer_cost_le` (deliverable 3): base-`m` digit
  pieces of `D' ≤ d` chunks plus `q₀ ≤ Q (1 + log_m d)` preprocessing kernels cost at most
  `C' (1 + log_m d) (d^λ K^τ + d^(σ+β(1-σ)) + 1)`; with `K ≤ d^c` and `τ(1 + c/β) ≤ λ` the
  factor `K^τ` is absorbed node by node, giving `C' (1 + log_m d)(d^λ + d^(σ+β(1-σ)) + 1)`
  and `layerConst · d^λ'` for every `d ≥ 1`.
* `layer_cost_bound` (deliverable 4): one constant for all `d`, `K`, cutoffs, piece costs and
  piece decompositions.

The paper's choice is `β = 1/2`; the statements hold for every `β > 0`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Layer.Recurrence

open Finset

/-! ### Two geometric unrollings -/

private theorem geom_step {a x D : ℝ} (hax : a < x) (i : ℕ) :
    a * (D * x / (x - a) * x ^ i) + D * x ^ (i + 1) = D * x / (x - a) * x ^ (i + 1) := by
  have hxa : x - a ≠ 0 := (sub_pos.mpr hax).ne'
  field_simp
  ring

/-- `F 0 ≤ L` and `F (i+1) ≤ a F i + D x^(i+1)` with `0 ≤ a < x`, `0 ≤ D` unroll to
`F i ≤ D x / (x - a) · x^i + L a^i`. -/
theorem unroll_geom {F : ℕ → ℝ} {a x D L : ℝ} (ha : 0 ≤ a) (hax : a < x) (hD : 0 ≤ D)
    (h0 : F 0 ≤ L) (hs : ∀ i, F (i + 1) ≤ a * F i + D * x ^ (i + 1)) :
    ∀ i, F i ≤ D * x / (x - a) * x ^ i + L * a ^ i := by
  have hx : 0 < x := lt_of_le_of_lt ha hax
  have hA : 0 ≤ D * x / (x - a) := div_nonneg (mul_nonneg hD hx.le) (sub_pos.mpr hax).le
  intro i
  induction i with
  | zero => simp only [pow_zero, mul_one]; linarith
  | succ i ih =>
    calc F (i + 1) ≤ a * F i + D * x ^ (i + 1) := hs i
      _ ≤ a * (D * x / (x - a) * x ^ i + L * a ^ i) + D * x ^ (i + 1) := by gcongr
      _ = D * x / (x - a) * x ^ (i + 1) + L * a ^ (i + 1) := by
        rw [← geom_step hax i]; ring

/-- Each exponent `j` is either a leaf, `G j ≤ C₀ y^j Y`, or an internal node
`G (i+1) ≤ a G i + D x^(i+1)`. With `0 ≤ a < x` and `a ≤ y` this gives
`G j ≤ D x / (x - a) · x^j + C₀ y^j Y` for every `j`. -/
theorem cost_invariant {G : ℕ → ℝ} {a x y D C₀ Y : ℝ} (ha : 0 ≤ a) (hax : a < x) (hay : a ≤ y)
    (hD : 0 ≤ D) (hC₀ : 0 ≤ C₀) (hY : 0 ≤ Y)
    (hG : ∀ j, G j ≤ C₀ * y ^ j * Y ∨ ∃ i, j = i + 1 ∧ G j ≤ a * G i + D * x ^ j) :
    ∀ j, G j ≤ D * x / (x - a) * x ^ j + C₀ * y ^ j * Y := by
  have hx : 0 < x := lt_of_le_of_lt ha hax
  have hy : 0 ≤ y := ha.trans hay
  have hA : 0 ≤ D * x / (x - a) := div_nonneg (mul_nonneg hD hx.le) (sub_pos.mpr hax).le
  intro j
  induction j with
  | zero =>
    rcases hG 0 with h | ⟨i, hi, _⟩
    · have : 0 ≤ D * x / (x - a) * x ^ 0 := by positivity
      linarith
    · omega
  | succ j ih =>
    rcases hG (j + 1) with h | ⟨i, hi, h⟩
    · have : 0 ≤ D * x / (x - a) * x ^ (j + 1) := by positivity
      linarith
    · have hij : i = j := by omega
      subst hij
      have h1 : a * (C₀ * y ^ i * Y) ≤ C₀ * y ^ (i + 1) * Y := by
        have hc : 0 ≤ C₀ * y ^ i * Y := by positivity
        calc a * (C₀ * y ^ i * Y) ≤ y * (C₀ * y ^ i * Y) := mul_le_mul_of_nonneg_right hay hc
          _ = C₀ * y ^ (i + 1) * Y := by ring
      calc G (i + 1) ≤ a * G i + D * x ^ (i + 1) := h
        _ ≤ a * (D * x / (x - a) * x ^ i + C₀ * y ^ i * Y) + D * x ^ (i + 1) := by gcongr
        _ = D * x / (x - a) * x ^ (i + 1) + a * (C₀ * y ^ i * Y) := by
          rw [← geom_step hax i]; ring
        _ ≤ D * x / (x - a) * x ^ (i + 1) + C₀ * y ^ (i + 1) * Y := by linarith

/-! ### Real powers -/

theorem pow_rpow_eq {m : ℝ} (hm : 0 ≤ m) (j : ℕ) (r : ℝ) : (m ^ j) ^ r = (m ^ r) ^ j :=
  (Real.rpow_pow_comm hm r j).symm

theorem lt_rpow_of_logb_lt {a m lam : ℝ} (ha : 0 ≤ a) (hm : 1 < m)
    (h : Real.logb m a < lam) : a < m ^ lam := by
  rcases ha.eq_or_lt with rfl | ha
  · exact Real.rpow_pos_of_pos (by linarith) lam
  · exact (Real.logb_lt_iff_lt_rpow hm ha).mp h

/-- The per-node overhead `(K e)^τ + 1` is at most `2 K^τ e^λ` for `K, e ≥ 1`, `0 ≤ τ ≤ λ`. -/
theorem overhead_le {K e τ lam : ℝ} (hK : 1 ≤ K) (he : 1 ≤ e) (hτ : 0 ≤ τ) (hτl : τ ≤ lam) :
    (K * e) ^ τ + 1 ≤ 2 * K ^ τ * e ^ lam := by
  rw [Real.mul_rpow (by linarith) (by linarith)]
  have h1 : 1 ≤ K ^ τ := Real.one_le_rpow hK hτ
  have h2 : e ^ τ ≤ e ^ lam := Real.rpow_le_rpow_of_exponent_le he hτl
  have h3 : 1 ≤ e ^ lam := Real.one_le_rpow he (hτ.trans hτl)
  nlinarith

/-- Absorption of `K` at an internal node: if `K ≤ d^c` and the node has `e ≥ d^β` chunks,
then `(K e)^τ + 1 ≤ 2 e^λ` whenever `τ (1 + c/β) ≤ λ`. -/
theorem overhead_absorb {d K e τ lam β c : ℝ} (hd : 1 ≤ d) (hβ : 0 < β) (hc : 0 ≤ c)
    (hτ : 0 ≤ τ) (hτc : τ * (1 + c / β) ≤ lam) (hK0 : 0 ≤ K) (hKd : K ≤ d ^ c)
    (he : d ^ β ≤ e) : (K * e) ^ τ + 1 ≤ 2 * e ^ lam := by
  have hdβ : 1 ≤ d ^ β := Real.one_le_rpow hd hβ.le
  have he1 : 1 ≤ e := hdβ.trans he
  have he0 : 0 < e := by linarith
  have hcβ : 0 ≤ c / β := div_nonneg hc hβ.le
  have hdc : d ^ c ≤ e ^ (c / β) := by
    have : d ^ c = (d ^ β) ^ (c / β) := by
      rw [← Real.rpow_mul (by linarith)]
      congr 1
      field_simp
    rw [this]
    exact Real.rpow_le_rpow (by linarith) he hcβ
  have hKτ : K ^ τ ≤ e ^ (c / β * τ) := by
    rw [Real.rpow_mul he0.le]
    exact Real.rpow_le_rpow hK0 (hKd.trans hdc) hτ
  have hexp : c / β * τ + τ ≤ lam := by nlinarith
  have hlam : 0 ≤ lam := by nlinarith
  rw [Real.mul_rpow hK0 he0.le]
  have h1 : K ^ τ * e ^ τ ≤ e ^ lam := by
    calc K ^ τ * e ^ τ ≤ e ^ (c / β * τ) * e ^ τ :=
          mul_le_mul_of_nonneg_right hKτ (Real.rpow_nonneg he0.le τ)
      _ = e ^ (c / β * τ + τ) := (Real.rpow_add he0 _ _).symm
      _ ≤ e ^ lam := Real.rpow_le_rpow_of_exponent_le he1 hexp
  have h2 : 1 ≤ e ^ lam := Real.one_le_rpow he1 hlam
  linarith

/-! ### 1. The closed recurrence bound -/

/-- Explicit constant of the closed bound: `C₀ + 2 C₁ m^λ / (m^λ - a)`. -/
noncomputable def recConst (a m lam C₀ C₁ : ℝ) : ℝ := C₀ + 2 * C₁ * m ^ lam / (m ^ lam - a)

/-- Sharp form: with leaf size `u ≥ 1`, `F 0 ≤ C₀ u` and the internal step at the parent of
`m^(j+1) u` chunks, `F j ≤ 2 C₁ m^λ/(m^λ - a) · (m^j u)^λ K^τ + C₀ a^j u`. -/
theorem recurrence_sharp {F : ℕ → ℝ} {a m τ lam K C₀ C₁ u : ℝ}
    (ha : 0 ≤ a) (hm : 1 < m) (hτ : 0 ≤ τ) (hτl : τ ≤ lam) (hal : Real.logb m a < lam)
    (hK : 1 ≤ K) (hC₁ : 0 ≤ C₁) (hu : 1 ≤ u) (h0 : F 0 ≤ C₀ * u)
    (hs : ∀ j, F (j + 1) ≤ a * F j + C₁ * ((K * m ^ (j + 1) * u) ^ τ + 1)) (j : ℕ) :
    F j ≤ 2 * C₁ * m ^ lam / (m ^ lam - a) * (m ^ j * u) ^ lam * K ^ τ + C₀ * a ^ j * u := by
  have hm0 : 0 ≤ m := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hax : a < m ^ lam := lt_rpow_of_logb_lt ha hm hal
  have hD : 0 ≤ 2 * C₁ * K ^ τ * u ^ lam := by positivity
  have hstep : ∀ i, F (i + 1) ≤ a * F i + 2 * C₁ * K ^ τ * u ^ lam * (m ^ lam) ^ (i + 1) := by
    intro i
    have he : 1 ≤ m ^ (i + 1) * u := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hm.le) hu
    have ho := overhead_le hK he hτ hτl
    rw [Real.mul_rpow (pow_nonneg hm0 _) hu0, pow_rpow_eq hm0, ← mul_assoc] at ho
    calc F (i + 1) ≤ a * F i + C₁ * ((K * m ^ (i + 1) * u) ^ τ + 1) := hs i
      _ ≤ a * F i + C₁ * (2 * K ^ τ * (m ^ lam) ^ (i + 1) * u ^ lam) := by
        gcongr
        exact ho.trans (le_of_eq (by ring))
      _ = a * F i + 2 * C₁ * K ^ τ * u ^ lam * (m ^ lam) ^ (i + 1) := by ring
  have hj := unroll_geom ha hax hD h0 hstep j
  rw [Real.mul_rpow (pow_nonneg hm0 _) hu0, pow_rpow_eq hm0]
  calc F j ≤ 2 * C₁ * K ^ τ * u ^ lam * m ^ lam / (m ^ lam - a) * (m ^ lam) ^ j +
        C₀ * u * a ^ j := hj
    _ = _ := by ring

/-- **Recurrence.** For `0 ≤ a`, `1 < m`, `0 ≤ τ ≤ λ`, `log_m a < λ` (`a = 0` allowed), `K ≥ 1`,
`C₀, C₁ ≥ 0`, leaf size `u ≥ 1`, `F 0 ≤ C₀ u` and
`F (j+1) ≤ a F j + C₁ ((K m^j u)^τ + 1)`, every `F j ≤ C (m^j u)^λ K^τ + C a^j u` with
`C = recConst a m λ C₀ C₁`. -/
theorem recurrence_closed {F : ℕ → ℝ} {a m τ lam K C₀ C₁ u : ℝ}
    (ha : 0 ≤ a) (hm : 1 < m) (hτ : 0 ≤ τ) (hτl : τ ≤ lam) (hal : Real.logb m a < lam)
    (hK : 1 ≤ K) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hu : 1 ≤ u) (h0 : F 0 ≤ C₀ * u)
    (hs : ∀ j, F (j + 1) ≤ a * F j + C₁ * ((K * m ^ j * u) ^ τ + 1)) (j : ℕ) :
    F j ≤ recConst a m lam C₀ C₁ * (m ^ j * u) ^ lam * K ^ τ +
      recConst a m lam C₀ C₁ * a ^ j * u := by
  have hm0 : 0 ≤ m := by linarith
  have hax : a < m ^ lam := lt_rpow_of_logb_lt ha hm hal
  have hs' : ∀ j, F (j + 1) ≤ a * F j + C₁ * ((K * m ^ (j + 1) * u) ^ τ + 1) := by
    intro j
    refine (hs j).trans ?_
    gcongr
    · have : 0 ≤ K * m ^ j := by positivity
      linarith
    · exact Nat.le_succ j
  have h := recurrence_sharp ha hm hτ hτl hal hK hC₁ hu h0 hs' j
  have hA : 0 ≤ 2 * C₁ * m ^ lam / (m ^ lam - a) :=
    div_nonneg (by positivity) (sub_pos.mpr hax).le
  have hP : 0 ≤ (m ^ j * u) ^ lam * K ^ τ := by
    have : 0 ≤ m ^ j * u := by have := pow_nonneg hm0 j; nlinarith
    positivity
  have hQ : 0 ≤ a ^ j * u := by have := pow_nonneg ha j; nlinarith
  unfold recConst
  nlinarith [mul_nonneg hC₀ hP, mul_nonneg hA hQ]

/-! ### 2. Leaves against internal nodes -/

/-- **Leaves vs. internal.** With `0 ≤ a ≤ m^σ` and `u > 0`,
`a^j u ≤ (m^j u)^σ u^(1-σ)`. -/
theorem leaf_le {a m σ u : ℝ} (ha : 0 ≤ a) (hm : 0 ≤ m) (haσ : a ≤ m ^ σ) (hu : 0 < u)
    (j : ℕ) : a ^ j * u ≤ (m ^ j * u) ^ σ * u ^ (1 - σ) := by
  rw [Real.mul_rpow (pow_nonneg hm j) hu.le, mul_assoc, ← Real.rpow_add hu,
    show σ + (1 - σ) = 1 by ring, Real.rpow_one, pow_rpow_eq hm]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha haσ j) hu.le

/-- Leaves of size `u ≤ U`, `σ ≤ 1`: `a^j u ≤ (m^j u)^σ U^(1-σ)`. -/
theorem leaf_le_of_le {a m σ u U : ℝ} (ha : 0 ≤ a) (hm : 0 ≤ m) (haσ : a ≤ m ^ σ) (hσ1 : σ ≤ 1)
    (hu : 0 < u) (huU : u ≤ U) (j : ℕ) : a ^ j * u ≤ (m ^ j * u) ^ σ * U ^ (1 - σ) := by
  refine (leaf_le ha hm haσ hu j).trans ?_
  have : 0 ≤ m ^ j * u := mul_nonneg (pow_nonneg hm j) hu.le
  gcongr

/-! ### 3. Pieces -/

/-- Normalized cost `G j` of a piece of `m^j` chunks for one layer of width parameter `d`.
Each exponent is either a leaf (`m^j ≤ d^β`, individual kernels, `G j ≤ C₀ m^j`) or an
internal node (`d^β ≤ m^j`) whose `s` children act on `m^(j-1)` chunks at volume `1/W`:
`G j ≤ a G (j-1) + C₁ ((K m^j)^τ + 1)` with `a = s/W`. -/
def PieceCost (m a τ β C₀ C₁ d K : ℝ) (G : ℕ → ℝ) : Prop :=
  ∀ j, (m ^ j ≤ d ^ β ∧ G j ≤ C₀ * m ^ j) ∨
    ∃ i, j = i + 1 ∧ d ^ β ≤ m ^ j ∧ G j ≤ a * G i + C₁ * ((K * m ^ j) ^ τ + 1)

/-- The recursion stopped at a fixed cutoff `j₀` with `m^j₀ ≤ d^β ≤ m^(j₀+1)`: pieces of
`m^j` chunks with `j ≤ j₀` are leaves and all others recurse, so the leaf size of a piece of
`m^j` chunks is `min (m^j) (m^j₀)`. -/
theorem pieceCost_of_cutoff {m a τ β C₀ C₁ d K : ℝ} {G : ℕ → ℝ} (hm : 1 ≤ m) {j₀ : ℕ}
    (hj₀ : m ^ j₀ ≤ d ^ β) (hj₀' : d ^ β ≤ m ^ (j₀ + 1))
    (hleaf : ∀ j ≤ j₀, G j ≤ C₀ * m ^ j)
    (hstep : ∀ j, j₀ ≤ j → G (j + 1) ≤ a * G j + C₁ * ((K * m ^ (j + 1)) ^ τ + 1)) :
    PieceCost m a τ β C₀ C₁ d K G := by
  intro j
  rcases le_or_gt j j₀ with h | h
  · exact Or.inl ⟨(pow_le_pow_right₀ hm h).trans hj₀, hleaf j h⟩
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact Or.inr ⟨i, rfl, hj₀'.trans (pow_le_pow_right₀ hm (by omega)), hstep i (by omega)⟩

/-- Such a cutoff exists for every `d^β ≥ 1`. -/
theorem exists_cutoff {m d β : ℝ} (hm : 1 < m) (hd : 1 ≤ d) (hβ : 0 ≤ β) :
    ∃ j₀ : ℕ, m ^ j₀ ≤ d ^ β ∧ d ^ β < m ^ (j₀ + 1) :=
  exists_nat_pow_near (Real.one_le_rpow hd hβ) hm

/-- A leaf of `m^j ≤ d^β` chunks: `m^j ≤ (m^σ)^j (d^β)^(1-σ)`. -/
theorem leaf_split {m d β σ : ℝ} (hm : 0 < m) (hσ1 : σ ≤ 1) {j : ℕ} (hj : m ^ j ≤ d ^ β) :
    m ^ j ≤ (m ^ σ) ^ j * (d ^ β) ^ (1 - σ) := by
  have hp : 0 < m ^ j := pow_pos hm j
  calc m ^ j = (m ^ j) ^ σ * (m ^ j) ^ (1 - σ) := by
        rw [← Real.rpow_add hp, show σ + (1 - σ) = 1 by ring, Real.rpow_one]
    _ ≤ (m ^ j) ^ σ * (d ^ β) ^ (1 - σ) := by
        gcongr
    _ = (m ^ σ) ^ j * (d ^ β) ^ (1 - σ) := by rw [pow_rpow_eq hm.le]

theorem rpow_split {d β σ : ℝ} (hd : 0 < d) :
    d ^ σ * (d ^ β) ^ (1 - σ) = d ^ (σ + β * (1 - σ)) := by
  rw [← Real.rpow_mul hd.le, ← Real.rpow_add hd]

/-- Per-piece bound for a general internal-overhead coefficient `D`: if every internal
overhead is at most `D (m^λ)^j`, then every piece of `m^j ≤ d` chunks costs at most
`D m^λ/(m^λ - a) · d^λ + C₀ d^(σ + β(1-σ))`. -/
theorem piece_le_of_overhead {m a τ σ lam β C₀ C₁ d K D : ℝ} {G : ℕ → ℝ}
    (hm : 1 < m) (ha : 0 ≤ a) (haσ : a ≤ m ^ σ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hσl : σ < lam)
    (hC₀ : 0 ≤ C₀) (hD : 0 ≤ D) (hd : 1 ≤ d)
    (hG : PieceCost m a τ β C₀ C₁ d K G)
    (hover : ∀ j, d ^ β ≤ m ^ j → C₁ * ((K * m ^ j) ^ τ + 1) ≤ D * (m ^ lam) ^ j)
    {j : ℕ} (hj : m ^ j ≤ d) :
    G j ≤ D * m ^ lam / (m ^ lam - a) * d ^ lam + C₀ * d ^ (σ + β * (1 - σ)) := by
  have hm0 : 0 < m := by linarith
  have hd0 : 0 < d := by linarith
  have hσl' : m ^ σ < m ^ lam := Real.rpow_lt_rpow_of_exponent_lt hm hσl
  have hax : a < m ^ lam := lt_of_le_of_lt haσ hσl'
  have hY : 0 ≤ (d ^ β) ^ (1 - σ) := by positivity
  have hinv := cost_invariant (G := G) (x := m ^ lam) (y := m ^ σ) (D := D) (C₀ := C₀)
    (Y := (d ^ β) ^ (1 - σ)) ha hax haσ hD hC₀ hY (by
      intro j
      rcases hG j with ⟨hl, hc⟩ | ⟨i, hi, hs, hc⟩
      · left
        calc G j ≤ C₀ * m ^ j := hc
          _ ≤ C₀ * ((m ^ σ) ^ j * (d ^ β) ^ (1 - σ)) := by
            gcongr; exact leaf_split hm0 hσ1 hl
          _ = C₀ * (m ^ σ) ^ j * (d ^ β) ^ (1 - σ) := by ring
      · right
        exact ⟨i, hi, hc.trans (by linarith [hover j hs])⟩) j
  have hA : 0 ≤ D * m ^ lam / (m ^ lam - a) :=
    div_nonneg (by positivity) (sub_pos.mpr hax).le
  have hpj : 0 ≤ m ^ j := by positivity
  have h1 : (m ^ lam) ^ j ≤ d ^ lam := by
    rw [← pow_rpow_eq hm0.le]
    exact Real.rpow_le_rpow hpj hj (hσ0.trans hσl.le)
  have h2 : (m ^ σ) ^ j ≤ d ^ σ := by
    rw [← pow_rpow_eq hm0.le]
    exact Real.rpow_le_rpow hpj hj hσ0
  calc G j ≤ D * m ^ lam / (m ^ lam - a) * (m ^ lam) ^ j + C₀ * (m ^ σ) ^ j * (d ^ β) ^ (1 - σ) :=
        hinv
    _ ≤ D * m ^ lam / (m ^ lam - a) * d ^ lam + C₀ * d ^ σ * (d ^ β) ^ (1 - σ) := by
        gcongr
    _ = _ := by rw [mul_assoc C₀, rpow_split hd0]

/-! #### Counting pieces -/

/-- At most `1 + log_m d` exponents `j` have `m^j ≤ d`. -/
theorem card_filter_pow_le {m d : ℝ} (hm : 1 < m) (hd : 1 ≤ d) (k : ℕ) :
    ((({j ∈ range (k + 1) | m ^ j ≤ d}) : Finset ℕ).card : ℝ) ≤ 1 + Real.logb m d := by
  have hsub : ({j ∈ range (k + 1) | m ^ j ≤ d} : Finset ℕ) ⊆ range (⌊Real.logb m d⌋₊ + 1) := by
    intro j hj
    rw [mem_filter] at hj
    rw [mem_range, Nat.lt_succ_iff]
    apply Nat.le_floor
    have := Real.logb_le_logb_of_le hm (by positivity) hj.2
    rwa [Real.logb_pow, Real.logb_self_eq_one hm, mul_one] at this
  have hc := card_le_card hsub
  rw [card_range] at hc
  have hl : 0 ≤ Real.logb m d := Real.logb_nonneg hm hd
  have hf : (⌊Real.logb m d⌋₊ : ℝ) ≤ Real.logb m d := Nat.floor_le hl
  have : ((({j ∈ range (k + 1) | m ^ j ≤ d}) : Finset ℕ).card : ℝ) ≤
      ((⌊Real.logb m d⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hc
  push_cast at this
  linarith

/-- A nonzero digit `n j` of `Σ n_j m^j ≤ d` has `m^j ≤ d`. -/
theorem pow_le_of_digit_ne_zero {m d : ℝ} (hm : 0 ≤ m) (n : ℕ → ℕ) (k : ℕ)
    (hsum : ∑ j ∈ range (k + 1), (n j : ℝ) * m ^ j ≤ d) :
    ∀ j ∈ range (k + 1), n j ≠ 0 → m ^ j ≤ d := by
  intro j hj hne
  have h1 : (1 : ℝ) ≤ n j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
  have hpow : 0 ≤ m ^ j := pow_nonneg hm j
  calc m ^ j ≤ (n j : ℝ) * m ^ j := le_mul_of_one_le_left hpow h1
    _ ≤ ∑ i ∈ range (k + 1), (n i : ℝ) * m ^ i :=
        single_le_sum (f := fun i => (n i : ℝ) * m ^ i) (fun i _ => by positivity) hj
    _ ≤ d := hsum

/-- Digit pieces: with digits `n j ≤ N`, nonzero only where `m^j ≤ d`, and every piece of
`m^j ≤ d` chunks costing at most `B ≥ 0`, all pieces together cost `≤ N (1 + log_m d) B`. -/
theorem digit_sum_le {m d N B : ℝ} {G : ℕ → ℝ} (hm : 1 < m) (hd : 1 ≤ d) (hB : 0 ≤ B)
    (n : ℕ → ℕ) (k : ℕ) (hn : ∀ j, (n j : ℝ) ≤ N)
    (hnz : ∀ j ∈ range (k + 1), n j ≠ 0 → m ^ j ≤ d) (hGB : ∀ j, m ^ j ≤ d → G j ≤ B) :
    ∑ j ∈ range (k + 1), (n j : ℝ) * G j ≤ N * (1 + Real.logb m d) * B := by
  have hN : 0 ≤ N := le_trans (Nat.cast_nonneg _) (hn 0)
  calc ∑ j ∈ range (k + 1), (n j : ℝ) * G j
      ≤ ∑ j ∈ range (k + 1), if m ^ j ≤ d then N * B else 0 := by
        apply sum_le_sum
        intro j hj
        split_ifs with h
        · calc (n j : ℝ) * G j ≤ n j * B := mul_le_mul_of_nonneg_left (hGB j h) (Nat.cast_nonneg _)
            _ ≤ N * B := mul_le_mul_of_nonneg_right (hn j) hB
        · have : n j = 0 := by
            by_contra hne
            exact h (hnz j hj hne)
          simp [this]
    _ = (({j ∈ range (k + 1) | m ^ j ≤ d} : Finset ℕ).card : ℝ) * (N * B) := by
        rw [← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ (1 + Real.logb m d) * (N * B) := by
        gcongr
        exact card_filter_pow_le hm hd k
    _ = N * (1 + Real.logb m d) * B := by ring

/-! #### Totals -/

/-- The digit pieces plus `q₀ ≤ Q (1 + log_m d)` preprocessing kernels of normalized cost
`C₂`, when each piece of `m^j ≤ d` chunks costs at most `A X + C₀ Y`. -/
theorem total_le {m d A C₀ C₂ Q q₀ X Y : ℝ} {G : ℕ → ℝ} (hm : 1 < m) (hd : 1 ≤ d)
    (hA : 0 ≤ A) (hC₀ : 0 ≤ C₀) (hC₂ : 0 ≤ C₂) (hQ : 0 ≤ Q) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (n : ℕ → ℕ) (k : ℕ) (hn : ∀ j, (n j : ℝ) ≤ m - 1)
    (hnz : ∀ j ∈ range (k + 1), n j ≠ 0 → m ^ j ≤ d)
    (hGB : ∀ j, m ^ j ≤ d → G j ≤ A * X + C₀ * Y) (hq : q₀ ≤ Q * (1 + Real.logb m d)) :
    ∑ j ∈ range (k + 1), (n j : ℝ) * G j + q₀ * C₂ ≤
      ((m - 1) * (A + C₀) + Q * C₂) * (1 + Real.logb m d) * (X + Y + 1) := by
  have hL : 0 ≤ 1 + Real.logb m d := by have := Real.logb_nonneg hm hd; linarith
  have hm1 : 0 ≤ m - 1 := by linarith
  have hs := digit_sum_le hm hd (by positivity : 0 ≤ A * X + C₀ * Y) n k hn hnz hGB
  have hq' : q₀ * C₂ ≤ Q * (1 + Real.logb m d) * C₂ := mul_le_mul_of_nonneg_right hq hC₂
  have key : (m - 1) * (A * X + C₀ * Y) + Q * C₂ ≤
      ((m - 1) * (A + C₀) + Q * C₂) * (X + Y + 1) := by
    nlinarith [mul_nonneg (mul_nonneg hm1 hA) hY, mul_nonneg hm1 hA,
      mul_nonneg (mul_nonneg hm1 hC₀) hX, mul_nonneg hm1 hC₀,
      mul_nonneg (mul_nonneg hQ hC₂) hX, mul_nonneg (mul_nonneg hQ hC₂) hY]
  have := mul_le_mul_of_nonneg_left key hL
  linarith

/-- Coefficient of `d^λ` in one piece: `2 C₁ m^λ / (m^λ - a)`. -/
noncomputable def internalConst (a m lam C₁ : ℝ) : ℝ := 2 * C₁ * m ^ lam / (m ^ lam - a)

/-- `C' = (m - 1)(2 C₁ m^λ / (m^λ - a) + C₀) + Q C₂`. -/
noncomputable def pieceConst (a m lam C₀ C₁ C₂ Q : ℝ) : ℝ :=
  (m - 1) * (internalConst a m lam C₁ + C₀) + Q * C₂

private theorem digit_le {m : ℕ} (n : ℕ → ℕ) (hn : ∀ j, n j < m) (j : ℕ) :
    (n j : ℝ) ≤ (m : ℝ) - 1 := by
  have : ((n j + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hn j
  push_cast at this
  linarith

/-- **Pieces, unabsorbed.** For `D' = Σ n_j m^j ≤ d` with base-`m` digits `n_j < m`, the
pieces plus `q₀ ≤ Q (1 + log_m d)` preprocessing kernels cost at most
`C' (1 + log_m d) (d^λ K^τ + d^(σ + β(1-σ)) + 1)` with `C' = pieceConst a m λ C₀ C₁ C₂ Q`. -/
theorem layer_total_le {m : ℕ} {a τ σ lam β C₀ C₁ C₂ Q d K q₀ : ℝ} {G : ℕ → ℝ}
    (hm : 2 ≤ m) (ha : 0 ≤ a) (haσ : a ≤ (m : ℝ) ^ σ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hσl : σ < lam) (hτ : 0 ≤ τ) (hτl : τ ≤ lam) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hC₂ : 0 ≤ C₂) (hQ : 0 ≤ Q) (hd : 1 ≤ d) (hK : 1 ≤ K)
    (hG : PieceCost m a τ β C₀ C₁ d K G)
    (n : ℕ → ℕ) (k : ℕ) (hn : ∀ j, n j < m)
    (hsum : ∑ j ∈ range (k + 1), (n j : ℝ) * (m : ℝ) ^ j ≤ d)
    (hq : q₀ ≤ Q * (1 + Real.logb m d)) :
    ∑ j ∈ range (k + 1), (n j : ℝ) * G j + q₀ * C₂ ≤
      pieceConst a m lam C₀ C₁ C₂ Q * (1 + Real.logb m d) *
        (d ^ lam * K ^ τ + d ^ (σ + β * (1 - σ)) + 1) := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hax : a < (m : ℝ) ^ lam :=
    lt_of_le_of_lt haσ (Real.rpow_lt_rpow_of_exponent_lt hm1 hσl)
  have hA : 0 ≤ internalConst a m lam C₁ :=
    div_nonneg (by positivity) (sub_pos.mpr hax).le
  have hpiece : ∀ j, (m : ℝ) ^ j ≤ d →
      G j ≤ internalConst a m lam C₁ * (d ^ lam * K ^ τ) + C₀ * d ^ (σ + β * (1 - σ)) := by
    intro j hj
    have h := piece_le_of_overhead (D := 2 * C₁ * K ^ τ) hm1 ha haσ hσ0 hσ1 hσl hC₀
      (by positivity) hd hG (by
        intro i _
        have he : 1 ≤ (m : ℝ) ^ i := one_le_pow₀ hm1.le
        have ho := overhead_le hK he hτ hτl
        rw [← pow_rpow_eq hm0]
        calc C₁ * ((K * (m : ℝ) ^ i) ^ τ + 1) ≤ C₁ * (2 * K ^ τ * ((m : ℝ) ^ i) ^ lam) := by
              gcongr
          _ = _ := by ring) hj
    calc G j ≤ _ := h
      _ = _ := by unfold internalConst; ring
  have h := total_le hm1 hd hA hC₀ hC₂ hQ (by positivity) (by positivity) n k (digit_le n hn)
    (pow_le_of_digit_ne_zero hm0 n k hsum) hpiece hq
  calc _ ≤ _ := h
    _ = _ := by unfold pieceConst; ring

/-- **Pieces, absorbed.** With `K ≤ d^c` and `τ (1 + c/β) ≤ λ`, each internal node
(`e ≥ d^β` chunks) has overhead `≤ 2 e^λ`, and the total is at most
`C' (1 + log_m d) (d^λ + d^(σ + β(1-σ)) + 1)`. -/
theorem layer_total_le_absorbed {m : ℕ} {a τ σ lam β c C₀ C₁ C₂ Q d K q₀ : ℝ} {G : ℕ → ℝ}
    (hm : 2 ≤ m) (ha : 0 ≤ a) (haσ : a ≤ (m : ℝ) ^ σ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hσl : σ < lam) (hτ : 0 ≤ τ) (hβ : 0 < β) (hc : 0 ≤ c) (hτc : τ * (1 + c / β) ≤ lam)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hQ : 0 ≤ Q)
    (hd : 1 ≤ d) (hK0 : 0 ≤ K) (hKd : K ≤ d ^ c)
    (hG : PieceCost m a τ β C₀ C₁ d K G)
    (n : ℕ → ℕ) (k : ℕ) (hn : ∀ j, n j < m)
    (hsum : ∑ j ∈ range (k + 1), (n j : ℝ) * (m : ℝ) ^ j ≤ d)
    (hq : q₀ ≤ Q * (1 + Real.logb m d)) :
    ∑ j ∈ range (k + 1), (n j : ℝ) * G j + q₀ * C₂ ≤
      pieceConst a m lam C₀ C₁ C₂ Q * (1 + Real.logb m d) *
        (d ^ lam + d ^ (σ + β * (1 - σ)) + 1) := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hax : a < (m : ℝ) ^ lam :=
    lt_of_le_of_lt haσ (Real.rpow_lt_rpow_of_exponent_lt hm1 hσl)
  have hA : 0 ≤ internalConst a m lam C₁ :=
    div_nonneg (by positivity) (sub_pos.mpr hax).le
  have hpiece : ∀ j, (m : ℝ) ^ j ≤ d →
      G j ≤ internalConst a m lam C₁ * d ^ lam + C₀ * d ^ (σ + β * (1 - σ)) := by
    intro j hj
    have h := piece_le_of_overhead (D := 2 * C₁) hm1 ha haσ hσ0 hσ1 hσl hC₀
      (by positivity) hd hG (by
        intro i hi
        have ho := overhead_absorb hd hβ hc hτ hτc hK0 hKd hi
        rw [← pow_rpow_eq hm0]
        calc C₁ * ((K * (m : ℝ) ^ i) ^ τ + 1) ≤ C₁ * (2 * ((m : ℝ) ^ i) ^ lam) := by
              gcongr
          _ = _ := by ring) hj
    exact h
  have h := total_le hm1 hd hA hC₀ hC₂ hQ (by positivity) (by positivity) n k (digit_le n hn)
    (pow_le_of_digit_ne_zero hm0 n k hsum) hpiece hq
  calc _ ≤ _ := h
    _ = _ := by unfold pieceConst; ring

/-! #### Absorbing the logarithm -/

theorem one_add_logb_le {m d ε : ℝ} (hm : 1 < m) (hd : 1 ≤ d) (hε : 0 < ε) :
    1 + Real.logb m d ≤ (1 + 1 / (ε * Real.log m)) * d ^ ε := by
  have hlogm : 0 < Real.log m := Real.log_pos hm
  have h1 : 1 ≤ d ^ ε := Real.one_le_rpow hd hε.le
  have h2 : Real.log d ≤ d ^ ε / ε := Real.log_le_rpow_div (by linarith) hε
  have h3 : Real.logb m d ≤ d ^ ε / ε / Real.log m := div_le_div_of_nonneg_right h2 hlogm.le
  calc 1 + Real.logb m d ≤ d ^ ε + d ^ ε / ε / Real.log m := by linarith
    _ = (1 + 1 / (ε * Real.log m)) * d ^ ε := by field_simp

theorem sum_rpow_le {d p q μ : ℝ} (hd : 1 ≤ d) (hp : p ≤ μ) (hq : q ≤ μ) (hμ : 0 ≤ μ) :
    d ^ p + d ^ q + 1 ≤ 3 * d ^ μ := by
  have h1 := Real.rpow_le_rpow_of_exponent_le hd hp
  have h2 := Real.rpow_le_rpow_of_exponent_le hd hq
  have h3 := Real.one_le_rpow hd hμ
  linarith

/-- The explicit final constant
`3 C' (1 + 1 / ((λ' - max λ (σ + β(1-σ))) log m))`. -/
noncomputable def layerConst (a m σ lam lam' β C₀ C₁ C₂ Q : ℝ) : ℝ :=
  3 * pieceConst a m lam C₀ C₁ C₂ Q *
    (1 + 1 / ((lam' - max lam (σ + β * (1 - σ))) * Real.log m))

/-- **Pieces, power bound.** Under the hypotheses of `layer_total_le_absorbed`, for every
`λ' > max λ (σ + β(1-σ))` and every `d ≥ 1` the total is at most
`layerConst · d^λ'`. -/
theorem layer_cost_le {m : ℕ} {a τ σ lam lam' β c C₀ C₁ C₂ Q d K q₀ : ℝ} {G : ℕ → ℝ}
    (hm : 2 ≤ m) (ha : 0 ≤ a) (haσ : a ≤ (m : ℝ) ^ σ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hσl : σ < lam) (hτ : 0 ≤ τ) (hβ : 0 < β) (hc : 0 ≤ c) (hτc : τ * (1 + c / β) ≤ lam)
    (hl' : lam < lam') (hℓ' : σ + β * (1 - σ) < lam')
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hQ : 0 ≤ Q)
    (hd : 1 ≤ d) (hK0 : 0 ≤ K) (hKd : K ≤ d ^ c)
    (hG : PieceCost m a τ β C₀ C₁ d K G)
    (n : ℕ → ℕ) (k : ℕ) (hn : ∀ j, n j < m)
    (hsum : ∑ j ∈ range (k + 1), (n j : ℝ) * (m : ℝ) ^ j ≤ d)
    (hq : q₀ ≤ Q * (1 + Real.logb m d)) :
    ∑ j ∈ range (k + 1), (n j : ℝ) * G j + q₀ * C₂ ≤
      layerConst a m σ lam lam' β C₀ C₁ C₂ Q * d ^ lam' := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hax : a < (m : ℝ) ^ lam :=
    lt_of_le_of_lt haσ (Real.rpow_lt_rpow_of_exponent_lt hm1 hσl)
  have hC' : 0 ≤ pieceConst a m lam C₀ C₁ C₂ Q := by
    have hA : 0 ≤ internalConst a m lam C₁ :=
      div_nonneg (by positivity) (sub_pos.mpr hax).le
    unfold pieceConst
    have : (0 : ℝ) ≤ m - 1 := by linarith
    positivity
  set μ := max lam (σ + β * (1 - σ)) with hμ
  have hε : 0 < lam' - μ := sub_pos.mpr (max_lt hl' hℓ')
  have hμ0 : 0 ≤ μ := le_max_of_le_left (hσ0.trans hσl.le)
  have h := layer_total_le_absorbed hm ha haσ hσ0 hσ1 hσl hτ hβ hc hτc hC₀ hC₁ hC₂ hQ hd hK0
    hKd hG n k hn hsum hq
  have hlog := one_add_logb_le hm1 hd hε
  have hsumle := sum_rpow_le (p := lam) (q := σ + β * (1 - σ)) hd (le_max_left _ _)
    (le_max_right _ _) hμ0
  have hL : 0 ≤ 1 + Real.logb m d := by have := Real.logb_nonneg hm1 hd; linarith
  have hd0 : 0 < d := by linarith
  have hS : 0 ≤ d ^ lam + d ^ (σ + β * (1 - σ)) + 1 := by positivity
  calc _ ≤ pieceConst a m lam C₀ C₁ C₂ Q * (1 + Real.logb m d) *
        (d ^ lam + d ^ (σ + β * (1 - σ)) + 1) := h
    _ ≤ pieceConst a m lam C₀ C₁ C₂ Q *
        ((1 + 1 / ((lam' - μ) * Real.log m)) * d ^ (lam' - μ)) * (3 * d ^ μ) := by
        gcongr
    _ = layerConst a m σ lam lam' β C₀ C₁ C₂ Q * (d ^ (lam' - μ) * d ^ μ) := by
        unfold layerConst; rw [← hμ]; ring
    _ = layerConst a m σ lam lam' β C₀ C₁ C₂ Q * d ^ lam' := by
        rw [← Real.rpow_add hd0, sub_add_cancel]

/-! ### Preprocessing count -/

/-- The row-preprocessing count `q₀ = ⌈log₂ W⌉ ⌈log_m (2d)⌉` satisfies
`q₀ ≤ Q (1 + log_m d)` with `Q = 2 ⌈log₂ W⌉`. -/
theorem q0_le {m W d : ℝ} (hm : 2 ≤ m) (hd : 1 ≤ d) :
    (⌈Real.logb 2 W⌉₊ : ℝ) * ⌈Real.logb m (2 * d)⌉₊ ≤
      2 * ⌈Real.logb 2 W⌉₊ * (1 + Real.logb m d) := by
  have hm1 : 1 < m := by linarith
  have hl : 0 ≤ Real.logb m d := Real.logb_nonneg hm1 hd
  have h2 : Real.logb m (2 * d) = Real.logb m 2 + Real.logb m d :=
    Real.logb_mul (by norm_num) (by linarith)
  have h2' : Real.logb m 2 ≤ 1 := by
    have := Real.logb_le_logb_of_le hm1 (by norm_num : (0 : ℝ) < 2) hm
    rwa [Real.logb_self_eq_one hm1] at this
  have hy : 0 ≤ Real.logb m (2 * d) := Real.logb_nonneg hm1 (by linarith)
  have hc : (⌈Real.logb m (2 * d)⌉₊ : ℝ) < Real.logb m (2 * d) + 1 := Nat.ceil_lt_add_one hy
  have he : (⌈Real.logb m (2 * d)⌉₊ : ℝ) ≤ 2 * (1 + Real.logb m d) := by linarith
  calc (⌈Real.logb 2 W⌉₊ : ℝ) * ⌈Real.logb m (2 * d)⌉₊
      ≤ (⌈Real.logb 2 W⌉₊ : ℝ) * (2 * (1 + Real.logb m d)) :=
        mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
    _ = 2 * ⌈Real.logb 2 W⌉₊ * (1 + Real.logb m d) := by ring

/-! ### 4. Packaged layer bound -/

/-- One constant bounds the total normalized layer cost for every `d ≥ 1`, `0 ≤ K ≤ d^c`,
piece cost `G` obeying `PieceCost`, base-`m` decomposition `Σ n_j m^j ≤ d` with `n_j < m`, and
preprocessing count `q₀ ≤ Q (1 + log_m d)`. -/
theorem exists_layer_cost_le {m : ℕ} {a τ σ lam lam' β c C₀ C₁ C₂ Q : ℝ}
    (hm : 2 ≤ m) (ha : 0 ≤ a) (haσ : a ≤ (m : ℝ) ^ σ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hσl : σ < lam) (hτ : 0 ≤ τ) (hβ : 0 < β) (hc : 0 ≤ c) (hτc : τ * (1 + c / β) ≤ lam)
    (hl' : lam < lam') (hℓ' : σ + β * (1 - σ) < lam')
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hQ : 0 ≤ Q) :
    ∃ C : ℝ, ∀ d K : ℝ, 1 ≤ d → 0 ≤ K → K ≤ d ^ c →
      ∀ G : ℕ → ℝ, PieceCost m a τ β C₀ C₁ d K G →
      ∀ (n : ℕ → ℕ) (k : ℕ), (∀ j, n j < m) →
        ∑ j ∈ range (k + 1), (n j : ℝ) * (m : ℝ) ^ j ≤ d →
      ∀ q₀ : ℝ, q₀ ≤ Q * (1 + Real.logb m d) →
        ∑ j ∈ range (k + 1), (n j : ℝ) * G j + q₀ * C₂ ≤ C * d ^ lam' :=
  ⟨layerConst a m σ lam lam' β C₀ C₁ C₂ Q,
    fun _ _ hd hK0 hKd _ hG n k hn hsum _ hq =>
      layer_cost_le hm ha haσ hσ0 hσ1 hσl hτ hβ hc hτc hl' hℓ' hC₀ hC₁ hC₂ hQ hd hK0 hKd hG
        n k hn hsum hq⟩

/-- **Simultaneous-layer cost, packaged.** Fix the base `m ≥ 2`, the branching ratio
`a = s/W` with `0 ≤ a ≤ m^σ`, exponents with `0 ≤ σ ≤ 1`, `σ < λ`, `0 ≤ τ`, `β > 0`, `c ≥ 0`,
`τ (1 + c/β) ≤ λ`, `max λ (σ + β(1-σ)) < λ'`, and constants `C₀, C₁, C₂, Q ≥ 0`. There is
one `C` such that for every `d ≥ 1`, `0 ≤ K ≤ d^c`, cutoff `m^j₀ ≤ d^β ≤ m^(j₀+1)` (leaf
size `min (m^j) (m^j₀)` for a piece of `m^j` chunks), piece cost `G` with leaves
`G j ≤ C₀ m^j` (`j ≤ j₀`) and internal steps
`G (j+1) ≤ a G j + C₁ ((K m^(j+1))^τ + 1)` (`j ≥ j₀`), every decomposition of `D' ≤ d`
chunks into base-`m` pieces (`Σ n_j m^j ≤ d`, `n_j < m`), and every preprocessing count
`q₀ ≤ Q (1 + log_m d)` of kernels of normalized cost `C₂`, the total normalized layer cost
is at most `C d^λ'`. -/
theorem layer_cost_bound {m : ℕ} {a τ σ lam lam' β c C₀ C₁ C₂ Q : ℝ}
    (hm : 2 ≤ m) (ha : 0 ≤ a) (haσ : a ≤ (m : ℝ) ^ σ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hσl : σ < lam) (hτ : 0 ≤ τ) (hβ : 0 < β) (hc : 0 ≤ c) (hτc : τ * (1 + c / β) ≤ lam)
    (hl' : lam < lam') (hℓ' : σ + β * (1 - σ) < lam')
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hQ : 0 ≤ Q) :
    ∃ C : ℝ, ∀ d K : ℝ, 1 ≤ d → 0 ≤ K → K ≤ d ^ c →
      ∀ j₀ : ℕ, (m : ℝ) ^ j₀ ≤ d ^ β → d ^ β ≤ (m : ℝ) ^ (j₀ + 1) →
      ∀ G : ℕ → ℝ, (∀ j ≤ j₀, G j ≤ C₀ * (m : ℝ) ^ j) →
        (∀ j, j₀ ≤ j → G (j + 1) ≤ a * G j + C₁ * ((K * (m : ℝ) ^ (j + 1)) ^ τ + 1)) →
      ∀ (n : ℕ → ℕ) (k : ℕ), (∀ j, n j < m) →
        ∑ j ∈ range (k + 1), (n j : ℝ) * (m : ℝ) ^ j ≤ d →
      ∀ q₀ : ℝ, q₀ ≤ Q * (1 + Real.logb m d) →
        ∑ j ∈ range (k + 1), (n j : ℝ) * G j + q₀ * C₂ ≤ C * d ^ lam' :=
  ⟨layerConst a m σ lam lam' β C₀ C₁ C₂ Q,
    fun _ _ hd hK0 hKd _ hj₀ hj₀' _ hleaf hstep n k hn hsum _ hq =>
      layer_cost_le hm ha haσ hσ0 hσ1 hσl hτ hβ hc hτc hl' hℓ' hC₀ hC₁ hC₂ hQ hd hK0 hKd
        (pieceCost_of_cutoff (by exact_mod_cast (show 1 ≤ m by omega)) hj₀ hj₀' hleaf hstep)
        n k hn hsum hq⟩

end IntegerMultBounds.MathlibTM2.Layer.Recurrence
