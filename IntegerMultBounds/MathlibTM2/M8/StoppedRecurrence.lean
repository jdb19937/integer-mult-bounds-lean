module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The stopped recurrence with a linear toll

The stage-2 supplier stops its reversed recursion at a growing atom width `w` and pays the
ordinary leaf interchange there. Its normalized cost obeys, for nodes of `n` atoms,
`T(n) ≤ Σ_i w_i T(n_i) + C n + C L` above a cutoff and `T(n) ≤ C L` below it, where the children
have `n_i ≤ (r_i/m) n` atoms and `L = w^(1-a_leaf)` is the leaf toll. The linear toll `C n` pays the
atom adapters.

`stopped_closed`: with the two moment gaps `Σ_i w_i (r_i/m) ≤ q₁ < 1` and
`Σ_i w_i (r_i/m)^τ ≤ q_τ < 1`, every node costs at most
`C/(1-q₁) · n + C/(1-q_τ) · n^τ L`. The linear child terms use at most `q₁` of the linear part,
leaving the linear toll, and the other child terms use at most `q_τ` of the second part, leaving
the leaf toll since `n^τ ≥ 1`.

The node type, child map, sizes and costs are the caller's; the size relation is an execution
premise, as in `Layer.VariableRecurrence`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.StoppedRecurrence

open Finset

/-- **Stopped recurrence.** Nodes of size at least the cutoff `u` cost at most the weighted costs
of their children plus the linear toll `C n` and the leaf toll `C L`; smaller nodes cost at most
`C L`. Every node has size at least one, and children of a node of size `n ≥ u` are smaller with
sizes at most `(rank/m) n`. With the moments `Σ w (r/m) ≤ q₁ < 1` and `Σ w (r/m)^τ ≤ q_τ < 1`,
every node costs at most `C/(1-q₁) n + C/(1-q_τ) n^τ L`, for `0 ≤ q_τ`. -/
theorem stopped_closed {Node : Type*} (size : Node → ℕ) (arity : Node → ℕ)
    (child : (x : Node) → Fin (arity x) → Node) (rank : (x : Node) → Fin (arity x) → ℕ)
    (weight : (x : Node) → Fin (arity x) → ℝ) (cost : Node → ℝ) (u : ℕ)
    {m τ q₁ qτ C L : ℝ} (hm : 0 < m) (hτ : 0 ≤ τ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hq₁ : q₁ < 1) (hqτ0 : 0 ≤ qτ) (hqτ : qτ < 1) (hweight : ∀ x i, 0 ≤ weight x i)
    (hpos : ∀ x, 1 ≤ size x)
    (hleaf : ∀ x, size x < u → cost x ≤ C * L)
    (hdecrease : ∀ x, u ≤ size x → ∀ i, size (child x i) < size x)
    (hsize : ∀ x, u ≤ size x → ∀ i, (size (child x i) : ℝ) ≤ ((rank x i : ℝ) / m) * size x)
    (hnode : ∀ x, u ≤ size x →
      cost x ≤ ∑ i, weight x i * cost (child x i) + C * size x + C * L)
    (hmom₁ : ∀ x, u ≤ size x → ∑ i, weight x i * ((rank x i : ℝ) / m) ≤ q₁)
    (hmomτ : ∀ x, u ≤ size x → ∑ i, weight x i * ((rank x i : ℝ) / m) ^ τ ≤ qτ) :
    ∀ x, cost x ≤ C / (1 - q₁) * size x + C / (1 - qτ) * ((size x : ℝ) ^ τ * L) := by
  set A := C / (1 - q₁) with hA
  set B := C / (1 - qτ) with hB
  have hA0 : 0 ≤ A := div_nonneg hC (by linarith)
  have hB0 : 0 ≤ B := div_nonneg hC (by linarith)
  have h₁ : 1 - q₁ ≠ 0 := (sub_pos.mpr hq₁).ne'
  have hτ₁ : 1 - qτ ≠ 0 := (sub_pos.mpr hqτ).ne'
  have hAq : A * q₁ + C = A := by
    rw [hA]
    field_simp
    ring
  have hBq : B * qτ + C = B := by
    rw [hB]
    field_simp
    ring
  have hCB : C ≤ B := by
    have := mul_nonneg hB0 hqτ0
    linarith
  have hone (x : Node) : (1 : ℝ) ≤ (size x : ℝ) ^ τ :=
    Real.one_le_rpow (by exact_mod_cast hpos x) hτ
  intro x
  induction hn : size x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    subst hn
    by_cases hu : u ≤ size x
    · have hchild : ∀ i, cost (child x i) ≤
          A * size (child x i) + B * ((size (child x i) : ℝ) ^ τ * L) :=
        fun i => ih _ (hdecrease x hu i) (child x i) rfl
      have hn0 : (0 : ℝ) ≤ size x := Nat.cast_nonneg _
      have hlin : ∑ i, weight x i * (size (child x i) : ℝ) ≤ q₁ * size x := by
        calc ∑ i, weight x i * (size (child x i) : ℝ)
            ≤ ∑ i, weight x i * (((rank x i : ℝ) / m) * size x) :=
              sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hsize x hu i) (hweight x i)
          _ = (∑ i, weight x i * ((rank x i : ℝ) / m)) * size x := by
              rw [sum_mul]; exact sum_congr rfl fun i _ => by ring
          _ ≤ q₁ * size x := mul_le_mul_of_nonneg_right (hmom₁ x hu) hn0
      have hpow : ∑ i, weight x i * (size (child x i) : ℝ) ^ τ ≤ qτ * (size x : ℝ) ^ τ := by
        calc ∑ i, weight x i * (size (child x i) : ℝ) ^ τ
            ≤ ∑ i, weight x i * (((rank x i : ℝ) / m) ^ τ * (size x : ℝ) ^ τ) := by
              refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hweight x i)
              rw [← Real.mul_rpow (div_nonneg (Nat.cast_nonneg _) hm.le) hn0]
              exact Real.rpow_le_rpow (Nat.cast_nonneg _) (hsize x hu i) hτ
          _ = (∑ i, weight x i * ((rank x i : ℝ) / m) ^ τ) * (size x : ℝ) ^ τ := by
              rw [sum_mul]; exact sum_congr rfl fun i _ => by ring
          _ ≤ qτ * (size x : ℝ) ^ τ :=
              mul_le_mul_of_nonneg_right (hmomτ x hu) (Real.rpow_nonneg hn0 _)
      have hsum : ∑ i, weight x i * cost (child x i) ≤
          A * (q₁ * size x) + B * ((qτ * (size x : ℝ) ^ τ) * L) := by
        calc ∑ i, weight x i * cost (child x i)
            ≤ ∑ i, weight x i * (A * size (child x i) + B * ((size (child x i) : ℝ) ^ τ * L)) :=
              sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hchild i) (hweight x i)
          _ = A * ∑ i, weight x i * (size (child x i) : ℝ) +
                B * ((∑ i, weight x i * (size (child x i) : ℝ) ^ τ) * L) := by
              rw [mul_sum, sum_mul, mul_sum, ← sum_add_distrib]
              exact sum_congr rfl fun i _ => by ring
          _ ≤ A * (q₁ * size x) + B * ((qτ * (size x : ℝ) ^ τ) * L) := by
              gcongr
      have h1 := hnode x hu
      have hL' : C * L ≤ C * ((size x : ℝ) ^ τ * L) := by
        have := mul_le_mul_of_nonneg_right (hone x) hL
        rw [one_mul] at this
        exact mul_le_mul_of_nonneg_left this hC
      calc cost x ≤ A * (q₁ * size x) + B * ((qτ * (size x : ℝ) ^ τ) * L) + C * size x + C * L := by
            linarith
        _ ≤ A * (q₁ * size x) + B * ((qτ * (size x : ℝ) ^ τ) * L) + C * size x +
              C * ((size x : ℝ) ^ τ * L) := by linarith
        _ = (A * q₁ + C) * size x + (B * qτ + C) * ((size x : ℝ) ^ τ * L) := by ring
        _ = A * size x + B * ((size x : ℝ) ^ τ * L) := by rw [hAq, hBq]
    · have hl := hleaf x (Nat.lt_of_not_le hu)
      have h2 : C * L ≤ B * ((size x : ℝ) ^ τ * L) := by
        have h3 : L ≤ (size x : ℝ) ^ τ * L := by
          have := mul_le_mul_of_nonneg_right (hone x) hL
          rwa [one_mul] at this
        calc C * L ≤ B * L := mul_le_mul_of_nonneg_right hCB hL
          _ ≤ B * ((size x : ℝ) ^ τ * L) := mul_le_mul_of_nonneg_left h3 hB0
      have h4 : 0 ≤ A * size x := mul_nonneg hA0 (Nat.cast_nonneg _)
      linarith

end IntegerMultBounds.MathlibTM2.M8.StoppedRecurrence
