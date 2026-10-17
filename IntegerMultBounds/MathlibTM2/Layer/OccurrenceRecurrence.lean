module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# A recurrence for individual variable-rank child calls

Unlike `Layer.Recurrence`, this bound permits different child sizes at one node.
The index `Fin (arity x)` names call occurrences, so repeated calls are charged
separately even when their states agree. The caller must supply the actual cost
recurrence, child-size decrease, and the rank/size relation for every occurrence.
A rank histogram alone supplies none of those execution premises.

The moment is the occurrence version of the selected construction's bill
`sum (r/m)^(1-a) / W`, described in `docs/research/bottleneck-brief.md` at upstream
CrocSwap/integer-mult-bounds revision 0fdd7d82de03e43c9e5a1000dfbcd380d1b687d2
(the pin and digest are recorded in `docs/sharper-bound-source.json`). This is an
independent analytic bridge, not an implementation or runtime theorem for either
selected supplier. Nonrecursive costs must include all local execution charges.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Layer.OccurrenceRecurrence

open Finset

/-- A potential bounds the cost of each actual node when every child occurrence
is smaller, local cost fits the unused potential, and the weighted child
potentials contract. No injectivity of `child` is assumed. -/
theorem cost_le_potential {Node : Type*}
    (size : Node → ℕ) (arity : Node → ℕ)
    (child : (x : Node) → Fin (arity x) → Node)
    (weight : (x : Node) → Fin (arity x) → ℝ)
    (cost overhead potential : Node → ℝ) (cutoff : ℕ) (C q : ℝ)
    (hC : 0 ≤ C)
    (hweight : ∀ x i, 0 ≤ weight x i)
    (hleaf : ∀ x, size x ≤ cutoff → cost x ≤ C * potential x)
    (hdecrease : ∀ x, cutoff < size x → ∀ i, size (child x i) < size x)
    (hcost : ∀ x, cutoff < size x →
      cost x ≤ overhead x + ∑ i, weight x i * cost (child x i))
    (hoverhead : ∀ x, cutoff < size x → overhead x ≤ C * (1 - q) * potential x)
    (hmoment : ∀ x, cutoff < size x →
      ∑ i, weight x i * potential (child x i) ≤ q * potential x) :
    ∀ x, cost x ≤ C * potential x := by
  intro x
  induction hn : size x using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases hsmall : size x ≤ cutoff
    · exact hleaf x hsmall
    · have hlarge : cutoff < size x := Nat.lt_of_not_ge hsmall
      have hchildren : ∑ i, weight x i * cost (child x i) ≤
          C * ∑ i, weight x i * potential (child x i) := by
        calc _ ≤ ∑ i, weight x i * (C * potential (child x i)) := by
               apply sum_le_sum
               intro i _
               apply mul_le_mul_of_nonneg_left _ (hweight x i)
               exact ih (size (child x i)) (hn ▸ hdecrease x hlarge i) (child x i) rfl
             _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro i _; ring
      calc cost x ≤ overhead x + ∑ i, weight x i * cost (child x i) := hcost x hlarge
        _ ≤ C * (1 - q) * potential x + C * (q * potential x) :=
          add_le_add (hoverhead x hlarge)
            (hchildren.trans (mul_le_mul_of_nonneg_left (hmoment x hlarge) hC))
        _ = C * potential x := by ring

/-- Per-occurrence ranks control the sum of child power potentials. `rank i`
and `childSize i` refer to the same occurrence, not independently sorted lists. -/
theorem rank_moment_le {n : ℕ} (rank childSize : Fin n → ℕ) (weight : Fin n → ℝ)
    {parentSize m σ q : ℝ} (hparent : 0 ≤ parentSize) (hm : 0 < m) (hσ : 0 ≤ σ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hsize : ∀ i, (childSize i : ℝ) ≤ ((rank i : ℝ) / m) * parentSize)
    (hmoment : ∑ i, weight i * ((rank i : ℝ) / m) ^ σ ≤ q) :
    ∑ i, weight i * (childSize i : ℝ) ^ σ ≤ q * parentSize ^ σ := by
  calc _ ≤ ∑ i, weight i * (((rank i : ℝ) / m) * parentSize) ^ σ := by
           apply sum_le_sum
           intro i _
           exact mul_le_mul_of_nonneg_left
             (Real.rpow_le_rpow (Nat.cast_nonneg _) (hsize i) hσ) (hweight i)
       _ = (∑ i, weight i * ((rank i : ℝ) / m) ^ σ) * parentSize ^ σ := by
           rw [sum_mul]
           apply sum_congr rfl
           intro i _
           rw [Real.mul_rpow (div_nonneg (Nat.cast_nonneg _) hm.le) hparent]
           ring
       _ ≤ q * parentSize ^ σ :=
           mul_le_mul_of_nonneg_right hmoment (Real.rpow_nonneg hparent σ)

/-- A variable-rank execution costs at most `C * size^σ` when its actual
per-occurrence moment leaves room for every local overhead charge. The natural
size decrease is independent of the real-valued rank bound, accommodating
integer rounding when that bound has been proved by the caller. -/
theorem cost_le_rank_power {Node : Type*}
    (size : Node → ℕ) (arity : Node → ℕ)
    (child : (x : Node) → Fin (arity x) → Node)
    (rank : (x : Node) → Fin (arity x) → ℕ)
    (weight : (x : Node) → Fin (arity x) → ℝ)
    (cost overhead : Node → ℝ) (cutoff : ℕ) {m σ C q : ℝ}
    (hm : 0 < m) (hσ : 0 ≤ σ) (hC : 0 ≤ C)
    (hweight : ∀ x i, 0 ≤ weight x i)
    (hleaf : ∀ x, size x ≤ cutoff → cost x ≤ C * (size x : ℝ) ^ σ)
    (hdecrease : ∀ x, cutoff < size x → ∀ i, size (child x i) < size x)
    (hsize : ∀ x, cutoff < size x → ∀ i,
      (size (child x i) : ℝ) ≤ ((rank x i : ℝ) / m) * (size x : ℝ))
    (hcost : ∀ x, cutoff < size x →
      cost x ≤ overhead x + ∑ i, weight x i * cost (child x i))
    (hoverhead : ∀ x, cutoff < size x → overhead x ≤ C * (1 - q) * (size x : ℝ) ^ σ)
    (hmoment : ∀ x, cutoff < size x →
      ∑ i, weight x i * ((rank x i : ℝ) / m) ^ σ ≤ q) :
    ∀ x, cost x ≤ C * (size x : ℝ) ^ σ := by
  apply cost_le_potential size arity child weight cost overhead
    (fun x => (size x : ℝ) ^ σ) cutoff C q hC hweight hleaf hdecrease hcost hoverhead
  intro x hx
  exact rank_moment_le (rank x) (fun i => size (child x i)) (weight x)
    (Nat.cast_nonneg _) hm hσ (hweight x) (hsize x hx) (hmoment x hx)

/-- With equal child volume `1/W`, the occurrence moment is precisely the
selected rank bill; equal ranks are still charged once per occurrence. -/
theorem uniform_volume_moment {n : ℕ} (rank : Fin n → ℕ) (m W σ : ℝ) :
    (∑ i, (1 / W) * ((rank i : ℝ) / m) ^ σ) =
      (∑ i, ((rank i : ℝ) / m) ^ σ) / W := by
  rw [sum_div]
  apply sum_congr rfl
  intro i _
  ring

end IntegerMultBounds.MathlibTM2.Layer.OccurrenceRecurrence
