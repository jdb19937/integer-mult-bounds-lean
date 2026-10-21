module

public import IntegerMultBounds.MathlibTM2.M8.Global.LocalSteps
public import IntegerMultBounds.MathlibTM2.M8.Stage2Moments
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The node's moves against the stage-2 histogram

For a nonnegative, monotone, subadditive `φ` with `φ 0 = 0`, the moment of the node's moves is at
most the moment of the stage-2 histogram (`edgeMoment_le_histogram`): the bound of
`Global.node_moment_le`, with the side slots' local moves the local-step histogram
(`Global.sum_localMoment_eq`), is the histogram row by row.

At `φ r = (r/m)^τ / W` this gives the two moment gaps of the stopped recurrence for the node's
moves: the linear moment is at most `q₁` (`linear_premise`) and the `τ*`-moment below `q_τ`
(`tau_premise`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Moments

open Global
open Global.Branching97 (width roleCount)

noncomputable section

/-- The moment of the histogram's rows. -/
def histMoment (φ : ℕ → ℝ) (rows : List Row) : ℝ := (rows.map fun row => (row.2.1 : ℝ) * φ row.1).sum

theorem card_slot : Fintype.card Slot = 28866 := by
  rw [Fintype.card_fin, slot_count]

/-- **The node's moves against the stage-2 histogram.** -/
theorem edgeMoment_le_histogram (φ : ℕ → ℝ) (hnn : ∀ n, 0 ≤ φ n) (hmono : Monotone φ)
    (hsub : ∀ a b, φ (a + b) ≤ φ a + φ b) (hz : φ 0 = 0) :
    edgeMoment φ framedNode ≤ histMoment φ histogram := by
  have h := node_moment_le φ hnn hmono hsub
  rw [Finset.sum_add_distrib, sum_localMoment_eq φ hz, Finset.sum_const, Finset.card_univ,
    card_slot, nsmul_eq_mul] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Local.localSteps, List.getD_cons_succ,
    List.getD_cons_zero, hz] at h
  simp only [histMoment, histogram, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast at h ⊢
  linarith

theorem rpow_add_le {x y τ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (x + y) ^ τ ≤ x ^ τ + y ^ τ := by
  lift x to NNReal using hx
  lift y to NNReal using hy
  exact_mod_cast NNReal.rpow_add_le_add_rpow x y hτ0 hτ1

theorem rpow_sub_add {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (a b : ℕ) :
    (((a + b : ℕ) : ℝ) / 529) ^ τ / roleCount ≤
      ((a : ℝ) / 529) ^ τ / roleCount + ((b : ℝ) / 529) ^ τ / roleCount := by
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (by norm_num [roleCount])
  push_cast
  rw [add_div]
  exact rpow_add_le (by positivity) (by positivity) hτ0 hτ1

/-- The moment of the histogram at `φ r = (r/m)^τ / W`. -/
theorem histMoment_rpow (τ : ℝ) : ∀ rows : List Row,
    histMoment (fun r => ((r : ℝ) / 529) ^ τ / roleCount) rows = moment τ rows
  | [] => by simp [histMoment, moment]
  | row :: rows => by
    have := histMoment_rpow τ rows
    simp only [histMoment, List.map_cons, List.sum_cons] at this ⊢
    rw [this, moment, show (width : ℝ) = 529 by norm_num [width]]
    ring

theorem edgeMoment_rpow_le {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    edgeMoment (fun r => ((r : ℝ) / 529) ^ τ / roleCount) framedNode ≤ moment τ histogram := by
  rw [← histMoment_rpow]
  refine edgeMoment_le_histogram _ (fun n => by positivity) (fun a b hab => ?_)
    (rpow_sub_add hτ0.le hτ1) (by simp [Real.zero_rpow hτ0.ne'])
  refine div_le_div_of_nonneg_right ?_ (by norm_num [roleCount])
  exact Real.rpow_le_rpow (by positivity)
    (div_le_div_of_nonneg_right (by exact_mod_cast hab) (by norm_num)) hτ0.le

/-- **The linear moment premise** for the node's moves. -/
theorem linear_premise :
    edgeMoment (fun r => ((r : ℝ) / 529) ^ (1 : ℝ) / roleCount) framedNode ≤ q₁ := by
  have h := edgeMoment_rpow_le (τ := 1) one_pos le_rfl
  rw [linear_moment] at h
  exact_mod_cast h

/-- **The `τ*`-moment premise** for the node's moves, at `τ* = 1 - 969/10⁷`. -/
theorem tau_premise :
    edgeMoment (fun r => ((r : ℝ) / 529) ^ (1 - (saving : ℝ)) / roleCount) framedNode < qτ := by
  have hs : (saving : ℝ) = 969 / 10 ^ 7 := by norm_num [saving]
  have h := edgeMoment_rpow_le (τ := 1 - (saving : ℝ)) (by rw [hs]; norm_num)
    (by rw [hs]; norm_num)
  exact h.trans_lt tau_moment

end

end IntegerMultBounds.MathlibTM2.M8.Stage2Moments
