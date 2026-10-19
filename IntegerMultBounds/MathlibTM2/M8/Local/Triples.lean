module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.IntervalCases

/-!
# The parity identity of the PR97 roots

The side DAG of the PR97 word has two kinds of roots for a point `c`: the outputs `(c, T)`, for a
triple `T ∋ c`, whose support is the triples meeting `T` exactly in `c`, and the retained centre
of `c`, whose support is the triples through `c`. Target `y_T` receives the three outputs `(c, T)`
and the three centres of the points `c ∈ T`. Over `𝔽₂` a triple `S` with `|S ∩ T| = k` is counted
`[k = 1] + k` times, which is odd exactly when `k = 3`, that is `S = T` (`root_parity`). So the
target receives exactly `x_T`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Local

open Finset

variable {α : Type*} [DecidableEq α]

/-- The outputs `(c, T)`, `c ∈ T`, whose support contains `S`. -/
theorem out_count (S T : Finset α) :
    (T.filter fun c => c ∈ S ∧ S ∩ T = {c}).card = if (S ∩ T).card = 1 then 1 else 0 := by
  split_ifs with h
  · obtain ⟨c, hc⟩ := Finset.card_eq_one.mp h
    have hf : (T.filter fun c' => c' ∈ S ∧ S ∩ T = {c'}) = {c} := by
      ext x
      rw [Finset.mem_filter, Finset.mem_singleton, hc]
      constructor
      · rintro ⟨_, _, hx⟩
        exact (Finset.singleton_injective hx).symm
      · rintro rfl
        have hcm : x ∈ S ∩ T := by rw [hc]; exact Finset.mem_singleton_self x
        exact ⟨(Finset.mem_inter.mp hcm).2, (Finset.mem_inter.mp hcm).1, rfl⟩
    rw [hf, Finset.card_singleton]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro c - ⟨_, hS⟩
    exact h (by rw [hS, Finset.card_singleton])

/-- The centres of the points `c ∈ T` whose support contains `S`. -/
theorem star_count (S T : Finset α) : (T.filter fun c => c ∈ S).card = (S ∩ T).card := by
  rw [Finset.filter_mem_eq_inter, Finset.inter_comm]

/-- `[k = 1] + k` is odd exactly at `k = 3`, for `k ≤ 3`. -/
theorem parity_small (k : ℕ) (hk : k ≤ 3) :
    (((if k = 1 then 1 else 0) + k : ℕ) : ZMod 2) = if k = 3 then 1 else 0 := by
  interval_cases k <;> decide

/-- **Root parity.** For triples `S` and `T`, the outputs and centres of `T` count `S` an odd
number of times exactly when `S = T`. -/
theorem root_parity (S T : Finset α) (hS : S.card = 3) (hT : T.card = 3) :
    (((T.filter fun c => c ∈ S ∧ S ∩ T = {c}).card + (T.filter fun c => c ∈ S).card : ℕ) :
      ZMod 2) = if S = T then 1 else 0 := by
  rw [out_count, star_count]
  have hle : (S ∩ T).card ≤ 3 := hS ▸ card_le_card inter_subset_left
  have h3 : (S ∩ T).card = 3 ↔ S = T := by
    constructor
    · intro h
      have h1 : S ∩ T = S := eq_of_subset_of_card_le inter_subset_left (by rw [h, hS])
      have h2 : S ∩ T = T := eq_of_subset_of_card_le inter_subset_right (by rw [h, hT])
      rw [← h1, h2]
    · rintro rfl
      rw [inter_self, hS]
  rw [parity_small _ hle]
  exact if_congr h3 rfl rfl

end IntegerMultBounds.MathlibTM2.M8.Local
