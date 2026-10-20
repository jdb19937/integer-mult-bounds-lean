module

public import IntegerMultBounds.NLogN.ResamplingInverse
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! The row indices `[tj/s]`, `0 ≤ j < s`, of the row-selecting map `C` of the
resampling interface: `q s t j` is `[tj/s]` as a natural-number division, strictly
increasing below `t`, and filtering `range t` by these indices enumerates them in
order. -/

@[expose] public section

namespace IntegerMultBounds.Resampling.RowSelect

open IntegerMultBounds.NLogN (rowIndexNat nearest)

/-! ### The index identity -/

section Index

/-- `[tj/s]` as a natural-number division. -/
def q (s t j : ℕ) : ℕ := (2 * (t * j) + s) / (2 * s)

/-- The indices are strictly increasing. -/
theorem q_strictMono (s t j k : ℕ) (hs : 0 < s) (hst : s < t) (hjk : j < k) : q s t j < q s t k := by
  have h2s : 0 < 2 * s := by omega
  have hk : 2 * (t * j) + s + 2 * s ≤ 2 * (t * k) + s := by nlinarith
  calc q s t j < q s t j + 1 := Nat.lt_succ_self _
    _ = (2 * (t * j) + s + 2 * s) / (2 * s) := (Nat.add_div_right _ h2s).symm
    _ ≤ q s t k := Nat.div_le_div_right hk

theorem q_lt (s t j : ℕ) (hs : 0 < s) (hst : s < t) (hj : j < s) : q s t j < t := by
  have h2s : 0 < 2 * s := by omega
  rw [q, Nat.div_lt_iff_lt_mul h2s]
  have : t * j + t ≤ t * s := by nlinarith
  nlinarith

/-- The paper's row index is `q`. -/
theorem rowIndexNat_eq (s t j : ℕ) (hs : 0 < s) (hj : j < s) :
    rowIndexNat s t (j : ZMod s) = q s t j := by
  have : NeZero s := ⟨by omega⟩
  unfold rowIndexNat q nearest
  rw [ZMod.val_natCast_of_lt hj]
  have hreal : (t : ℝ) * j / s + 1 / 2 = ((2 * (t * j) + s : ℕ) : ℝ) / ((2 * s : ℕ) : ℝ) := by
    have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    push_cast
    field_simp
  rw [hreal, Int.floor_div_natCast, Int.floor_natCast, ← Int.natCast_div, Int.toNat_natCast]

end Index

/-! ### Filtering a range by a strictly increasing enumeration -/

section Lists

theorem eq_of_pairwise_lt {l₁ l₂ : List ℕ} (h₁ : l₁.Pairwise (· < ·)) (h₂ : l₂.Pairwise (· < ·))
    (hm : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons b l => exact absurd ((hm b).mpr (List.mem_cons_self)) List.not_mem_nil
  | cons a l ih =>
    cases l₂ with
    | nil => exact absurd ((hm a).mp List.mem_cons_self) List.not_mem_nil
    | cons b l' =>
      rw [List.pairwise_cons] at h₁ h₂
      have hab : a = b := by
        have ha : a ∈ b :: l' := (hm a).mp List.mem_cons_self
        have hb : b ∈ a :: l := (hm b).mpr List.mem_cons_self
        rcases List.mem_cons.mp ha with rfl | ha
        · rfl
        · rcases List.mem_cons.mp hb with rfl | hb
          · rfl
          · have := h₁.1 b hb
            have := h₂.1 a ha
            omega
      subst hab
      congr 1
      refine ih h₁.2 h₂.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
      · rcases List.mem_cons.mp ((hm x).mp (List.mem_cons_of_mem _ hx)) with rfl | h
        · exact absurd (h₁.1 x hx) (lt_irrefl _)
        · exact h
      · rcases List.mem_cons.mp ((hm x).mpr (List.mem_cons_of_mem _ hx)) with rfl | h
        · exact absurd (h₂.1 x hx) (lt_irrefl _)
        · exact h

/-- Filtering `range t` by membership in a strictly increasing enumeration
below `t` gives the enumeration. -/
theorem filter_range_eq_map (f : ℕ → ℕ) (s t : ℕ) (hmono : ∀ j k, j < k → k < s → f j < f k)
    (hlt : ∀ j, j < s → f j < t) :
    (List.range t).filter (fun i => decide (∃ j < s, f j = i)) = (List.range s).map f := by
  refine eq_of_pairwise_lt (List.pairwise_lt_range.filter _) ?_ fun x => ?_
  · rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp_of_mem fun {j k} _ hk hjk =>
      hmono j k hjk (List.mem_range.mp hk)
  · simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, List.mem_map]
    constructor
    · rintro ⟨-, j, hj, rfl⟩
      exact ⟨j, hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨hlt j hj, j, hj, rfl⟩

end Lists

-- The ordered selection machine run (`rowSelect_hoare`) was unused; restore from 5e86d444.

end IntegerMultBounds.Resampling.RowSelect
