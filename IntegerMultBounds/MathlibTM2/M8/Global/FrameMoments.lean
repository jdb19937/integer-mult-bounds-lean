module

public import IntegerMultBounds.MathlibTM2.M8.Global.Cost

/-! Frame-chain moments independent of any concrete local word or supplier.
Computed design-B frames reuse the same definitions as the existing node,
without importing that node's semantics or creating an import cycle. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Global

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open Classical

variable {d : ℕ} {M : Type} [AddCommMonoid M]

/-- One step of a frame sequence: no move between equal frames. -/
def stepMoment (φ : ℕ → M) (A B : Mat d) : M := if A = B then 0 else φ (moveRank A B)

/-- The moment of the moves along a frame sequence. -/
def chainMoment (φ : ℕ → M) : List (Mat d) → M
  | a :: b :: l => stepMoment φ a b + chainMoment φ (b :: l)
  | _ => 0

theorem rank_neg {d : ℕ} (A : Mat d) : (-A).rank = A.rank := by
  have h : ∀ B : Mat d, (-B).rank ≤ B.rank := fun B => by
    rw [← neg_one_mul]
    exact Matrix.rank_mul_le_right _ _
  exact le_antisymm (h A) (by simpa using h (-A))

theorem moveRank_eq (A B : Mat d) : moveRank A B = (A - B).rank := by
  unfold moveRank
  split_ifs with h1 h2
  · subst h1; simp
  · rw [← neg_sub, rank_neg]
  · rfl

theorem eq_zero_of_rank_eq_zero {E : Mat d} (h : E.rank = 0) : E = 0 := by
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
  ext i j
  have := congrFun (LinearMap.congr_fun h (Pi.single j 1)) i
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single] using this

theorem rank_sub_comm (A B : Mat d) : (A - B).rank = (B - A).rank := by
  rw [← neg_sub, rank_neg]

theorem stepMoment_eq {M : Type} [AddCommMonoid M] (φ : ℕ → M) (A B : Mat d) :
    stepMoment φ A B = if A = B then 0 else φ (A - B).rank := by
  rw [stepMoment, moveRank_eq]

theorem chainMoment_cons_cons (φ : ℕ → M) (a b : Mat d) (l : List (Mat d)) :
    chainMoment φ (a :: b :: l) = stepMoment φ a b + chainMoment φ (b :: l) := rfl

end

end IntegerMultBounds.MathlibTM2.M8.Global
