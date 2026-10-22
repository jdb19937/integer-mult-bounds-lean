module

public import IntegerMultBounds.MathlibTM2.M8.Global.ChainMoments

/-! Linear moments telescope, and pointwise rank bounds pass to chain moments. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open Classical
variable {d : Nat}

theorem stepMoment_nat_cast (φ : Nat → Nat) (A B : Mat d) :
    stepMoment (fun r => (φ r : ℝ)) A B = ((stepMoment φ A B : Nat) : ℝ) := by
  rw [stepMoment, stepMoment]
  split_ifs <;> simp

theorem chainMoment_nat_cast (φ : Nat → Nat) : ∀ fs : List (Mat d),
    chainMoment (fun r => (φ r : ℝ)) fs = ((chainMoment φ fs : ℕ) : ℝ)
  | [] => by simp [chainMoment]
  | [_] => by simp [chainMoment]
  | a :: b :: fs => by
    rw [chainMoment_cons_cons, chainMoment_cons_cons, chainMoment_nat_cast φ (b :: fs), Nat.cast_add,
      stepMoment, stepMoment]
    split_ifs <;> simp

theorem chainMoment_nat_scale_le {φ ψ : Nat → Nat} {c : Nat} (h : ∀ r, c * φ r ≤ ψ r) :
    ∀ fs : List (Mat d), c * chainMoment φ fs ≤ chainMoment ψ fs
  | [] => by simp [chainMoment]
  | [_] => by simp [chainMoment]
  | a :: b :: fs => by
    rw [chainMoment_cons_cons, chainMoment_cons_cons, mul_add]
    apply Nat.add_le_add ?_ (chainMoment_nat_scale_le h (b :: fs))
    rw [stepMoment, stepMoment]
    split_ifs
    · simp
    · exact h _

private theorem chainMoment_id : ∀ fs : List (Mat d), chainMoment (fun r => r) fs = chainCost fs
  | [] => rfl
  | [_] => rfl
  | a :: b :: fs => by
    rw [chainMoment_cons_cons, chainCost_cons_cons, chainMoment_id (b :: fs)]
    unfold stepMoment
    split_ifs with h
    · subst b
      simp [moveRank]
    · rfl

/-- The complete moment of an increasing path is its rise in rank. -/
theorem chainMoment_linear (a b : Mat d) (fs : List (Mat d))
    (hp : (a :: (fs ++ [b])).Pairwise Le)
    (hi : ∀ F ∈ a :: (fs ++ [b]), F * F = F) :
    chainMoment (fun r => (r : ℝ)) (a :: (fs ++ [b])) = (b.rank : ℝ) - a.rank := by
  have h := chainCost_mono (fs ++ [b]) a hp.isChain hi
  have he : (a :: (fs ++ [b])).getLast (by simp) = b := by simp
  rw [he] at h
  have h' : (chainCost (a :: (fs ++ [b])) : ℝ) + a.rank = b.rank := by exact_mod_cast h
  rw [chainMoment_nat_cast, chainMoment_id]
  linarith

/-- The linear moment is the total number of rank-one interchanges. -/
theorem edgeMoment_linear {ι : Type} (L : List (FStep ι d)) :
    edgeMoment (fun r => (r : ℝ)) L = (edgeRanks L : ℝ) := by
  induction L with
  | nil => simp [edgeMoment, edgeRanks]
  | cons s L ih => cases s <;> simp [edgeMoment, edgeRanks, ih]

end
end IntegerMultBounds.MathlibTM2.M8.Global
