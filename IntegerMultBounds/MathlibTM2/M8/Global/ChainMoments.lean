module

public import IntegerMultBounds.MathlibTM2.M8.Global.MoveMoments

/-!
# Moments along frame chains

The rank of a move is the rank of the difference of its frames, in either order (`moveRank_eq`),
so a frame chain has the same moment reversed (`chainMoment_reverse`) and complemented
(`chainMoment_compl`). For a function `φ` with `φ (a + b) ≤ φ a + φ b`,
inserting an intermediate nested frame never lowers the moment (`chainMoment_insert`): a move
through it splits into two moves whose ranks add up. A nested chain through two frames makes one
move (`chainMoment_two`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Global

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open Classical

variable {d : ℕ}

/-! ### Ranks of differences -/

theorem stepMoment_comm {M : Type} [AddCommMonoid M] (φ : ℕ → M) (A B : Mat d) :
    stepMoment φ A B = stepMoment φ B A := by
  rw [stepMoment_eq, stepMoment_eq, rank_sub_comm]
  by_cases h : A = B
  · subst h; simp
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

theorem stepMoment_compl {M : Type} [AddCommMonoid M] (φ : ℕ → M) (A B : Mat d) :
    stepMoment φ (1 - A) (1 - B) = stepMoment φ B A := by
  rw [stepMoment_eq, stepMoment_eq, sub_sub_sub_cancel_left]
  by_cases h : B = A
  · subst h; simp
  · rw [ite_eq_right h, ite_eq_right (fun e => h (sub_right_injective e).symm)]

/-! ### Chain algebra -/

variable {M : Type} [AddCommMonoid M]

theorem chainMoment_append (φ : ℕ → M) : ∀ (l₁ : List (Mat d)) (a b : Mat d) (l₂ : List (Mat d)),
    chainMoment φ (l₁ ++ a :: b :: l₂) =
      chainMoment φ (l₁ ++ [a]) + stepMoment φ a b + chainMoment φ (b :: l₂)
  | [], a, b, l₂ => by simp [chainMoment_cons_cons, chainMoment]
  | [x], a, b, l₂ => by
    simp only [List.cons_append, List.nil_append, chainMoment_cons_cons]
    simp [chainMoment, add_assoc]
  | x :: y :: l₁, a, b, l₂ => by
    simp only [List.cons_append, chainMoment_cons_cons]
    have := chainMoment_append φ (y :: l₁) a b l₂
    simp only [List.cons_append] at this
    rw [this, add_assoc, add_assoc, add_assoc]

theorem chainMoment_snoc (φ : ℕ → M) : ∀ (l : List (Mat d)) (a b : Mat d),
    chainMoment φ (l ++ [a, b]) = chainMoment φ (l ++ [a]) + stepMoment φ a b := by
  intro l a b
  have := chainMoment_append φ l a b []
  simpa [chainMoment] using this

theorem chainMoment_map (φ : ℕ → M) (f : Mat d → Mat d) (hf : ∀ A B, stepMoment φ (f A) (f B) = stepMoment φ A B) :
    ∀ l : List (Mat d), chainMoment φ (l.map f) = chainMoment φ l
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
    rw [List.map_cons, List.map_cons, chainMoment_cons_cons, ← List.map_cons,
      chainMoment_map φ f hf (b :: l), hf, chainMoment_cons_cons]

theorem chainMoment_reverse (φ : ℕ → M) : ∀ l : List (Mat d), chainMoment φ l.reverse = chainMoment φ l
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
    rw [List.reverse_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
    have h := chainMoment_append φ (l.reverse) b a []
    simp only [chainMoment, add_zero] at h
    rw [h, ← List.reverse_cons, chainMoment_reverse φ (b :: l), chainMoment_cons_cons,
      stepMoment_comm, add_comm]

theorem chainMoment_compl (φ : ℕ → M) (l : List (Mat d)) :
    chainMoment φ ((l.map (1 - ·)).reverse) = chainMoment φ l := by
  rw [chainMoment_reverse]
  exact chainMoment_map φ _ (fun A B => (stepMoment_compl φ A B).trans (stepMoment_comm φ B A)) l

/-! ### Insertion -/

theorem le_antisymm' {A B : Mat d} (h : Le A B) (h' : Le B A) : A = B := by
  rw [← h.1, h'.2]

theorem rank_split {A B C : Mat d} (hA : A * A = A) (hB : B * B = B) (hC : C * C = C)
    (hAC : Le A C) (hCB : Le C B) : (B - A).rank = (B - C).rank + (C - A).rank := by
  have h1 := rank_sub_of_le hA hB (le_trans' hAC hCB)
  have h2 := rank_sub_of_le hA hC hAC
  have h3 := rank_sub_of_le hC hB hCB
  omega

theorem stepMoment_split (φ : ℕ → ℝ) (hsub : ∀ a b, φ (a + b) ≤ φ a + φ b)
    {A B C : Mat d} (hA : A * A = A) (hB : B * B = B) (hC : C * C = C)
    (hAC : Le A C) (hCB : Le C B) :
    stepMoment φ A B ≤ stepMoment φ A C + stepMoment φ C B := by
  simp only [stepMoment_eq]
  have hr := rank_split hA hB hC hAC hCB
  by_cases hac : A = C
  · subst hac; simp
  · by_cases hcb : C = B
    · subst hcb; simp
    · have hab : A ≠ B := fun e => by subst e; exact hac (le_antisymm' hAC hCB)
      simp only [hab, hac, hcb, ↓reduceIte]
      rw [rank_sub_comm A B, rank_sub_comm A C, rank_sub_comm C B, hr, add_comm]
      exact hsub _ _

/-- **Insertion.** A frame nested between two consecutive frames does not lower the moment. -/
theorem chainMoment_insert (φ : ℕ → ℝ) (hsub : ∀ a b, φ (a + b) ≤ φ a + φ b)
    (l₁ l₂ : List (Mat d)) {A B C : Mat d} (hA : A * A = A) (hB : B * B = B) (hC : C * C = C)
    (hAC : Le A C) (hCB : Le C B) :
    chainMoment φ (l₁ ++ A :: B :: l₂) ≤ chainMoment φ (l₁ ++ A :: C :: B :: l₂) := by
  rw [chainMoment_append, chainMoment_append φ l₁ A C (B :: l₂), chainMoment_cons_cons]
  have := stepMoment_split φ hsub hA hB hC hAC hCB
  linarith

/-! ### Two frames -/

theorem chainMoment_const (φ : ℕ → M) (B : Mat d) :
    ∀ l : List (Mat d), (∀ y ∈ l, y = B) → chainMoment φ (B :: (l ++ [B])) = 0
  | [], _ => by simp [chainMoment, stepMoment]
  | y :: l, h => by
    rw [h y (by simp)]
    change stepMoment φ B B + chainMoment φ (B :: (l ++ [B])) = 0
    rw [stepMoment, ite_eq_left rfl, zero_add]
    exact chainMoment_const φ B l (fun z hz => h z (by simp [hz]))

/-- A nested chain through the two frames `A ≤ B`, from `A` to `B`, makes one move. -/
theorem chainMoment_two (φ : ℕ → M) {A B : Mat d} (hAB : Le A B) :
    ∀ l : List (Mat d), (∀ x ∈ l, x = A ∨ x = B) → (A :: (l ++ [B])).Pairwise Le →
      chainMoment φ (A :: (l ++ [B])) = stepMoment φ A B
  | [], _, _ => by simp [chainMoment]
  | x :: l, hl, hpw => by
    have hpw' : (x :: (l ++ [B])).Pairwise Le := List.Pairwise.of_cons hpw
    change stepMoment φ A x + chainMoment φ (x :: (l ++ [B])) = stepMoment φ A B
    rcases hl x (by simp) with hx | hx
    · rw [hx, stepMoment, ite_eq_left rfl, zero_add]
      rw [hx] at hpw'
      exact chainMoment_two φ hAB l (fun y hy => hl y (by simp [hy])) hpw'
    · rw [hx] at hpw' ⊢
      have hrest : ∀ y ∈ l, y = B := by
        intro y hy
        rcases hl y (by simp [hy]) with h | h
        · have hBy : Le B y := (List.pairwise_cons.mp hpw').1 y (by simp [hy])
          rw [h] at hBy ⊢
          exact le_antisymm' hAB hBy
        · exact h
      rw [chainMoment_const φ B l hrest, add_zero]

end

end IntegerMultBounds.MathlibTM2.M8.Global
