module

public import IntegerMultBounds.MathlibTM2.Binary
public import IntegerMultBounds.Machine

/-!
# Tapes as pairs of stacks

A tape with its head is stored as two stacks: the cells left of the head, nearest first, and
the cells from the head rightwards. Cells beyond either stack are blank. One transition of an
`IntegerMultBounds.Machine.Program` changes each pair by a bounded number of pushes and pops.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2

open IntegerMultBounds.Machine

instance : Fintype Move := Fintype.ofList [.left, .stay, .right] (by intro m; cases m <;> simp)

variable {S : Type}


/-- The cell at offset `d` from the head. -/
def readAt (blank : S) (L R : List S) (d : ℤ) : S :=
  if 0 ≤ d then (R[d.toNat]?).getD blank else (L[(-d - 1).toNat]?).getD blank

/-- The two stacks after writing `w` under the head and moving. -/
def stepStacks (blank : S) (L R : List S) (w : S) : Move → List S × List S
  | .right => (w :: L, R.tail)
  | .stay => (L, w :: R.tail)
  | .left => (L.tail, L.head?.getD blank :: w :: R.tail)

lemma readAt_nonneg (blank : S) (L R : List S) (k : ℕ) :
    readAt blank L R k = (R[k]?).getD blank := by
  simp [readAt]

lemma readAt_neg (blank : S) (L R : List S) (k : ℕ) :
    readAt blank L R (-(k + 1 : ℕ)) = (L[k]?).getD blank := by
  simp only [readAt]
  rw [ite_eq_right (by omega)]
  congr 2
  omega

/-- Every integer is `k` or `-(k+1)` for a natural `k`. -/
lemma int_cases (d : ℤ) : (∃ k : ℕ, d = k) ∨ ∃ k : ℕ, d = -(k + 1 : ℕ) := by
  rcases Int.eq_nat_or_neg d with ⟨k, rfl | rfl⟩
  · exact .inl ⟨k, rfl⟩
  · rcases k with _ | k
    · exact .inl ⟨0, by simp⟩
    · exact .inr ⟨k, by push_cast; ring⟩

theorem readAt_step (blank : S) (L R : List S) (w : S) (m : Move) (d : ℤ) :
    readAt blank (stepStacks blank L R w m).1 (stepStacks blank L R w m).2 (d - m.offset) =
      if d = 0 then w else readAt blank L R d := by
  rcases int_cases d with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · cases m with
    | right =>
        rcases k with _ | k
        · simp only [stepStacks, Move.offset, Nat.cast_zero, zero_sub, ite_true]
          rw [show (-1 : ℤ) = -((0 : ℕ) + 1 : ℕ) by norm_num, readAt_neg]
          simp
        · rw [ite_eq_right (by omega), show ((k + 1 : ℕ) : ℤ) - Move.offset .right = (k : ℕ) by
            simp [Move.offset]]
          simp only [stepStacks, readAt_nonneg, List.getElem?_tail]
    | stay =>
        rcases k with _ | k
        · simp [stepStacks, Move.offset, readAt]
        · rw [ite_eq_right (by omega), show ((k + 1 : ℕ) : ℤ) - Move.offset .stay = ((k + 1 : ℕ) : ℤ) by
            simp [Move.offset]]
          simp only [stepStacks, readAt_nonneg, List.getElem?_cons_succ, List.getElem?_tail]
    | left =>
        rw [show ((k : ℕ) : ℤ) - Move.offset .left = ((k + 1 : ℕ) : ℤ) by
          simp [Move.offset]]
        rcases k with _ | k
        · simp [stepStacks, readAt]
        · rw [ite_eq_right (by omega)]
          simp only [stepStacks, readAt_nonneg, List.getElem?_cons_succ, List.getElem?_tail]
  · rw [ite_eq_right (by omega)]
    cases m with
    | right =>
        rw [show -((k + 1 : ℕ) : ℤ) - Move.offset .right = -((k + 1 + 1 : ℕ) : ℤ) by
          push_cast [Move.offset]; ring]
        simp only [stepStacks, readAt_neg, List.getElem?_cons_succ]
    | stay =>
        rw [show -((k + 1 : ℕ) : ℤ) - Move.offset .stay = -((k + 1 : ℕ) : ℤ) by
          simp [Move.offset]]
        simp only [stepStacks, readAt_neg]
    | left =>
        rcases k with _ | k
        · rw [show -(((0 : ℕ) + 1 : ℕ) : ℤ) - Move.offset .left = ((0 : ℕ) : ℤ) by
            simp [Move.offset]]
          simp only [stepStacks, readAt_nonneg, readAt_neg]
          cases L <;> simp
        · rw [show -((k + 1 + 1 : ℕ) : ℤ) - Move.offset .left = -((k + 1 : ℕ) : ℤ) by
            push_cast [Move.offset]; ring]
          simp only [stepStacks, readAt_neg, List.getElem?_tail]

/-- The stacks `L i`, `R i` represent tape `i` of a configuration. -/
def Rep {t q a : ℕ} (c : Config t q a) (L R : Fin t → List (Fin (a + 4))) : Prop :=
  ∀ i j, c.tape i j = readAt blank (L i) (R i) (j - c.head i)

/-- The scanned cell is the top of the right stack. -/
lemma rep_scan {t q a : ℕ} {c : Config t q a} {L R : Fin t → List (Fin (a + 4))}
    (h : Rep c L R) (i : Fin t) : c.tape i (c.head i) = ((R i).head?).getD blank := by
  rw [h i, sub_self, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, readAt_nonneg]
  cases R i <;> rfl

/-- One transition preserves the representation, with each tape's stacks updated by
`stepStacks`. -/
theorem rep_step {t q a : ℕ} {M : Program t q a} {c : Config t q a}
    {L R : Fin t → List (Fin (a + 4))} (h : Rep c L R) {st : Fin q}
    {act : Fin t → Fin (a + 4) × Move}
    (ht : M.transition c.state (fun i => c.tape i (c.head i)) = some (st, act)) :
    ∃ c', step M c = some c' ∧ c'.state = st ∧
      Rep c' (fun i => (stepStacks blank (L i) (R i) (act i).1 (act i).2).1)
        (fun i => (stepStacks blank (L i) (R i) (act i).1 (act i).2).2) := by
  refine ⟨⟨st, (fun i => c.head i + (act i).2.offset),
      (fun i j => if j = c.head i then (act i).1 else c.tape i j)⟩, ?_, rfl, ?_⟩
  · simp only [step, ht]
  intro i j
  simp only
  rw [show j - (c.head i + (act i).2.offset) = (j - c.head i) - (act i).2.offset by ring,
    readAt_step, ← h i]
  by_cases hj : j = c.head i
  · simp [hj]
  · simp [hj, sub_eq_zero]

/-- The stored cells of a tape, leftmost first, are a contiguous window of the tape. -/
theorem window_eq (blank : S) (L R : List S) (h : ℤ) (T : ℤ → S)
    (hT : ∀ j, T j = readAt blank L R (j - h)) :
    L.reverse ++ R = (List.range (L.length + R.length)).map (fun i : ℕ => T (h - L.length + (i : ℤ))) := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp only [List.getElem_map, List.getElem_range, hT]
  by_cases hi : i < L.length
  · rw [List.getElem_append_left (by simpa using hi), List.getElem_reverse,
      show h - (L.length : ℤ) + (i : ℤ) - h = -((L.length - 1 - i : ℕ) + 1 : ℕ) by omega, readAt_neg,
      List.getElem?_eq_getElem (by omega)]
    rfl
  · rw [List.getElem_append_right (by simpa using hi),
      show h - (L.length : ℤ) + (i : ℤ) - h = ((i - L.length : ℕ) : ℤ) by omega, readAt_nonneg,
      List.getElem?_eq_getElem (by simp at h₁; omega)]
    simp

end IntegerMultBounds.MathlibTM2
