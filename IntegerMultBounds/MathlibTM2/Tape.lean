module

public import IntegerMultBounds.MathlibTM2.Binary

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

/-- The input configuration is represented by the input word on the right stack of tape 0 and
empty stacks elsewhere. -/
theorem rep_input {t q a : ℕ} (M : Program t q a) (x y : List Bool) :
    Rep (input M x y) (fun _ => [])
      (fun i => if i.val = 0 then x.map bitSymbol ++ [separator] ++ y.map bitSymbol else []) := by
  intro i j
  simp only [IntegerMultBounds.Machine.input, sub_zero]
  rcases int_cases j with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [readAt_nonneg]
    split_ifs <;> simp [wordTape]
  · rw [readAt_neg]
    split_ifs <;> simp [wordTape]; omega

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

/-- Draining a tape that holds exactly a nonempty bit word, keeping the bit symbols, recovers
the word. -/
theorem filterMap_window {a : ℕ} (L R : List (Fin (a + 4))) (h : ℤ) (out : List Bool)
    (hne : out ≠ []) (hT : ∀ j, wordTape (out.map bitSymbol) j = readAt blank L R (j - h)) :
    (L.reverse ++ R).filterMap decodeBit = out := by
  rw [window_eq blank L R h _ hT]
  set lo : ℤ := h - L.length
  set len := L.length + R.length
  have hbit : ∀ j : ℕ, j < out.length → wordTape (out.map bitSymbol) j ≠ (blank : Fin (a + 4)) := by
    intro j hj
    simp only [wordTape, Nat.cast_nonneg, ite_true, Int.toNat_natCast, List.getElem?_map,
      List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]
    cases out[j] <;> simp [bitSymbol, blank]
  have hlen : 0 < out.length := List.length_pos_iff.2 hne
  have hlo : lo ≤ 0 := by
    by_contra hc
    apply hbit 0 hlen
    rw [hT, show ((0 : ℕ) : ℤ) - h = -((h - 1 - L.length).toNat + L.length + 1 : ℕ) by omega,
      readAt_neg, List.getElem?_eq_none (by omega)]
    rfl
  have hlo' : lo = h - L.length := rfl
  have hlen' : len = L.length + R.length := rfl
  have hhi : (out.length : ℤ) ≤ lo + len := by
    by_contra hc
    apply hbit (out.length - 1) (by omega)
    rw [hT, show (((out.length - 1 : ℕ)) : ℤ) - h = ((((out.length - 1 : ℕ) : ℤ) - h).toNat : ℕ) by
        omega, readAt_nonneg, List.getElem?_eq_none (by omega)]
    rfl
  have hsplit : (List.range len).map (fun i : ℕ => wordTape (a := a) (out.map bitSymbol) (lo + (i : ℤ))) =
      List.replicate (-lo).toNat blank ++ out.map bitSymbol ++
        List.replicate (len - (-lo).toNat - out.length) blank := by
    apply List.ext_getElem (by simp; omega)
    intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_range]
    by_cases hi : i < (-lo).toNat
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
        List.getElem_replicate]
      simp only [wordTape]
      rw [ite_eq_right (by omega)]
    · by_cases hi' : i < (-lo).toNat + out.length
      · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
        simp only [wordTape, List.length_replicate]
        rw [ite_eq_left (by omega), show (lo + i).toNat = i - (-lo).toNat by omega,
          List.getElem?_eq_getElem (by simp; omega)]
        rfl
      · rw [List.getElem_append_right (by simp; omega), List.getElem_replicate]
        simp only [wordTape]
        split_ifs with h0
        · rw [List.getElem?_eq_none (by simp; omega)]
          rfl
        · rfl
  rw [hsplit]
  simp [List.filterMap_append, List.filterMap_map]

end IntegerMultBounds.MathlibTM2
