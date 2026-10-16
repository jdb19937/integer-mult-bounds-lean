module

public import IntegerMultBounds.MathlibTM2.Mult.BandSolveFold

/-! Folding a line into the elimination order and back, as list operations a tape
machine performs. Folding interleaves the first half with the reversed second half;
unfolding takes the even positions followed by the reversed odd positions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.BandFactor

open IntegerMultBounds.NLogN.PhaseCellMatrix

/-- Interleave two lists, starting with the first. -/
def interleave {α : Type*} : List α → List α → List α
  | a :: as, b :: bs => a :: b :: interleave as bs
  | as, [] => as
  | [], bs => bs

/-- The folded line: the first `⌈s/2⌉` entries interleaved with the reversed rest. -/
def foldList {α : Type*} (v : List α) : List α :=
  interleave (v.take ((v.length + 1) / 2)) (v.drop ((v.length + 1) / 2)).reverse

/-- The entries at even positions. -/
def evens {α : Type*} : List α → List α
  | a :: _ :: rest => a :: evens rest
  | l => l

/-- The entries at odd positions. -/
def odds {α : Type*} : List α → List α
  | _ :: b :: rest => b :: odds rest
  | _ => []

/-- The unfolded line: even positions, then the odd positions reversed. -/
def unfoldList {α : Type*} (x : List α) : List α := evens x ++ (odds x).reverse

theorem length_interleave {α : Type*} : ∀ (a b : List α), b.length ≤ a.length →
    a.length ≤ b.length + 1 → (interleave a b).length = a.length + b.length
  | _ :: as, _ :: bs, h1, h2 => by
    simp only [interleave, List.length_cons] at *
    rw [length_interleave as bs (by omega) (by omega)]; omega
  | as, [], _, _ => by cases as <;> simp [interleave]
  | [], _ :: _, h, _ => by simp at h

theorem getD_interleave {α : Type*} (d : α) : ∀ (a b : List α), b.length ≤ a.length →
    a.length ≤ b.length + 1 → ∀ i,
    (interleave a b).getD i d = if i % 2 = 0 then a.getD (i / 2) d else b.getD (i / 2) d
  | x :: as, y :: bs, h1, h2, i => by
    simp only [List.length_cons] at h1 h2
    rcases i with _ | _ | i
    · simp [interleave]
    · simp [interleave]
    · simp only [interleave, List.getD_cons_succ]
      rw [getD_interleave d as bs (by omega) (by omega) i]
      have e : (i + 2) / 2 = i / 2 + 1 := by omega
      have e2 : (i + 2) % 2 = i % 2 := by omega
      rw [e, e2]
      split_ifs <;> simp
  | as, [], h1, h2, i => by
    cases as with
    | nil => simp [interleave]
    | cons x as =>
      simp at h2
      subst h2
      rcases i with _ | _ | i <;> simp [interleave] <;> split_ifs <;> simp <;> omega
  | [], _ :: _, h, _, _ => by simp at h

/-- The index of the folded position `i` in the natural order. -/
def foldAtN (s i : ℕ) : ℕ := if i % 2 = 0 then i / 2 else s - 1 - i / 2

theorem getD_foldList {α : Type*} (d : α) (v : List α) (i : ℕ) (hi : i < v.length) :
    (foldList v).getD i d = v.getD (foldAtN v.length i) d := by
  set s := v.length
  set h := (s + 1) / 2
  unfold foldList
  rw [getD_interleave d _ _ (by simp; omega) (by simp; omega), foldAtN]
  split_ifs with he
  · simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_take_of_lt (by omega)]
  · simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_reverse (by simp; omega), List.getElem?_drop]
    congr 2
    simp; omega

theorem foldAt_val_eq (s : ℕ) [NeZero s] (i : ℕ) (hi : i < s) :
    (foldAt s i).val = foldAtN s i := by
  unfold foldAt foldAtN
  split
  · rw [ZMod.val_cast_of_lt (by omega)]
  · rw [ZMod.val_cast_of_lt (by omega)]

theorem length_evens {α : Type*} : ∀ x : List α, (evens x).length = (x.length + 1) / 2
  | [] => by simp [evens]
  | [_] => by simp [evens]
  | a :: b :: rest => by simp only [evens, List.length_cons, length_evens rest]; omega

theorem length_odds {α : Type*} : ∀ x : List α, (odds x).length = x.length / 2
  | [] => by simp [odds]
  | [_] => by simp [odds]
  | a :: b :: rest => by simp only [odds, List.length_cons, length_odds rest]; omega

theorem getD_evens {α : Type*} (d : α) : ∀ (x : List α) (k : ℕ),
    (evens x).getD k d = x.getD (2 * k) d
  | [], k => by simp [evens]
  | [a], k => by rcases k with _ | k <;> simp [evens]
  | a :: b :: rest, 0 => by simp [evens]
  | a :: b :: rest, k + 1 => by
    simp only [evens, List.getD_cons_succ, getD_evens d rest k]
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, List.getD_cons_succ, List.getD_cons_succ]

theorem getD_odds {α : Type*} (d : α) : ∀ (x : List α) (k : ℕ), 2 * k + 1 < x.length →
    (odds x).getD k d = x.getD (2 * k + 1) d
  | [], k, h => by simp at h
  | [a], k, h => by simp at h
  | a :: b :: rest, 0, _ => by simp [odds]
  | a :: b :: rest, k + 1, h => by
    simp only [odds, List.getD_cons_succ]
    rw [getD_odds d rest k (by simp at h; omega), show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
    simp

/-- The folded position of the natural index `ℓ`. -/
def foldPosN (s ℓ : ℕ) : ℕ := if 2 * ℓ < s then 2 * ℓ else 2 * (s - 1 - ℓ) + 1

theorem getD_unfoldList {α : Type*} (d : α) (x : List α) (ℓ : ℕ) (hℓ : ℓ < x.length) :
    (unfoldList x).getD ℓ d = x.getD (foldPosN x.length ℓ) d := by
  set s := x.length
  unfold unfoldList foldPosN
  have he := length_evens x
  have ho := length_odds x
  split_ifs with h2
  · rw [List.getD_append _ _ _ _ (by rw [he]; omega), getD_evens]
  · rw [List.getD_append_right _ _ _ _ (by rw [he]; omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_reverse (by rw [ho, he]; omega)]
    rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD,
      getD_odds d x _ (by rw [ho, he]; omega)]
    congr 1
    rw [ho, he]; omega

end IntegerMultBounds.MathlibTM2.Mult.BandFactor
