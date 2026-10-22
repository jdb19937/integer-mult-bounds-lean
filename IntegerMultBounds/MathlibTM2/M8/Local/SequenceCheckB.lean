module

public import IntegerMultBounds.MathlibTM2.M8.Local.KeyIndexB

/-! Linear comparison with an independently supplied indexed sequence. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local

def sequenceCheck (get : Nat → Nat) : Nat → List Nat → Bool
  | _, [] => true
  | n, x :: xs => Nat.beq (get n) x && sequenceCheck get (n + 1) xs

theorem sequenceCheck_append (get : Nat → Nat) (n : Nat) (xs ys : List Nat) :
    sequenceCheck get n (xs ++ ys) =
      (sequenceCheck get n xs && sequenceCheck get (n + xs.length) ys) := by
  induction xs generalizing n with
  | nil => simp [sequenceCheck]
  | cons x xs ih => simp [sequenceCheck, ih, Bool.and_assoc, Nat.add_comm, Nat.add_left_comm]

theorem sequenceCheck_get (get : Nat → Nat) (n : Nat) (xs : List Nat)
    (h : sequenceCheck get n xs = true) (i : Nat) (hi : i < xs.length) :
    get (n + i) = xs[i] := by
  induction xs generalizing n i with
  | nil => simp at hi
  | cons x xs ih =>
    simp only [sequenceCheck, Bool.and_eq_true, Nat.beq_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have hi' : i < xs.length := by simpa using hi
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (n + 1) h.2 i hi'

/-- Equal length and checked entries identify whole sequences structurally. -/
theorem sequenceCheck_eq (get : Nat → Nat) (xs ys : List Nat) (hlen : xs.length = ys.length)
    (hx : sequenceCheck get 0 xs = true) (hy : sequenceCheck get 0 ys = true) : xs = ys := by
  apply List.ext_getElem hlen
  intro i hi hj
  have hxi := sequenceCheck_get get 0 xs hx i hi
  have hyi := sequenceCheck_get get 0 ys hy i hj
  exact hxi.symm.trans hyi

end IntegerMultBounds.MathlibTM2.M8.Local
