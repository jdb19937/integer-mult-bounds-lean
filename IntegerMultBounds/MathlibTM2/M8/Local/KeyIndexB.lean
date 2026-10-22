module

public import IntegerMultBounds.MathlibTM2.M8.Local.KeyedOrderB

/-! Linear certificate checks for independently supplied key-position inverses. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local

/-- Each list entry returns its position through an independent inverse table. -/
def indexCheck {α : Type*} (index : α → Nat) : Nat → List α → Bool
  | _, [] => true
  | n, x :: xs => Nat.beq (index x) n && indexCheck index (n + 1) xs

theorem indexCheck_append {α : Type*} (index : α → Nat) (n : Nat) (xs ys : List α) :
    indexCheck index n (xs ++ ys) =
      (indexCheck index n xs && indexCheck index (n + xs.length) ys) := by
  induction xs generalizing n with
  | nil => simp [indexCheck]
  | cons x xs ih => simp [indexCheck, ih, Bool.and_assoc, Nat.add_comm, Nat.add_left_comm]

theorem indexCheck_get {α : Type*} (index : α → Nat) (n : Nat) (xs : List α)
    (h : indexCheck index n xs = true) (i : Nat) (hi : i < xs.length) :
    index xs[i] = n + i := by
  induction xs generalizing n i with
  | nil => simp at hi
  | cons x xs ih =>
    simp only [indexCheck, Bool.and_eq_true, Nat.beq_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have hi' : i < xs.length := by simpa using hi
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (n + 1) h.2 i hi'

theorem nodup_of_indexCheck {α : Type*} (index : α → Nat) (xs : List α)
    (h : indexCheck index 0 xs = true) : xs.Nodup :=
  nodup_of_index_inverse xs index fun i hi => by simpa using indexCheck_get index 0 xs h i hi

end IntegerMultBounds.MathlibTM2.M8.Local
