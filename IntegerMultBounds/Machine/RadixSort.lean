module

public import Mathlib.Data.List.Sort
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Executable stable least-significant-bit radix sorting of arbitrary records.
Each pass is exactly the false filter followed by the true filter. The theorems
here describe lists and the record volume traversed by the passes; they do not
claim a tape implementation or charge list operations as machine steps. -/

@[expose] public section

namespace IntegerMultBounds.Machine.RadixSort

variable {α : Type*}

/-- A stable binary partition, with the false bucket first. -/
def pass (bit : α → Bool) (xs : List α) : List α :=
  xs.filter (fun x => !(bit x)) ++ xs.filter bit

/-- Process bit zero first; bit `k` is the next more significant bit. -/
def sort (bit : α → ℕ → Bool) : ℕ → List α → List α
  | 0, xs => xs
  | k + 1, xs => pass (fun x => bit x k) (sort bit k xs)

/-- The natural-number value of the low `k` bits of a record's key. -/
def keyValue (bit : α → ℕ → Bool) : ℕ → α → ℕ
  | 0, _ => 0
  | k + 1, x => keyValue bit k x + if bit x k then 2 ^ k else 0

theorem pass_perm (bit : α → Bool) (xs : List α) : (pass bit xs).Perm xs := by
  simpa [pass] using List.filter_append_perm (fun x => !(bit x)) xs

theorem sort_perm (bit : α → ℕ → Bool) (k : ℕ) (xs : List α) :
    (sort bit k xs).Perm xs := by
  induction k with
  | zero => exact List.Perm.refl _
  | succ k ih => exact (pass_perm _ _).trans ih

@[simp] theorem pass_length (bit : α → Bool) (xs : List α) :
    (pass bit xs).length = xs.length := (pass_perm bit xs).length_eq

@[simp] theorem sort_length (bit : α → ℕ → Bool) (k : ℕ) (xs : List α) :
    (sort bit k xs).length = xs.length := (sort_perm bit k xs).length_eq

theorem keyValue_lt (bit : α → ℕ → Bool) (k : ℕ) (x : α) :
    keyValue bit k x < 2 ^ k := by
  induction k with
  | zero => simp [keyValue]
  | succ k ih =>
    simp only [keyValue, pow_succ]
    cases bit x k <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- One stable partition extends sortedness from the low `k` bits to `k + 1`. -/
theorem pass_pairwise (bit : α → ℕ → Bool) (k : ℕ) (xs : List α)
    (hs : xs.Pairwise (fun x y => keyValue bit k x ≤ keyValue bit k y)) :
    (pass (fun x => bit x k) xs).Pairwise
      (fun x y => keyValue bit (k + 1) x ≤ keyValue bit (k + 1) y) := by
  apply List.pairwise_append.mpr
  refine ⟨?_, ?_, ?_⟩
  · apply (hs.filter (fun x => !(bit x k))).imp_of_mem
    intro x y hx hy hxy
    have hx' : bit x k = false := by simpa using (List.mem_filter.mp hx).2
    have hy' : bit y k = false := by simpa using (List.mem_filter.mp hy).2
    simpa [keyValue, hx', hy'] using hxy
  · apply (hs.filter (fun x => bit x k)).imp_of_mem
    intro x y hx hy hxy
    have hx' := (List.mem_filter.mp hx).2
    have hy' := (List.mem_filter.mp hy).2
    simpa [keyValue, hx', hy'] using Nat.add_le_add_right hxy (2 ^ k)
  · intro x hx y hy
    have hx' : bit x k = false := by simpa using (List.mem_filter.mp hx).2
    have hy' := (List.mem_filter.mp hy).2
    have hbound := keyValue_lt bit k x
    simp only [keyValue, hx', Bool.false_eq_true, ↓reduceIte, Nat.add_zero, hy']
    omega

/-- After `k` passes the records are sorted by all `k` key bits. -/
theorem sort_pairwise (bit : α → ℕ → Bool) (k : ℕ) (xs : List α) :
    (sort bit k xs).Pairwise (fun x y => keyValue bit k x ≤ keyValue bit k y) := by
  induction k with
  | zero =>
    induction xs with
    | nil => exact .nil
    | cons x xs ih => exact .cons (by simp [keyValue]) ih
  | succ k ih => exact pass_pairwise bit k _ ih

/-- Total encoded record volume, allowing variable-sized payloads. -/
def volume (weight : α → ℕ) (xs : List α) : ℕ := (xs.map weight).sum

@[simp] theorem pass_volume (bit : α → Bool) (weight : α → ℕ) (xs : List α) :
    volume weight (pass bit xs) = volume weight xs :=
  ((pass_perm bit xs).map weight).sum_eq

@[simp] theorem sort_volume (bit : α → ℕ → Bool) (weight : α → ℕ)
    (k : ℕ) (xs : List α) : volume weight (sort bit k xs) = volume weight xs :=
  ((sort_perm bit k xs).map weight).sum_eq

/-- A uniform upper bound on encoded record sizes gives the usual volume bound. -/
theorem volume_le (weight : α → ℕ) (xs : List α) (width : ℕ)
    (h : ∀ x ∈ xs, weight x ≤ width) : volume weight xs ≤ xs.length * width := by
  induction xs with
  | nil => simp [volume]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [volume, List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul] at *
    omega

end IntegerMultBounds.Machine.RadixSort
