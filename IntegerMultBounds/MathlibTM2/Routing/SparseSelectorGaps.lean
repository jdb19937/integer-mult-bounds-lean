module

public import IntegerMultBounds.MathlibTM2.Routing.SparseSelectorCompress

/-! Convert a whole zero interval into one compact gap update. This avoids
constructing its dense zero list when specifying sparse coordinate generation.
The final zero entry handles a trailing interval exactly. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.SparseSelectorRun

variable {W : ℕ}

def addGaps (n : ℕ) (runs : List (SparseSelectorRun W)) : List (SparseSelectorRun W) :=
  match n, runs with
  | 0, _ => runs
  | n + 1, [] => [⟨n, 0⟩]
  | n + 1, run :: rest => { run with gap := run.gap + (n + 1) } :: rest

theorem addGaps_succ (n : ℕ) (runs : List (SparseSelectorRun W)) :
    addGaps (n + 1) runs = addGap (addGaps n runs) := by
  cases n <;> cases runs with
  | nil => rfl
  | cons run rest =>
    simp [addGaps, addGap, Nat.add_assoc]

theorem compress_zero_prefix (n : ℕ) (qs : List (Fin (W + 1))) :
    compress (List.replicate n 0 ++ qs) = addGaps n (compress qs) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, compress, ↓reduceIte, ih, addGaps_succ]

theorem expand_addGaps (n : ℕ) (runs : List (SparseSelectorRun W)) :
    expand (addGaps n runs) = List.replicate n 0 ++ expand runs := by
  induction n with
  | zero => rfl
  | succ n ih => simp [addGaps_succ, expand_addGap, ih, List.replicate_succ]

theorem compress_live_run (gap : ℕ) (q : Fin (W + 1)) (hq : q ≠ 0)
    (qs : List (Fin (W + 1))) :
    compress (List.replicate gap 0 ++ q :: qs) = ⟨gap, q⟩ :: compress qs := by
  rw [compress_zero_prefix]
  simp only [compress, ite_eq_right hq]
  cases gap with
  | zero => rfl
  | succ gap => simp [addGaps]

theorem compress_trailing_zeros (n : ℕ) :
    compress (List.replicate (n + 1) (0 : Fin (W + 1))) = [⟨n, 0⟩] := by
  have h := compress_zero_prefix (W := W) (n + 1) []
  simpa only [List.append_nil, compress, addGaps] using h

end IntegerMultBounds.MathlibTM2.Routing.SparseSelectorRun
