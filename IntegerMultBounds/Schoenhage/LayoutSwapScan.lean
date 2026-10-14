module

public import IntegerMultBounds.Schoenhage.LayoutScript

/-! The chunk exchanges of the §6 layout as a scan of the unsettled suffix. Once
positions `0, …, k - 1` hold their own blocks, the left-to-right scan only reads
and rewrites the suffix: at the head `a` it either moves on (`a = k`) or
exchanges `k` with the position `k + 1 + i` of block `k`, `i` its index in the
rest, which then holds `a` (`selS`, `selectL_range`). An exchange `(k, j)`
with `k < j` has widths `K`, `(j - k - 1) K`, `(m - 1 - j) K` (`exParamsN_lt`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage.LayoutScript

/-- The scan on the unsettled suffix whose head is position `k`. -/
def selS : List ℕ → ℕ → List (ℕ × ℕ)
  | [], _ => []
  | a :: rest, k =>
    if a = k then selS rest (k + 1)
    else (k, k + 1 + rest.idxOf k) :: selS (rest.set (rest.idxOf k) a) (k + 1)
termination_by suffix => suffix.length
decreasing_by all_goals simp

theorem selS_cons_eq (rest : List ℕ) (k : ℕ) : selS (k :: rest) k = selS rest (k + 1) := by
  rw [selS]; simp

theorem selS_cons_ne {a k : ℕ} (rest : List ℕ) (h : a ≠ k) :
    selS (a :: rest) k = (k, k + 1 + rest.idxOf k) :: selS (rest.set (rest.idxOf k) a) (k + 1) := by
  rw [selS]; simp [h]

/-- The scan from a settled prefix `0, …, k - 1`. -/
theorem selectL_range : ∀ (e k : ℕ) (rest : List ℕ), rest.length = e →
    selectL (List.range k ++ rest) k e = selS rest k
  | 0, k, rest, hl => by
    rw [List.length_eq_zero_iff.mp hl, selectL, selS]
  | e + 1, k, [], hl => by simp at hl
  | e + 1, k, a :: rest, hl => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have hget : (List.range k ++ a :: rest).getD k 0 = a := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp
    rw [selectL, hget]
    by_cases hak : a = k
    · subst hak
      rw [if_pos rfl, selS_cons_eq, show List.range a ++ a :: rest = List.range (a + 1) ++ rest by
        simp [List.range_succ]]
      exact selectL_range e (a + 1) rest hl
    · rw [if_neg hak, selS_cons_ne rest hak]
      have hidx : (List.range k ++ a :: rest).idxOf k = k + 1 + rest.idxOf k := by
        rw [List.idxOf_append_of_notMem (by simp), List.idxOf_cons_ne _ hak]
        simp; omega
      rw [hidx]
      congr 1
      have hset : ((List.range k ++ a :: rest).set k k).set (k + 1 + rest.idxOf k) a =
          List.range (k + 1) ++ rest.set (rest.idxOf k) a := by
        rw [List.set_append_right _ _ (by simp), List.length_range, Nat.sub_self, List.set_cons_zero,
          show List.range k ++ k :: rest = List.range k ++ [k] ++ rest by simp,
          List.set_append_right _ _ (by simp)]
        simp [List.range_succ]
      rw [hset]
      exact selectL_range e (k + 1) _ (by simp [hl])

/-- An exchange of positions `k < j` among `m` blocks of `K` slots. -/
theorem exParamsN_lt {m K k j : ℕ} (h : k < j) :
    exParamsN m K (k, j) = (K, (j - k - 1) * K, (m - 1 - j) * K) := by
  simp [exParamsN, h.ne, max_eq_right h.le, min_eq_left h.le]

/-- Every pair of the suffix scan has its first position below its second. -/
theorem selS_lt : ∀ (S : List ℕ) (k : ℕ), ∀ q ∈ selS S k, q.1 < q.2
  | [], _, q, hq => by simp [selS] at hq
  | a :: rest, k, q, hq => by
    by_cases hak : a = k
    · subst hak; rw [selS_cons_eq] at hq; exact selS_lt rest _ q hq
    · rw [selS_cons_ne rest hak, List.mem_cons] at hq
      rcases hq with rfl | hq
      · simp; omega
      · exact selS_lt _ _ q hq
termination_by S => S.length
decreasing_by all_goals simp

/-- The axis-major arrangement of `D` axes of `q` chunks. -/
def axisArr (q D : ℕ) : List ℕ := (List.range (q * D)).map fun x => x % q * D + x / q

/-- `layoutSwaps_selS`: the paper's chunk exchanges are the suffix scan of the axis-major arrangement. -/
theorem layoutSwaps_selS {ts : List ℕ} {ℓ K : ℕ} :
    LayoutMachines.layoutSwaps ts ℓ K =
      (selS (axisArr ((ℓ - 1) / K) ts.length) 0).map (exParamsN ((ℓ - 1) / K * ts.length) K) := by
  have h := selectL_range ((ℓ - 1) / K * ts.length) 0 (axisArr ((ℓ - 1) / K) ts.length) (by simp [axisArr])
  simp only [List.range_zero, List.nil_append] at h
  rw [layoutSwaps_eq, ← h]
  rfl

end IntegerMultBounds.Schoenhage.LayoutScript
