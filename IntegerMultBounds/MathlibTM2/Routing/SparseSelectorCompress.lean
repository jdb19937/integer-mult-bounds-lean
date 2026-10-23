module

public import IntegerMultBounds.MathlibTM2.Routing.SparseSelectorRuns

/-! Canonical compact runs for any dense selector list. A final zero selector
closes trailing gaps, including all-zero tables; no extra physical read is used.
This is specification algebra, not an executed coordinate generator. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.SparseSelectorRun

variable {W : ℕ}

def addGap : List (SparseSelectorRun W) → List (SparseSelectorRun W)
  | [] => [⟨0, 0⟩]
  | run :: runs => { run with gap := run.gap + 1 } :: runs

def compress : List (Fin (W + 1)) → List (SparseSelectorRun W)
  | [] => []
  | q :: qs => if q = 0 then addGap (compress qs) else ⟨0, q⟩ :: compress qs

theorem expand_addGap (runs : List (SparseSelectorRun W)) :
    expand (addGap runs) = 0 :: expand runs := by
  cases runs with
  | nil => rfl
  | cons run runs => simp [addGap, expand, indices, List.replicate_succ]

theorem expand_compress (qs : List (Fin (W + 1))) : expand (compress qs) = qs := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    by_cases hq : q = 0
    · subst q; simp [compress, expand_addGap, ih]
    · simp [compress, hq, expand, indices, ih]

theorem compress_nonempty (qs : List (Fin (W + 1))) : compress qs = [] ↔ qs = [] := by
  constructor
  · intro hc
    have he := expand_compress qs
    rw [hc] at he
    exact he.symm
  · rintro rfl; rfl

/-- At most one final zero entry is needed beyond the actual nonzero reads. -/
theorem compress_length_le (qs : List (Fin (W + 1))) :
    (compress qs).length ≤ (qs.filter (fun q => q ≠ 0)).length + 1 := by
  induction qs with
  | nil => simp [compress]
  | cons q qs ih =>
    by_cases hq : q = 0
    · subst q
      simp only [compress, ↓reduceIte, List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true]
      cases hc : compress qs with
      | nil => simp [addGap]
      | cons run runs =>
        simp only [hc, addGap, List.length_cons] at ih ⊢
        exact ih
    · simp [compress, hq] at ih ⊢
      omega

theorem compress_gap_lt_length (qs : List (Fin (W + 1))) :
    ∀ run ∈ compress qs, run.gap < qs.length := by
  induction qs with
  | nil => simp [compress]
  | cons q qs ih =>
    intro run hr
    by_cases hq : q = 0
    · simp only [compress, ite_eq_left hq] at hr
      cases hc : compress qs with
      | nil =>
        simp only [hc, addGap, List.mem_singleton] at hr
        subst run; simp
      | cons head rest =>
        simp only [hc, addGap, List.mem_cons] at hr
        rcases hr with rfl | hr
        · have hh := ih head (by rw [hc]; simp)
          simp only [List.length_cons]; omega
        · have hh := ih run (by rw [hc]; simp [hr])
          simp only [List.length_cons]; omega
    · simp only [compress, ite_eq_right hq, List.mem_cons] at hr
      rcases hr with rfl | hr
      · simp
      · have hh := ih run hr
        simp only [List.length_cons]; omega

end IntegerMultBounds.MathlibTM2.Routing.SparseSelectorRun
