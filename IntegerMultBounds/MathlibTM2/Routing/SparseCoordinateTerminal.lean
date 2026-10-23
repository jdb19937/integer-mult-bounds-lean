module

public import IntegerMultBounds.MathlibTM2.Routing.SparsePatternReadiness

/-! Complete an ordered coordinate list at the final output position. A zero
entry is appended only when that position is absent, avoiding duplicate targets. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

variable {W : ℕ}

def sparseCoordinateClose (N : ℕ) (entries : List (ℕ × Fin (W + 1))) : List (ℕ × Fin (W + 1)) :=
  if ∃ q, (N - 1, q) ∈ entries then entries else entries ++ [(N - 1, 0)]

theorem sparseCoordinateClose_ordered (N : ℕ) (entries : List (ℕ × Fin (W + 1)))
    (horder : entries.Pairwise (fun a b => a.1 < b.1)) (hbound : ∀ e ∈ entries, e.1 < N) :
    (sparseCoordinateClose N entries).Pairwise (fun a b => a.1 < b.1) := by
  unfold sparseCoordinateClose
  split_ifs with ht
  · exact horder
  · rw [List.pairwise_append]
    refine ⟨horder, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    have hh := hbound a ha
    have hn : a.1 ≠ N - 1 := by
      intro he
      apply ht
      exact ⟨a.2, by simpa only [← he, Prod.mk.eta] using ha⟩
    simp only
    omega

theorem sparseCoordinateClose_bound (N : ℕ) (hN : 0 < N)
    (entries : List (ℕ × Fin (W + 1))) (hbound : ∀ e ∈ entries, e.1 < N) :
    ∀ e ∈ sparseCoordinateClose N entries, e.1 < N := by
  intro e he
  unfold sparseCoordinateClose at he
  split_ifs at he with ht
  · exact hbound e he
  · rcases List.mem_append.mp he with he | he
    · exact hbound e he
    · simp only [List.mem_singleton] at he
      subst e; simp only; omega

theorem sparseCoordinateClose_terminal (N : ℕ) (entries : List (ℕ × Fin (W + 1))) :
    ∃ q, (N - 1, q) ∈ sparseCoordinateClose N entries := by
  unfold sparseCoordinateClose
  split_ifs with ht
  · exact ht
  · exact ⟨0, by simp⟩

theorem sparseCoordinateClose_ready (L N : ℕ) (hN : 0 < N) (hfit : N < 2 ^ L)
    (entries : List (ℕ × Fin (W + 1)))
    (horder : entries.Pairwise (fun a b => a.1 < b.1)) (hbound : ∀ e ∈ entries, e.1 < N) :
    SparseCoordinatesReady L 0 (sparseCoordinateValues (sparseCoordinateClose N entries)) := by
  apply sparseCoordinatesReady_of_ordered L 0 _ (sparseCoordinateClose_ordered N entries horder hbound)
  · intro e he
    have hh := sparseCoordinateClose_bound N hN entries hbound e he
    omega
  · intro e he; omega

theorem sparseCoordinateClose_length (N : ℕ) (entries : List (ℕ × Fin (W + 1))) :
    (sparseCoordinateClose N entries).length ≤ entries.length + 1 := by
  unfold sparseCoordinateClose
  split_ifs <;> simp

theorem sparseCoordinateEnd_bound (N cursor : ℕ) (entries : List (ℕ × ℕ))
    (hc : cursor ≤ N) (hb : ∀ e ∈ entries, e.1 < N) : sparseCoordinateEnd cursor entries ≤ N := by
  induction entries generalizing cursor with
  | nil => exact hc
  | cons pair rest ih =>
    obtain ⟨x, q⟩ := pair
    apply ih (x + 1)
    · have hh := hb (x, q) (by simp); omega
    · intro e he; exact hb e (List.mem_cons_of_mem _ he)

theorem sparseCoordinateEnd_gt_member (L cursor : ℕ) (entries : List (ℕ × ℕ))
    (hr : SparseCoordinatesReady L cursor entries) (x q : ℕ) (hm : (x, q) ∈ entries) :
    x < sparseCoordinateEnd cursor entries := by
  induction entries generalizing cursor with
  | nil => simp at hm
  | cons pair rest ih =>
    obtain ⟨y, r⟩ := pair
    obtain ⟨_, _, ht⟩ := hr
    rcases List.mem_cons.mp hm with he | hm
    · cases he
      have hh := sparseCoordinateEnd_ge L (x + 1) rest ht
      change x < sparseCoordinateEnd (x + 1) rest
      omega
    · exact ih (y + 1) ht hm

theorem sparseCoordinateClose_end (L N : ℕ) (hN : 0 < N) (hfit : N < 2 ^ L)
    (entries : List (ℕ × Fin (W + 1)))
    (ho : entries.Pairwise (fun a b => a.1 < b.1)) (hb : ∀ e ∈ entries, e.1 < N) :
    sparseCoordinateEnd 0 (sparseCoordinateValues (sparseCoordinateClose N entries)) = N := by
  have hbound := sparseCoordinateClose_bound N hN entries hb
  have hle := sparseCoordinateEnd_bound N 0 (sparseCoordinateValues (sparseCoordinateClose N entries)) (by omega)
    (by intro e he; obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he; exact hbound a ha)
  obtain ⟨q, hq⟩ := sparseCoordinateClose_terminal N entries
  have hmem : (N - 1, q.val) ∈ sparseCoordinateValues (sparseCoordinateClose N entries) :=
    List.mem_map.mpr ⟨(N - 1, q), hq, rfl⟩
  have hgt := sparseCoordinateEnd_gt_member L 0 _ (sparseCoordinateClose_ready L N hN hfit entries ho hb) _ _ hmem
  omega

end IntegerMultBounds.MathlibTM2.Routing
