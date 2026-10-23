module

public import IntegerMultBounds.MathlibTM2.Routing.SparseCoordinateTerminal

/-! Terminal-completed mirrored sparse coordinates expand to the exact reversed
pattern-index list, including inactive entries and all terminal zeros. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

variable {W m N : ℕ}

theorem sparseCoordinateClose_mem (N : ℕ) (entries : List (ℕ × Fin (W + 1)))
    (e : ℕ × Fin (W + 1)) (he : e ∈ entries) : e ∈ sparseCoordinateClose N entries := by
  unfold sparseCoordinateClose
  split_ifs <;> simp [he]

theorem sparseCoordinateClose_lookup (N : ℕ) (hN : 0 < N)
    (entries : List (ℕ × Fin (W + 1))) (qs : List (Fin (W + 1))) (hlen : qs.length = N)
    (htarget : ∀ x q, (x, q) ∈ entries → qs[x]? = some q)
    (hgap : ∀ x, x < N → (∀ q, (x, q) ∉ entries) → qs[x]? = some 0) :
    (∀ x q, (x, q) ∈ sparseCoordinateClose N entries → qs[x]? = some q) ∧
    (∀ x, x < N → (∀ q, (x, q) ∉ sparseCoordinateClose N entries) → qs[x]? = some 0) := by
  constructor
  · intro x q hm
    unfold sparseCoordinateClose at hm
    split_ifs at hm with ht
    · exact htarget x q hm
    · rcases List.mem_append.mp hm with hm | hm
      · exact htarget x q hm
      · simp only [List.mem_singleton, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        exact hgap (N - 1) (by omega) (by simpa only [not_exists] using ht)
  · intro x hx hoff
    apply hgap x hx
    intro q hq
    exact hoff q (sparseCoordinateClose_mem N entries (x, q) hq)

theorem sparsePatternComplete_indices (L : ℕ) (hN : 0 < N) (hfit : N < 2 ^ L)
    (pos : ℕ → ℕ) (hpos : StrictMono pos) (src : Fin m → Option (Fin W))
    (hbound : ∀ j < m, pos j < N) :
    SparseSelectorRun.expand (sparseCoordinateRuns 0
      (sparseCoordinateClose N (sparsePatternCoordinates (N := N) pos src))) =
      (List.ofFn (patternIndex (sparsePattern (L := N) pos src))).reverse := by
  let entries := sparsePatternCoordinates (N := N) pos src
  have ho := sparsePatternCoordinates_ordered pos hpos src hbound
  have hb := sparsePatternCoordinates_bound pos src hbound
  have hr := sparseCoordinateClose_ready L N hN hfit entries ho hb
  have he := sparseCoordinateClose_end L N hN hfit entries ho hb
  have hl : (List.ofFn (patternIndex (sparsePattern (L := N) pos src))).reverse.length = N := by simp
  obtain ⟨ht, hg⟩ := sparseCoordinateClose_lookup N hN entries
    (List.ofFn (patternIndex (sparsePattern (L := N) pos src))).reverse hl
    (sparsePatternCoordinates_target pos hpos src hbound) (sparsePatternCoordinates_gap pos src hbound)
  apply sparseCoordinateRuns_eq L _ hr _
  · simpa using he
  · exact ht
  · intro x hx hoff; exact hg x (by simpa using hx) hoff

end IntegerMultBounds.MathlibTM2.Routing
