module

public import IntegerMultBounds.MathlibTM2.Routing.CompactDescriptorBank

/-! Exact per-table contents and unchanged auxiliary tapes of a compiled bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

noncomputable section

variable {T N J A : ℕ}

theorem compactDescriptorBankGenerated_at (R : Fin T → List (Fin (A + 4)))
    (jobs : List (CompactDescriptorJob T)) (hn : (jobs.map CompactDescriptorJob.dst).Nodup)
    (job : CompactDescriptorJob T) (hj : job ∈ jobs) :
    compactDescriptorBankGenerated R jobs job.dst = job.word ++ R job.dst := by
  induction jobs generalizing R with
  | nil => simp at hj
  | cons head jobs ih =>
    have hnd := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hj with rfl | hj
    · rw [compactDescriptorBankGenerated, compactDescriptorBankGenerated_keep]
      · simp
      · intro other ho he
        exact hnd.1 (List.mem_map.mpr ⟨other, ho, he.symm⟩)
    · rw [compactDescriptorBankGenerated, ih _ hnd.2 hj]
      have hne : job.dst ≠ head.dst := by
        intro he
        exact hnd.1 (List.mem_map.mpr ⟨job, hj, he⟩)
      rw [Function.update_of_ne hne]

theorem compactBankContents (dst : Fin J → Fin N) (hdst : Function.Injective dst)
    (Lw Lg L W : Fin J → ℕ) (qs : (j : Fin J) → List (Fin (W j + 1)))
    (R : Fin (compactDescriptorT N J) → List (Fin (A + 4))) (j : Fin J) :
    compactDescriptorBankGenerated R (List.ofFn (compactBankJob dst Lw Lg L W qs)) (compactDescriptorCore (dst j)) =
      (sourceTable (qs j)).flatten.map bitSymbol ++ R (compactDescriptorCore (dst j)) := by
  have hn : ((List.ofFn (compactBankJob dst Lw Lg L W qs)).map CompactDescriptorJob.dst).Nodup := by
    rw [List.map_ofFn]
    apply List.nodup_ofFn.mpr
    exact compactDescriptorCore_injective.comp hdst
  exact compactDescriptorBankGenerated_at R _ hn (compactBankJob dst Lw Lg L W qs j) (List.mem_ofFn.mpr ⟨j, rfl⟩)

theorem compactBankAux_keep (dst : Fin J → Fin N) (Lw Lg L W : Fin J → ℕ)
    (qs : (j : Fin J) → List (Fin (W j + 1)))
    (R : Fin (compactDescriptorT N J) → List (Fin (A + 4))) (i : CompactDescriptorRole J) :
    compactDescriptorBankGenerated R (List.ofFn (compactBankJob dst Lw Lg L W qs)) (compactDescriptorAux i) = R (compactDescriptorAux i) := by
  apply compactDescriptorBankGenerated_keep
  intro job hj
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hj
  exact (compactDescriptorCore_aux (dst j) i).symm

end
end IntegerMultBounds.MathlibTM2.Routing
