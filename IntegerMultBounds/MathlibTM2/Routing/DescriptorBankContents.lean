module

public import IntegerMultBounds.MathlibTM2.Routing.DescriptorBank

/-! Exact per-table contents and unchanged auxiliary tapes of a compiled bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

variable {T N J A : ℕ}

theorem descriptorBankGenerated_at (R : Fin T → List (Fin (A + 4)))
    (jobs : List (DescriptorJob T)) (hn : (jobs.map DescriptorJob.dst).Nodup)
    (job : DescriptorJob T) (hj : job ∈ jobs) :
    descriptorBankGenerated R jobs job.dst = job.word ++ R job.dst := by
  induction jobs generalizing R with
  | nil => simp at hj
  | cons head jobs ih =>
    have hnd := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hj with rfl | hj
    · rw [descriptorBankGenerated, descriptorBankGenerated_keep]
      · simp
      · intro other ho he
        exact hnd.1 (List.mem_map.mpr ⟨other, ho, he.symm⟩)
    · rw [descriptorBankGenerated, ih _ hnd.2 hj]
      have hne : job.dst ≠ head.dst := by
        intro he
        exact hnd.1 (List.mem_map.mpr ⟨job, hj, he⟩)
      rw [Function.update_of_ne hne]

theorem descriptorBankContents (dst : Fin J → Fin N) (hdst : Function.Injective dst)
    (L W : Fin J → ℕ) (qs : (j : Fin J) → List (Fin (W j)))
    (R : Fin (N + (2 * J + 12)) → List (Fin (A + 4))) (j : Fin J) :
    descriptorBankGenerated R (List.ofFn (descriptorBankJob dst L W qs)) (descriptorCore (dst j)) =
      (sourceTable (qs j)).flatten.map bitSymbol ++ R (descriptorCore (dst j)) := by
  have hn : ((List.ofFn (descriptorBankJob dst L W qs)).map DescriptorJob.dst).Nodup := by
    rw [List.map_ofFn]
    apply List.nodup_ofFn.mpr
    exact descriptorCore_injective.comp hdst
  exact descriptorBankGenerated_at R _ hn (descriptorBankJob dst L W qs j) (List.mem_ofFn.mpr ⟨j, rfl⟩)

theorem descriptorBankAux_keep (dst : Fin J → Fin N) (L W : Fin J → ℕ)
    (qs : (j : Fin J) → List (Fin (W j)))
    (R : Fin (N + (2 * J + 12)) → List (Fin (A + 4))) (i : Fin (2 * J + 12)) :
    descriptorBankGenerated R (List.ofFn (descriptorBankJob dst L W qs)) (descriptorAux i) = R (descriptorAux i) := by
  apply descriptorBankGenerated_keep
  intro job hj
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hj
  exact (descriptorCore_aux (dst j) i).symm

end IntegerMultBounds.MathlibTM2.Routing
