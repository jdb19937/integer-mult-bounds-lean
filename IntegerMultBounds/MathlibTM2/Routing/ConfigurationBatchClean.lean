module

public import IntegerMultBounds.MathlibTM2.Routing.ConfigurationBatchSpec
public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-!
# Clearing a loaded configuration bank restores its reusable register frame

Only the raw source cursor and its rewind archive differ from the input bank.
Thus a real routing call can run between loading and clearing without allocating
fresh tapes for the next configuration.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

theorem configurationBatchClean_restore {T A : ℕ}
    (R : Fin T → List (Fin (A + 4))) (src tmp saved : Fin T)
    (hst : src ≠ tmp) (hss : src ≠ saved) (hts : tmp ≠ saved)
    (slots : List (ConfigurationSlot T)) (words : List (List (Fin (A + 4))))
    (hlen : words.length = slots.length)
    (hslots : ∀ slot ∈ slots, src ≠ slot.dst ∧ tmp ≠ slot.dst ∧ saved ≠ slot.dst)
    (rest : List (Fin (A + 4))) (hsrc : R src = configurationWords words ++ rest)
    (htmp : R tmp = []) (hempty : ∀ slot ∈ slots, R slot.dst = []) :
    metadataCleared (configurationBatchLoaded R src tmp saved slots words rest)
        (slots.map ConfigurationSlot.dst) =
      Function.update (Function.update R src rest) saved ((configurationWords words).reverse ++ R saved) := by
  funext j
  by_cases hj : j ∈ slots.map ConfigurationSlot.dst
  · rw [metadataCleared_at _ _ j hj]
    obtain ⟨slot, hs, rfl⟩ := List.mem_map.mp hj
    obtain ⟨hsd, htd, had⟩ := hslots slot hs
    simp only [Function.update_of_ne had.symm, Function.update_of_ne hsd.symm, hempty slot hs]
  · rw [metadataCleared_keep _ _ j hj]
    by_cases hjs : j = src
    · subst j
      rw [configurationBatchLoaded_src R src tmp saved hst hss slots words hlen
        (fun slot hs => (hslots slot hs).1) rest hsrc]
      simp [Function.update_of_ne hss]
    · by_cases hja : j = saved
      · subst j
        rw [configurationBatchLoaded_saved R src tmp saved slots words hlen
          (fun slot hs => (hslots slot hs).2.2) rest]
        simp
      · by_cases hjt : j = tmp
        · subst j
          rw [configurationBatchLoaded_tmp R src tmp saved hts slots words hlen
            (fun slot hs => (hslots slot hs).2.1) rest htmp]
          simp [Function.update_of_ne hja, Function.update_of_ne hjs, htmp]
        · rw [configurationBatchLoaded_keep R src tmp saved slots words rest j hjs hjt hja hj]
          simp [Function.update_of_ne hja, Function.update_of_ne hjs]

end IntegerMultBounds.MathlibTM2.Routing
