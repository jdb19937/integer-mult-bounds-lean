module

public import IntegerMultBounds.MathlibTM2.Routing.MetadataInstall

/-! Structural size bounds for installed metadata in an injective tape bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

theorem bankLength_update_le {N T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (bank : Fin N → Fin T) (hbank : Function.Injective bank) (k : Fin N)
    (word : List (Fin (A + 4))) :
    (∑ j, (Function.update R (bank k) word (bank j)).length) ≤
      (∑ j, (R (bank j)).length) + word.length := by
  calc
    _ ≤ ∑ j, ((R (bank j)).length + if j = k then word.length else 0) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j = k
      · subst j; simp
      · simp [Function.update_of_ne (fun he => hj (hbank he)), hj]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

/-- Installation adds at most the total generated-word length, regardless of
the original contents of the borrowed bank. No concrete bank is expanded. -/
theorem metadataInstalled_bankLength_le {N T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (bank : Fin N → Fin T) (hbank : Function.Injective bank) (jobs : List (MetadataJob T))
    (hdst : ∀ job ∈ jobs, ∃ k, job.dst = bank k) :
    (∑ j, (metadataInstalled R jobs (bank j)).length) ≤
      (∑ j, (R (bank j)).length) + (jobs.map (fun job => (job.contents R).length)).sum := by
  induction jobs with
  | nil => simp [metadataInstalled]
  | cons job jobs ih =>
    obtain ⟨k, hk⟩ := hdst job (by simp)
    have h := bankLength_update_le (metadataInstalled R jobs) bank hbank k (job.contents R)
    rw [← hk] at h
    have ht := ih (fun j hj => hdst j (by simp [hj]))
    simp only [metadataInstalled, List.map_cons, List.sum_cons]
    omega

end IntegerMultBounds.MathlibTM2.Routing
