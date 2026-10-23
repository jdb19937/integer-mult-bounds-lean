module

public import IntegerMultBounds.MathlibTM2.Routing.CompactDescriptorContents
public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-! Erase a compiled descriptor bank after an arbitrary change to a disjoint
stream. Initial blank descriptor destinations and every other tape are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def compactDescriptorEraseCost : List (CompactDescriptorJob T) → ℕ
  | [] => 1
  | job :: jobs => compactDescriptorEraseCost jobs + (2 * (job.indices.length * (job.sourceWidth + 1)) + 2)

theorem compactDescriptorEraseCost_eq (R : Fin T → List (Fin (A + 4))) (jobs : List (CompactDescriptorJob T))
    (hlen : ∀ job ∈ jobs, (R job.dst).length = job.indices.length * (job.sourceWidth + 1)) :
    metadataCleanCost R (jobs.map CompactDescriptorJob.dst) = compactDescriptorEraseCost jobs := by
  induction jobs with
  | nil => rfl
  | cons job jobs ih =>
    simp only [List.map_cons, metadataCleanCost, compactDescriptorEraseCost]
    rw [ih (fun j hj => hlen j (by simp [hj])), hlen job (by simp)]

theorem compactDescriptorClean_restore (R : Fin T → List (Fin (A + 4))) (jobs : List (CompactDescriptorJob T))
    (hblank : ∀ job ∈ jobs, R job.dst = []) (str : Fin T) (out : List (Fin (A + 4)))
    (hstr : ∀ job ∈ jobs, job.dst ≠ str) :
    metadataCleared (Function.update (compactDescriptorBankGenerated R jobs) str out) (jobs.map CompactDescriptorJob.dst) =
      Function.update R str out := by
  funext j
  by_cases hj : j ∈ jobs.map CompactDescriptorJob.dst
  · rw [metadataCleared_at _ _ j hj]
    obtain ⟨job, hjob, rfl⟩ := List.mem_map.mp hj
    rw [Function.update_of_ne (hstr job hjob), hblank job hjob]
  · rw [metadataCleared_keep _ _ j hj]
    by_cases hs : j = str
    · subst j; simp
    · rw [Function.update_of_ne hs, Function.update_of_ne hs]
      apply compactDescriptorBankGenerated_keep
      intro job hjob he
      exact hj (List.mem_map.mpr ⟨job, hjob, he.symm⟩)

theorem compactDescriptorClean_exec (body : P → Pr P T Q A U) (jobs : List (CompactDescriptorJob T))
    (hn : (jobs.map CompactDescriptorJob.dst).Nodup) (str : Fin T)
    (hstr : ∀ job ∈ jobs, job.dst ≠ str)
    (v : HS T Q A U) (S : Stacks T A) (out : List (Fin (A + 4)))
    (hblank : ∀ job ∈ jobs, S.R job.dst = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (metadataClean (jobs.map CompactDescriptorJob.dst))
        (mk v { S with R := Function.update (compactDescriptorBankGenerated S.R jobs) str out })
        (compactDescriptorEraseCost jobs) (mk v' { S with R := Function.update S.R str out }) := by
  let S₁ : Stacks T A := { S with R := Function.update (compactDescriptorBankGenerated S.R jobs) str out }
  obtain ⟨v', hu, he⟩ := metadataClean_exec body _ hn v S₁
  have hc : metadataCleanCost S₁.R (jobs.map CompactDescriptorJob.dst) = compactDescriptorEraseCost jobs := by
    apply compactDescriptorEraseCost_eq
    intro job hj
    change (Function.update (compactDescriptorBankGenerated S.R jobs) str out job.dst).length = _
    rw [Function.update_of_ne (hstr job hj), compactDescriptorBankGenerated_at S.R jobs hn job hj,
      hblank job hj, List.append_nil]
    simp only [CompactDescriptorJob.word, List.length_map, sourceTable_size]
  have hf := compactDescriptorClean_restore S.R jobs hblank str out hstr
  rw [hc, hf] at he
  exact ⟨v', hu, he⟩

end IntegerMultBounds.MathlibTM2.Routing
