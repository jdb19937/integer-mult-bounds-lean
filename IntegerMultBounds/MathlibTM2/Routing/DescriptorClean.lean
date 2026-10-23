module

public import IntegerMultBounds.MathlibTM2.Routing.DescriptorBankContents
public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-! Erase a compiled descriptor bank after an arbitrary change to a disjoint
stream. Initial blank descriptor destinations and every other tape are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def descriptorEraseCost : List (DescriptorJob T) → ℕ
  | [] => 1
  | job :: jobs => descriptorEraseCost jobs + (2 * (job.indices.length * job.sourceWidth) + 2)

theorem descriptorEraseCost_eq (R : Fin T → List (Fin (A + 4))) (jobs : List (DescriptorJob T))
    (hlen : ∀ job ∈ jobs, (R job.dst).length = job.indices.length * job.sourceWidth) :
    metadataCleanCost R (jobs.map DescriptorJob.dst) = descriptorEraseCost jobs := by
  induction jobs with
  | nil => rfl
  | cons job jobs ih =>
    simp only [List.map_cons, metadataCleanCost, descriptorEraseCost]
    rw [ih (fun j hj => hlen j (by simp [hj])), hlen job (by simp)]

theorem descriptorClean_restore (R : Fin T → List (Fin (A + 4))) (jobs : List (DescriptorJob T))
    (hblank : ∀ job ∈ jobs, R job.dst = []) (str : Fin T) (out : List (Fin (A + 4)))
    (hstr : ∀ job ∈ jobs, job.dst ≠ str) :
    metadataCleared (Function.update (descriptorBankGenerated R jobs) str out) (jobs.map DescriptorJob.dst) =
      Function.update R str out := by
  funext j
  by_cases hj : j ∈ jobs.map DescriptorJob.dst
  · rw [metadataCleared_at _ _ j hj]
    obtain ⟨job, hjob, rfl⟩ := List.mem_map.mp hj
    rw [Function.update_of_ne (hstr job hjob), hblank job hjob]
  · rw [metadataCleared_keep _ _ j hj]
    by_cases hs : j = str
    · subst j; simp
    · rw [Function.update_of_ne hs, Function.update_of_ne hs]
      apply descriptorBankGenerated_keep
      intro job hjob he
      exact hj (List.mem_map.mpr ⟨job, hjob, he.symm⟩)

theorem descriptorClean_exec (body : P → Pr P T Q A U) (jobs : List (DescriptorJob T))
    (hn : (jobs.map DescriptorJob.dst).Nodup) (str : Fin T)
    (hstr : ∀ job ∈ jobs, job.dst ≠ str)
    (v : HS T Q A U) (S : Stacks T A) (out : List (Fin (A + 4)))
    (hblank : ∀ job ∈ jobs, S.R job.dst = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (metadataClean (jobs.map DescriptorJob.dst))
        (mk v { S with R := Function.update (descriptorBankGenerated S.R jobs) str out })
        (descriptorEraseCost jobs) (mk v' { S with R := Function.update S.R str out }) := by
  let S₁ : Stacks T A := { S with R := Function.update (descriptorBankGenerated S.R jobs) str out }
  obtain ⟨v', hu, he⟩ := metadataClean_exec body _ hn v S₁
  have hc : metadataCleanCost S₁.R (jobs.map DescriptorJob.dst) = descriptorEraseCost jobs := by
    apply descriptorEraseCost_eq
    intro job hj
    change (Function.update (descriptorBankGenerated S.R jobs) str out job.dst).length = _
    rw [Function.update_of_ne (hstr job hj), descriptorBankGenerated_at S.R jobs hn job hj,
      hblank job hj, List.append_nil]
    simp only [DescriptorJob.word, List.length_map, sourceTable_size]
  have hf := descriptorClean_restore S.R jobs hblank str out hstr
  rw [hc, hf] at he
  exact ⟨v', hu, he⟩

end IntegerMultBounds.MathlibTM2.Routing
