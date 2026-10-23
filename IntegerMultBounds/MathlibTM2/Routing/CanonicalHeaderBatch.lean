module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalHeaderJob

/-! Execute an arbitrary fixed list of canonical-header jobs with shared scratch.
Initial inputs establish all later readiness; no per-job execution is assumed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def canonicalHeadersGenerated (bank : Fin T → List (Fin (A + 4))) :
    List (CanonicalHeaderJob T) → Fin T → List (Fin (A + 4))
  | [] => bank
  | job :: jobs => canonicalHeadersGenerated (Function.update bank job.dst job.word) jobs

def canonicalHeaderBatch : List (CanonicalHeaderJob T) → Pr P T Q A U
  | [] => .act .done
  | job :: jobs => .seq job.program (canonicalHeaderBatch jobs)

def canonicalHeaderBatchCost : List (CanonicalHeaderJob T) → ℕ
  | [] => 1
  | job :: jobs => job.cost + canonicalHeaderBatchCost jobs

theorem canonicalHeadersGenerated_keep (bank : Fin T → List (Fin (A + 4))) (jobs : List (CanonicalHeaderJob T))
    (i : Fin T) (hi : ∀ job ∈ jobs, i ≠ job.dst) : canonicalHeadersGenerated bank jobs i = bank i := by
  induction jobs generalizing bank with
  | nil => rfl
  | cons job jobs ih =>
    rw [canonicalHeadersGenerated, ih _ (fun j hj => hi j (by simp [hj]))]
    exact Function.update_of_ne (hi job (by simp)) _ _

theorem canonicalHeadersGenerated_at (bank : Fin T → List (Fin (A + 4)))
    (jobs : List (CanonicalHeaderJob T)) (hdst : (jobs.map CanonicalHeaderJob.dst).Nodup)
    (job : CanonicalHeaderJob T) (hjob : job ∈ jobs) :
    canonicalHeadersGenerated bank jobs job.dst = job.word := by
  induction jobs generalizing bank with
  | nil => simp at hjob
  | cons j jobs ih =>
    have hn := List.nodup_cons.mp (show (j.dst :: jobs.map CanonicalHeaderJob.dst).Nodup from hdst)
    rcases List.mem_cons.mp hjob with he | hm
    · subst job
      rw [canonicalHeadersGenerated, canonicalHeadersGenerated_keep]
      · simp
      · intro other ho he
        exact hn.1 (List.mem_map.mpr ⟨other, ho, he.symm⟩)
    · exact ih (Function.update bank j.dst j.word) hn.2 hm

theorem canonicalHeaderBatch_exec (body : P → Pr P T Q A U) (jobs : List (CanonicalHeaderJob T))
    (hsep : ∀ job ∈ jobs, ∀ other ∈ jobs, job ≠ other → ∀ i, job.dst ≠ other.reg i)
    (hnodup : jobs.Nodup) (v : HS T Q A U) (S : Stacks T A)
    (hready : ∀ job ∈ jobs, job.Ready S.R) :
    ∃ v', v'.user = v.user ∧ Exec body (canonicalHeaderBatch jobs) (mk v S) (canonicalHeaderBatchCost jobs)
      (mk v' { S with R := canonicalHeadersGenerated S.R jobs }) := by
  induction jobs generalizing v S with
  | nil => exact ⟨v, rfl, Exec.act (body := body) .done (mk v S)⟩
  | cons job jobs ih =>
    obtain ⟨v₁, hu₁, he₁⟩ := job.exec body v S (hready job (by simp))
    let S₁ : Stacks T A := { S with R := Function.update S.R job.dst job.word }
    have ht : ∀ other ∈ jobs, other ∈ job :: jobs := fun other ho => by simp [ho]
    have hne : ∀ other ∈ jobs, job ≠ other := by
      intro other ho he
      exact (List.nodup_cons.mp hnodup).1 (he ▸ ho)
    have hr : ∀ other ∈ jobs, other.Ready S₁.R := by
      intro other ho
      exact (hready other (ht other ho)).update job.dst job.word
        (hsep job (by simp) other (ht other ho) (hne other ho))
    obtain ⟨v₂, hu₂, he₂⟩ := ih
      (fun j hj other ho hjo i => hsep j (ht j hj) other (ht other ho) hjo i)
      (List.nodup_cons.mp hnodup).2 v₁ S₁ hr
    exact ⟨v₂, hu₂.trans hu₁, Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Routing
