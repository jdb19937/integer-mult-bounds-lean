module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalHeaderBatch
public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-! Erase a generated canonical-header bank after an arbitrary stream change.
All other tapes return to their initial values, with erasure priced by widths. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def canonicalHeaderEraseCost : List (CanonicalHeaderJob T) → ℕ
  | [] => 1
  | job :: jobs => canonicalHeaderEraseCost jobs + (2 * job.width + 2)

theorem canonicalHeadersCleared_restore (bank : Fin T → List (Fin (A + 4)))
    (jobs : List (CanonicalHeaderJob T)) (hblank : ∀ job ∈ jobs, bank job.dst = []) :
    metadataCleared (canonicalHeadersGenerated bank jobs) (jobs.map CanonicalHeaderJob.dst) = bank := by
  funext i
  by_cases hi : i ∈ jobs.map CanonicalHeaderJob.dst
  · rw [metadataCleared_at _ _ i hi]
    obtain ⟨job, hj, rfl⟩ := List.mem_map.mp hi
    exact (hblank job hj).symm
  · rw [metadataCleared_keep _ _ i hi]
    apply canonicalHeadersGenerated_keep
    intro job hj he
    exact hi (List.mem_map.mpr ⟨job, hj, he.symm⟩)

theorem canonicalHeaderCleanCost_le (bank : Fin T → List (Fin (A + 4)))
    (jobs : List (CanonicalHeaderJob T)) (hwidth : ∀ job ∈ jobs, (bank job.dst).length ≤ job.width) :
    metadataCleanCost bank (jobs.map CanonicalHeaderJob.dst) ≤ canonicalHeaderEraseCost jobs := by
  induction jobs with
  | nil => exact le_rfl
  | cons job jobs ih =>
    have hh := hwidth job (by simp)
    have ht := ih (fun j hj => hwidth j (by simp [hj]))
    simp only [List.map_cons, metadataCleanCost, canonicalHeaderEraseCost]
    omega

theorem canonicalHeaderClean_exec (body : P → Pr P T Q A U) (jobs : List (CanonicalHeaderJob T))
    (hdst : (jobs.map CanonicalHeaderJob.dst).Nodup)
    (hfit : ∀ job ∈ jobs, job.value < 2 ^ job.width)
    (src : Fin T) (hsrc : src ∉ jobs.map CanonicalHeaderJob.dst)
    (v : HS T Q A U) (S : Stacks T A) (records : List (Fin (A + 4)))
    (hblank : ∀ job ∈ jobs, S.R job.dst = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ canonicalHeaderEraseCost jobs ∧
      Exec body (metadataClean (jobs.map CanonicalHeaderJob.dst))
        (mk v { S with R := Function.update (canonicalHeadersGenerated S.R jobs) src records }) m
        (mk v' { S with R := Function.update S.R src records }) := by
  let S₁ : Stacks T A := { S with R := Function.update (canonicalHeadersGenerated S.R jobs) src records }
  obtain ⟨v', hu, he⟩ := metadataClean_exec body (jobs.map CanonicalHeaderJob.dst) hdst v S₁
  have hf : metadataCleared S₁.R (jobs.map CanonicalHeaderJob.dst) = Function.update S.R src records := by
    rw [metadataCleared_update _ _ _ _ hsrc, canonicalHeadersCleared_restore _ _ hblank]
  have hc : metadataCleanCost S₁.R (jobs.map CanonicalHeaderJob.dst) ≤ canonicalHeaderEraseCost jobs := by
    apply canonicalHeaderCleanCost_le
    intro job hj
    have hs : job.dst ≠ src := by
      intro he
      exact hsrc (List.mem_map.mpr ⟨job, hj, he⟩)
    change (Function.update (canonicalHeadersGenerated S.R jobs) src records job.dst).length ≤ job.width
    rw [Function.update_of_ne hs, canonicalHeadersGenerated_at S.R jobs hdst job hj]
    exact job.word_length_le (hfit job hj)
  rw [hf] at he
  exact ⟨v', _, hu, hc, he⟩

end IntegerMultBounds.MathlibTM2.Routing
