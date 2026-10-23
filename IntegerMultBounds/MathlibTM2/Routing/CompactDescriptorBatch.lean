module

public import IntegerMultBounds.MathlibTM2.Routing.CompactDescriptorJob

/-! Execute a fixed bank of descriptor compilers with shared scratch.
No per-job execution hypotheses or freshly prepared intermediate banks occur. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def compactDescriptorBankGenerated (R : Fin T → List (Fin (A + 4))) :
    List (CompactDescriptorJob T) → Fin T → List (Fin (A + 4))
  | [] => R
  | job :: jobs => compactDescriptorBankGenerated (Function.update R job.dst (job.word ++ R job.dst)) jobs

def compactDescriptorBatch : List (CompactDescriptorJob T) → Pr P T Q A U
  | [] => .act .done
  | job :: jobs => .seq job.program (compactDescriptorBatch jobs)

def compactDescriptorBatchCost : List (CompactDescriptorJob T) → ℕ
  | [] => 1
  | job :: jobs => job.cost + compactDescriptorBatchCost jobs

theorem compactDescriptorBankGenerated_keep (R : Fin T → List (Fin (A + 4))) (jobs : List (CompactDescriptorJob T))
    (k : Fin T) (hk : ∀ job ∈ jobs, k ≠ job.dst) : compactDescriptorBankGenerated R jobs k = R k := by
  induction jobs generalizing R with
  | nil => rfl
  | cons job jobs ih =>
    rw [compactDescriptorBankGenerated, ih _ (fun j hj => hk j (by simp [hj]))]
    exact Function.update_of_ne (hk job (by simp)) _ _

theorem compactDescriptorBatch_exec (body : P → Pr P T Q A U) (jobs : List (CompactDescriptorJob T))
    (hzero : ∀ job ∈ jobs, ∀ other ∈ jobs, ∀ r, job.dst ≠ other.zero r)
    (hruns : ∀ job ∈ jobs, ∀ other ∈ jobs, ∀ r, job.dst ≠ other.runs r)
    (hreg : ∀ job ∈ jobs, ∀ other ∈ jobs, ∀ r, job.dst ≠ other.mask r)
    (hsaved : ∀ job ∈ jobs, ∀ other ∈ jobs, job.dst ≠ other.saved)
    (v : HS T Q A U) (S : Stacks T A) (hready : ∀ job ∈ jobs, job.Ready S.R) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ compactDescriptorBatchCost jobs ∧
      Exec body (compactDescriptorBatch jobs) (mk v S) m
        (mk v' { S with R := compactDescriptorBankGenerated S.R jobs }) := by
  induction jobs generalizing v S with
  | nil => exact ⟨v, 1, rfl, le_rfl, Exec.act (body := body) .done (mk v S)⟩
  | cons job jobs ih =>
    obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := job.exec body v S (hready job (by simp))
    let S₁ : Stacks T A := { S with R := Function.update S.R job.dst (job.word ++ S.R job.dst) }
    have ht : ∀ other ∈ jobs, other ∈ job :: jobs := fun other ho => by simp [ho]
    have hr : ∀ other ∈ jobs, other.Ready S₁.R := by
      intro other ho
      exact (hready other (ht other ho)).update job.dst _
        (fun r => hzero job (by simp) other (ht other ho) r)
        (fun r => hruns job (by simp) other (ht other ho) r)
        (fun r => hreg job (by simp) other (ht other ho) r)
        (hsaved job (by simp) other (ht other ho))
    obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := ih
      (fun j hj other ho r => hzero j (ht j hj) other (ht other ho) r)
      (fun j hj other ho r => hruns j (ht j hj) other (ht other ho) r)
      (fun j hj other ho r => hreg j (ht j hj) other (ht other ho) r)
      (fun j hj other ho => hsaved j (ht j hj) other (ht other ho)) v₁ S₁ hr
    exact ⟨v₂, m₁ + m₂, hu₂.trans hu₁, Nat.add_le_add hm₁ hm₂, Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Routing
