module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryFieldJob

/-! Execute a fixed bank of binary-width field generators with shared scratch.
No per-job execution hypotheses or freshly prepared intermediate banks occur. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def binaryFieldsGenerated (R : Fin T → List (Fin (A + 4))) :
    List (BinaryFieldJob T) → Fin T → List (Fin (A + 4))
  | [] => R
  | job :: jobs => binaryFieldsGenerated (Function.update R job.dst (job.word ++ R job.dst)) jobs

def binaryFieldBatch : List (BinaryFieldJob T) → Pr P T Q A U
  | [] => .act .done
  | job :: jobs => .seq job.program (binaryFieldBatch jobs)

def binaryFieldBatchCost : List (BinaryFieldJob T) → ℕ
  | [] => 1
  | job :: jobs => job.cost + binaryFieldBatchCost jobs

theorem binaryFieldsGenerated_keep (R : Fin T → List (Fin (A + 4))) (jobs : List (BinaryFieldJob T))
    (k : Fin T) (hk : ∀ job ∈ jobs, k ≠ job.dst) : binaryFieldsGenerated R jobs k = R k := by
  induction jobs generalizing R with
  | nil => rfl
  | cons job jobs ih =>
    rw [binaryFieldsGenerated, ih _ (fun j hj => hk j (by simp [hj]))]
    exact Function.update_of_ne (hk job (by simp)) _ _

theorem binaryFieldBatch_exec (body : P → Pr P T Q A U) (jobs : List (BinaryFieldJob T))
    (hsep : ∀ job ∈ jobs, ∀ other ∈ jobs, ∀ r : BinaryZeroReg,
      r ≠ .dst → job.dst ≠ other.reg r)
    (v : HS T Q A U) (S : Stacks T A) (hready : ∀ job ∈ jobs, job.Ready S.R) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ binaryFieldBatchCost jobs ∧
      Exec body (binaryFieldBatch jobs) (mk v S) m
        (mk v' { S with R := binaryFieldsGenerated S.R jobs }) := by
  induction jobs generalizing v S with
  | nil => exact ⟨v, 1, rfl, le_rfl, Exec.act (body := body) .done (mk v S)⟩
  | cons job jobs ih =>
    obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := job.exec body v S (hready job (by simp))
    let S₁ : Stacks T A := { S with R := Function.update S.R job.dst (job.word ++ S.R job.dst) }
    have ht : ∀ other ∈ jobs, other ∈ job :: jobs := fun other ho => by simp [ho]
    have hr : ∀ other ∈ jobs, other.Ready S₁.R := by
      intro other ho
      exact (hready other (ht other ho)).update job.dst _
        (fun r hrd => hsep job (by simp) other (ht other ho) r hrd)
    obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := ih
      (fun j hj other ho r hrd => hsep j (ht j hj) other (ht other ho) r hrd) v₁ S₁ hr
    exact ⟨v₂, m₁ + m₂, hu₂.trans hu₁, Nat.add_le_add hm₁ hm₂, Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Routing
