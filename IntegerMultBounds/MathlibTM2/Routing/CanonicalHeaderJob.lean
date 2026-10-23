module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalHeaderValue

/-! One canonical-header copy job. Width/value data specify its contract and
cost; the executed program reads the live binary source and shared scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

structure CanonicalHeaderJob (T : ℕ) where
  reg : Fin 4 → Fin T
  width : ℕ
  value : ℕ

namespace CanonicalHeaderJob

variable {T Q A : ℕ} {P U : Type}

def dst (job : CanonicalHeaderJob T) := job.reg 1

def word (job : CanonicalHeaderJob T) : List (Fin (A + 4)) :=
  (GrowingCounterData.advance job.value []).map bitSymbol

def program (job : CanonicalHeaderJob T) : Pr P T Q A U :=
  binaryCanonicalCopyProgram (job.reg 0) job.dst (job.reg 2) (job.reg 3)

def cost (job : CanonicalHeaderJob T) := 10 * job.width + 12

theorem word_length_le (job : CanonicalHeaderJob T) (hfit : job.value < 2 ^ job.width) :
    (job.word (A := A)).length ≤ job.width := by
  simpa only [word, List.length_map] using canonicalHeader_length_le job.width job.value hfit

structure Ready (job : CanonicalHeaderJob T) (bank : Fin T → List (Fin (A + 4))) : Prop where
  injective : Function.Injective job.reg
  fit : job.value < 2 ^ job.width
  source : bank (job.reg 0) = binSyms job.width job.value
  blank : ∀ i : Fin 4, i ≠ 0 → bank (job.reg i) = []

theorem Ready.update {job : CanonicalHeaderJob T} {bank : Fin T → List (Fin (A + 4))}
    (ready : job.Ready bank) (dst : Fin T) (word : List (Fin (A + 4)))
    (hsep : ∀ i, dst ≠ job.reg i) : job.Ready (Function.update bank dst word) := by
  constructor
  · exact ready.injective
  · exact ready.fit
  · rw [Function.update_of_ne (hsep 0).symm]; exact ready.source
  · intro i hi
    rw [Function.update_of_ne (hsep i).symm]
    exact ready.blank i hi

theorem exec (job : CanonicalHeaderJob T) (body : P → Pr P T Q A U)
    (v : HS T Q A U) (S : Stacks T A) (ready : job.Ready S.R) :
    ∃ v', v'.user = v.user ∧ Exec body job.program (Host.mk v S) job.cost
      (Host.mk v' { S with R := Function.update S.R job.dst job.word }) := by
  exact binaryCanonicalHeaderCopy_exec body (job.reg 0) (job.reg 1) (job.reg 2) (job.reg 3)
    (by simp [List.nodup_cons, ready.injective.eq_iff]) job.width job.value ready.fit v S
    ready.source (ready.blank 1 (by decide)) (ready.blank 2 (by decide)) (ready.blank 3 (by decide))

end CanonicalHeaderJob
end IntegerMultBounds.MathlibTM2.Routing
