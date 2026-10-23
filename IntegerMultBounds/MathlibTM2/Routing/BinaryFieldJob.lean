module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryFullMask
public import IntegerMultBounds.MathlibTM2.Routing.BinaryZeroField

/-! A common binary-width interface for zero fields and full masks.
Numerical annotations affect the contract and cost, never the executed code. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks

structure BinaryFieldJob (T : ℕ) where
  reg : BinaryZeroReg → Fin T
  ones : Bool
  width : ℕ
  value : ℕ

namespace BinaryFieldJob

variable {T Q A : ℕ} {P U : Type}

def dst (job : BinaryFieldJob T) := job.reg .dst

def word (job : BinaryFieldJob T) : List (Fin (A + 4)) :=
  binSyms job.value (if job.ones then maskVal job.value id else 0)

def cost (job : BinaryFieldJob T) : ℕ :=
  if job.ones then job.width * (4 * job.value + 11) + 2 * job.value + 6
  else job.width * (4 * job.value + 11) + 8 * job.value + 12

def program (job : BinaryFieldJob T) : Pr P T Q A U :=
  if job.ones then toUnary (job.reg .width) job.dst (job.reg (.scratch 0))
    (job.reg (.scratch 1)) (job.reg (.scratch 2))
  else binaryZeroFieldProgram job.reg

structure Ready (job : BinaryFieldJob T) (R : Fin T → List (Fin (A + 4))) : Prop where
  injective : Function.Injective job.reg
  fits : job.value < 2 ^ job.width
  input : R (job.reg .width) = binSyms job.width job.value
  blank : ∀ r, r ≠ .width → r ≠ .dst → R (job.reg r) = []

theorem Ready.update {job : BinaryFieldJob T} {R : Fin T → List (Fin (A + 4))}
    (h : job.Ready R) (k : Fin T) (word : List (Fin (A + 4)))
    (hk : ∀ r, r ≠ .dst → k ≠ job.reg r) : job.Ready (Function.update R k word) := by
  refine ⟨h.injective, h.fits, ?_, ?_⟩
  · rw [Function.update_of_ne (hk .width (by simp)).symm]; exact h.input
  · intro r hw hd
    rw [Function.update_of_ne (hk r hd).symm]
    exact h.blank r hw hd

theorem exec (body : P → Pr P T Q A U) (job : BinaryFieldJob T)
    (v : HS T Q A U) (S : Stacks T A) (h : job.Ready S.R) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ job.cost ∧
      Exec body job.program (Host.mk v S) m
        (Host.mk v' { S with R := Function.update S.R job.dst (job.word ++ S.R job.dst) }) := by
  cases ho : job.ones with
  | false =>
    obtain ⟨v', m, hu, hm, he⟩ := binaryZeroField_exec body job.reg h.injective job.width job.value
      h.fits v S h.input (h.blank .unary (by simp) (by simp))
      (fun i => h.blank (.scratch i) (by simp) (by simp))
    exact ⟨v', m, hu, by simpa [cost, ho] using hm, by simpa [program, word, dst, ho] using he⟩
  | true =>
    obtain ⟨v', m, hu, hm, he⟩ := binaryFullMask_exec body (job.reg .width) job.dst
      (job.reg (.scratch 0)) (job.reg (.scratch 1)) (job.reg (.scratch 2))
      (by simp [dst, List.nodup_cons, h.injective.eq_iff]) job.width job.value h.fits v S h.input
      (h.blank (.scratch 0) (by simp) (by simp)) (h.blank (.scratch 1) (by simp) (by simp))
      (h.blank (.scratch 2) (by simp) (by simp))
    exact ⟨v', m, hu, by simpa [cost, ho] using hm, by simpa [program, word, ho] using he⟩

end BinaryFieldJob

end IntegerMultBounds.MathlibTM2.Routing
