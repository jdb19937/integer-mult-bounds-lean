module

public import IntegerMultBounds.MathlibTM2.Routing.DescriptorTableCompile

/-! A reusable descriptor compiler job. Only its destination changes; binary
selector frames, width inputs, archive and compiler scratch are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

structure DescriptorJob (T : ℕ) where
  reg : BinaryMaskReg → Fin T
  selectors : Fin T
  saved : Fin T
  dst : Fin T
  width : ℕ
  sourceWidth : ℕ
  indices : List (Fin sourceWidth)

namespace DescriptorJob

variable {T Q A : ℕ} {P U : Type}

def word (job : DescriptorJob T) : List (Fin (A + 4)) :=
  (sourceTable job.indices).flatten.map bitSymbol

def cost (job : DescriptorJob T) : ℕ :=
  job.indices.length * (descriptorCompileCallCost job.width job.sourceWidth + 2) +
    2 * (job.indices.length * (job.width + 1)) + 4

def program (job : DescriptorJob T) : Pr P T Q A U :=
  descriptorCompileProgram job.reg job.selectors job.saved job.dst

structure Ready (job : DescriptorJob T) (R : Fin T → List (Fin (A + 4))) : Prop where
  injective : Function.Injective job.reg
  selectors_saved : job.selectors ≠ job.saved
  selectors_dst : job.selectors ≠ job.dst
  saved_dst : job.saved ≠ job.dst
  selectors_reg : ∀ r, job.selectors ≠ job.reg r
  saved_reg : ∀ r, job.saved ≠ job.reg r
  dst_reg : ∀ r, job.dst ≠ job.reg r
  fits : job.sourceWidth < 2 ^ job.width
  compiler : DescriptorCompileReady job.reg R job.width job.sourceWidth
  input : R job.selectors = descriptorSelectorFrames job.width job.indices.reverse
  archive : R job.saved = []

theorem Ready.update {job : DescriptorJob T} {R : Fin T → List (Fin (A + 4))}
    (h : job.Ready R) (k : Fin T) (word : List (Fin (A + 4)))
    (hreg : ∀ r, k ≠ job.reg r) (hselectors : k ≠ job.selectors) (hsaved : k ≠ job.saved) :
    job.Ready (Function.update R k word) := by
  refine { h with compiler := ?_, input := ?_, archive := ?_ }
  · constructor
    · rw [Function.update_of_ne (hreg .width).symm]; exact h.compiler.width
    · intro r hr
      rw [Function.update_of_ne (hreg r).symm]; exact h.compiler.blank r hr
  · rw [Function.update_of_ne hselectors.symm]; exact h.input
  · rw [Function.update_of_ne hsaved.symm]; exact h.archive

theorem exec (body : P → Pr P T Q A U) (job : DescriptorJob T)
    (v : HS T Q A U) (S : Stacks T A) (h : job.Ready S.R) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ job.cost ∧
      Exec body job.program (Host.mk v S) m
        (Host.mk v' { S with R := Function.update S.R job.dst (job.word ++ S.R job.dst) }) := by
  exact sourceTableCompile_exec body job.reg h.injective job.selectors job.saved job.dst
    h.selectors_saved h.selectors_dst h.saved_dst h.selectors_reg h.saved_reg h.dst_reg
    job.width h.fits job.indices v S h.compiler h.input h.archive

end DescriptorJob
end IntegerMultBounds.MathlibTM2.Routing
