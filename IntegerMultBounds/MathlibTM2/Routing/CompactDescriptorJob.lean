module

public import IntegerMultBounds.MathlibTM2.Routing.CompactDescriptorCompile

/-! A reusable compact-descriptor job and readiness stable under unrelated
output writes. Compact operands and all compiler scratch are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

structure CompactDescriptorJob (T : ℕ) where
  zero : BinaryZeroReg → Fin T
  runs : SelectorRunReg → Fin T
  mask : BinaryMaskReg → Fin T
  saved : Fin T
  dst : Fin T
  widthBits : ℕ
  gapBits : ℕ
  width : ℕ
  sourceWidth : ℕ
  indices : List (Fin (sourceWidth + 1))

namespace CompactDescriptorJob

variable {T Q A : ℕ} {P U : Type}

def word (job : CompactDescriptorJob T) : List (Fin (A + 4)) :=
  (sourceTable job.indices).flatten.map bitSymbol

def cost (job : CompactDescriptorJob T) : ℕ :=
  ((job.widthBits * (4 * job.width + 11) + 8 * job.width + 13) +
    selectorRunLoopCost job.gapBits job.width (SparseSelectorRun.compress job.indices.reverse).reverse +
    2 * (selectorRunFrames (A := 0) job.gapBits job.width (SparseSelectorRun.compress job.indices.reverse).reverse).length +
    3 + (2 * (job.width + 1) + 2)) +
    (job.indices.length * (descriptorCompileCallCost job.width (job.sourceWidth + 1) + 2) +
      2 * (job.indices.length * (job.width + 1)) + 4) +
    (2 * (job.indices.length * (job.width + 1)) + 2)

def program (job : CompactDescriptorJob T) : Pr P T Q A U :=
  compactDescriptorProgram job.zero job.runs job.mask job.saved job.dst

structure Ready (job : CompactDescriptorJob T) (R : Fin T → List (Fin (A + 4))) : Prop where
  zero_injective : Function.Injective job.zero
  runs_injective : Function.Injective job.runs
  mask_injective : Function.Injective job.mask
  block : job.zero .dst = job.runs .block
  selectors_saved : job.runs .dst ≠ job.saved
  selectors_dst : job.runs .dst ≠ job.dst
  saved_dst : job.saved ≠ job.dst
  selectors_mask : ∀ r, job.runs .dst ≠ job.mask r
  saved_mask : ∀ r, job.saved ≠ job.mask r
  dst_mask : ∀ r, job.dst ≠ job.mask r
  width_fits : job.width < 2 ^ job.widthBits
  source_fits : job.sourceWidth + 1 < 2 ^ job.width
  gap_fits : job.indices.length < 2 ^ job.gapBits
  width : R (job.zero .width) = binSyms job.widthBits job.width
  unary : R (job.zero .unary) = []
  scratch : ∀ i, R (job.zero (.scratch i)) = []
  input : R (job.runs .src) = selectorRunFrames job.gapBits job.width (SparseSelectorRun.compress job.indices.reverse).reverse
  archive : R (job.runs .archive) = []
  block_blank : R (job.runs .block) = []
  selectors : R (job.runs .dst) = []
  blank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .block → r ≠ .dst → R (job.runs r) = []
  compiler : DescriptorCompileReady job.mask R job.width (job.sourceWidth + 1)
  saved : R job.saved = []

theorem Ready.update {job : CompactDescriptorJob T} {R : Fin T → List (Fin (A + 4))}
    (h : job.Ready R) (k : Fin T) (word : List (Fin (A + 4)))
    (hz : ∀ r, k ≠ job.zero r) (hr : ∀ r, k ≠ job.runs r)
    (hm : ∀ r, k ≠ job.mask r) (hs : k ≠ job.saved) :
    job.Ready (Function.update R k word) := by
  refine { h with width := ?_, unary := ?_, scratch := ?_, input := ?_, archive := ?_, block_blank := ?_, selectors := ?_, blank := ?_, compiler := ?_, saved := ?_ }
  · rw [Function.update_of_ne (hz _).symm]; exact h.width
  · rw [Function.update_of_ne (hz _).symm]; exact h.unary
  · intro i; rw [Function.update_of_ne (hz _).symm]; exact h.scratch i
  · rw [Function.update_of_ne (hr _).symm]; exact h.input
  · rw [Function.update_of_ne (hr _).symm]; exact h.archive
  · rw [Function.update_of_ne (hr _).symm]; exact h.block_blank
  · rw [Function.update_of_ne (hr _).symm]; exact h.selectors
  · intro r hsrc ha hb hd; rw [Function.update_of_ne (hr _).symm]; exact h.blank r hsrc ha hb hd
  · constructor
    · rw [Function.update_of_ne (hm _).symm]; exact h.compiler.width
    · intro r hne; rw [Function.update_of_ne (hm _).symm]; exact h.compiler.blank r hne
  · rw [Function.update_of_ne hs.symm]; exact h.saved

theorem selectorRunFrames_length {W : ℕ} (Lg L : ℕ) (rs : List (SparseSelectorRun W)) :
    (selectorRunFrames (A := A) Lg L rs).length = rs.length * (Lg + L + 2) := by
  induction rs with
  | nil => simp [selectorRunFrames]
  | cons r rs ih =>
    simp only [selectorRunFrames, List.length_append, List.length_cons, length_binSyms, ih, Nat.add_mul, Nat.one_mul]
    omega

theorem exec (body : P → Pr P T Q A U) (job : CompactDescriptorJob T)
    (v : HS T Q A U) (S : Stacks T A) (h : job.Ready S.R) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ job.cost ∧
      Exec body job.program (Host.mk v S) steps
        (Host.mk v' { S with R := Function.update S.R job.dst (job.word ++ S.R job.dst) }) := by
  obtain ⟨v', steps, hu, ht, he⟩ := compactDescriptor_exec body job.zero h.zero_injective job.runs h.runs_injective
    h.block job.mask h.mask_injective job.saved job.dst h.selectors_saved h.selectors_dst h.saved_dst
    h.selectors_mask h.saved_mask h.dst_mask job.widthBits job.gapBits job.width h.width_fits h.source_fits
    job.indices h.gap_fits v S h.width h.unary h.scratch h.input h.archive h.block_blank h.selectors h.blank h.compiler h.saved
  exact ⟨v', steps, hu, by simpa only [cost, selectorRunFrames_length] using ht, he⟩

end CompactDescriptorJob
end IntegerMultBounds.MathlibTM2.Routing
