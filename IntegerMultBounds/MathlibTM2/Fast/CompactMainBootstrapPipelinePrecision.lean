module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapPipelineSource
public import IntegerMultBounds.MathlibTM2.Fast.MainCorrect

/-! The existing parameter stage supplies the actual original-precision source. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.MathlibTM2.Mult.Sizes
noncomputable section
variable {A : ℕ}

private lemma projectedRead {T T' A : ℕ} (e : Fin T → Fin T')
    (S₁ : Stacks T A) (S : Stacks T' A) (h : embStk e S=S₁) (x : Fin T) :
    S.R (e x)=S₁.R x := congrArg (fun Z : Stacks T A => Z.R x) h

lemma compactMnBootstrap_parameter_precision (S : Stacks mnT A) (x y n : ℕ)
    (h : MnMid S x y n) : S.R (mnRg (.io .dpn))=List.replicate (p n) tick :=
  h.dpn

lemma compactMnBootstrap_placed_precision (S₁ : Stacks mnT A) (S : Stacks compactMnT A)
    (x y n : ℕ) (hmid : MnMid S₁ x y n) :
    ((compactMainFinalStacks S₁ S).R (compactMnRg (.io .dpn))).length=p n := by
  have h := projectedRead compactMnLegacyReg S₁ (compactMainFinalStacks S₁ S)
    (compactMainFinalStacks_projection S₁ S) (mnRg (.io .dpn))
  rw [compactMnLegacyReg_rg] at h
  rw [h,compactMnBootstrap_parameter_precision S₁ x y n hmid,List.length_replicate]

end
end IntegerMultBounds.MathlibTM2.Fast.Main
