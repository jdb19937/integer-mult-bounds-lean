module

public import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapPipeline
public import IntegerMultBounds.MathlibTM2.Fast.DistSynMain

/-! The actual distribution wire file supplies predecessor depth to the bootstrap. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.MathlibTM2.Mult.Sizes
noncomputable section

private lemma projectedRead {T T' A : ℕ} (e : Fin T → Fin T')
    (S₁ : Stacks T A) (S : Stacks T' A) (h : embStk e S=S₁) (x : Fin T) :
    S.R (e x)=S₁.R x := congrArg (fun Z : Stacks T A => Z.R x) h

lemma compactMnBootstrap_initial_depth (n : ℕ) :
    dsyV₀ n (.p .D)=List.replicate (d n-1) tick := by
  change List.replicate (dsyEs n).length tick=_
  rw [TableVM.ds_length_cvAx]

/-- The concrete postcondition of `dsyWires_spec` supplies the copied depth. -/
lemma compactMnBootstrap_distribution_depth (n : ℕ) (S : Stacks mnT bdA)
    (hw : ∀ x,S.R (mnLay x)=mnσ (blP₀ dsW n) (dsyV₀ n) x) :
    S.R (mnLay (.wire (synWire (.p .D))))=List.replicate (d n-1) tick := by
  rw [hw,mnσ_wire,compactMnBootstrap_initial_depth]

/-- Main-stage placement preserves the exact initial depth source register. -/
lemma compactMnBootstrap_placed_depth (n : ℕ) (S₁ : Stacks mnT bdA)
    (S : Stacks compactMnT bdA)
    (hw : ∀ x,S₁.R (mnLay x)=mnσ (blP₀ dsW n) (dsyV₀ n) x) :
    ((compactMainFinalStacks S₁ S).R
      (compactMnLayerReg (compactLegacyReg (sreg (.p .D))))).length=d n-1 := by
  have h := projectedRead compactMnLegacyReg S₁ (compactMainFinalStacks S₁ S)
    (compactMainFinalStacks_projection S₁ S) (mnLay (.wire (synWire (.p .D))))
  rw [compactMnLegacyReg_lay] at h
  simp only [compactMapRegName] at h
  rw [compactMnSyn_legacy]
  change ((compactMainFinalStacks S₁ S).R
    (compactMnLay (.wire (synWire (.p .D))))).length=_
  rw [h,compactMnBootstrap_distribution_depth n S₁ hw,List.length_replicate]

end
end IntegerMultBounds.MathlibTM2.Fast.Main
