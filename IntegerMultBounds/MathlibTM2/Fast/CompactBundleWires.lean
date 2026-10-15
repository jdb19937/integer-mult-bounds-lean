module

public import IntegerMultBounds.MathlibTM2.Fast.CompactBdWiresCost
public import IntegerMultBounds.MathlibTM2.Fast.CompactBundleMnLay

/-! The actual retuned wires and source distribution as complete charged bundles. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Mult.Sizes
open IntegerMultBounds.MathlibTM2.Fast.TableVM Filter
noncomputable section

/-- Full wire bundle from the existing source-converter postcondition. -/
def compactBdWires : BdWires (fun n => mnσ (blP₀ dsW n) (compactDsyV₀ n)) where
  prog := compactBdWiresProg
  cost := compactBdWiresCost
  spec := compactBdWires_spec
  costBound := ⟨2^25,7,by
    filter_upwards [compactBdWiresCost_le] with n h
    have hr : 2^5*(r n*dsW n)≤2^25*(r n*dsW n) :=
      Nat.mul_le_mul_right _ (by norm_num)
    omega⟩

/-- Retuned source distribution. The existing stronger parameter-postcondition
bridge is explicit; no legacy layout or legacy total-cost theorem is asserted. -/
def compactBdDist
    (hP : ∀ (R : Regs mnT bdA) (n : ℕ),MnPostParam R n → BdPostParam R n) :
    MnDist mnKa mnLb bdW (fun n => mnσ (blP₀ dsW n) (compactDsyV₀ n)) :=
  bdDist compactBdWires hP

@[simp] theorem compactBdDist_prog
    (hP : ∀ (R : Regs mnT bdA) (n : ℕ),MnPostParam R n → BdPostParam R n) :
    (compactBdDist hP).distP=bdDistP compactBdWires := rfl

@[simp] theorem compactBdDist_cost
    (hP : ∀ (R : Regs mnT bdA) (n : ℕ),MnPostParam R n → BdPostParam R n) (n : ℕ) :
    (compactBdDist hP).cost n=dsMainCost n+bdRndCost n+compactBdWiresCost n := rfl

end
end IntegerMultBounds.MathlibTM2.Fast.Main
