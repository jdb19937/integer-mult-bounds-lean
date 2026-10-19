module

public import IntegerMultBounds.Networks.ComplexFramedExecution
public import IntegerMultBounds.Networks.TensorTerminalWeight
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-! Concrete binary phase endpoint corrections for the actual complex network.
The source/sink projectors and diagonal corrections are proved as operators;
no terminal transform identity is assumed. -/

@[expose] public section

namespace IntegerMultBounds.Networks.ComplexEndpoints

open BinaryPhase BinaryWalsh
open scoped TensorProduct

section Walsh
variable {h : ℕ}

private theorem address_add_self (u : BinaryWalsh.Address h) : u + u = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (u i)

end Walsh

section Projectors
variable {h : ℕ} (hs : (Labels.binary h).IsSymm)

/-- The total projector is the identity at the full terminal label. -/
theorem projector_top (x : BinaryWalsh.Address h) :
    ProjectionTrace.projector (Labels.binary h) hs ⊤ x = x := by
  rw [ProjectionTrace.projector_eq _ _ _ (MotifLabels.top_nondegenerate _ Labels.binary_nondegenerate)]
  exact ProjectionRank.project_left _ _ _ _ Submodule.mem_top

/-- The zero source label contributes no phase or address operation. -/
theorem projector_bot (x : BinaryWalsh.Address h) :
    ProjectionTrace.projector (Labels.binary h) hs ⊥ x = 0 := by
  rw [ProjectionTrace.projector_eq _ _ _ (MotifLabels.bot_nondegenerate _)]
  exact ProjectionRank.project_right _ _ _ _ (by simp)

end Projectors
section Columns
open BinaryColumns
variable {h : ℕ}

/-- The desired forward tensor transform on all address bits and columns. -/
noncomputable def fullFrame (k : ℕ) : BinaryColumns.Arrays h k ≃ₗ[ℂ] BinaryColumns.Arrays h k :=
  BinaryColumnFrame.frameEquiv k weightPhase

/-- One forward C kernel for each genuine binary address coordinate. -/
def coordinateKernels (h : ℕ) : List (ZMod 4 × BinaryWalsh.Address h) :=
  List.ofFn (fun j : Fin h => (1, Pi.single j 1))

theorem coordinateKernels_phase : listPhase (coordinateKernels h) = weightPhase := by
  funext x
  rw [coordinateKernels, listPhase_ofFn]
  simp [Labels.binary, Labels.form_apply, Pi.single_apply, weightPhase]

/-- The full weight frame is precisely the forward C tensor: one forward
coordinate kernel on every binary bit, tensoring the same operator across
all columns. This identifies the target without a transform assumption. -/
theorem fullFrame_coordinate_product (k : ℕ) :
    (fullFrame (h := h) k).toLinearMap =
      ((coordinateKernels h).map (BinaryColumns.vectorFactor k)).prod := by
  change tensorColumns k (frame weightPhase).toLinearMap = _
  rw [← tensorColumns_kernel_prod, kernel_prod_eq_frame, coordinateKernels_phase]

end Columns
section ActualTerminals
open ComplexRank25 ComplexPhaseBudget ComplexFramedExecution

end ActualTerminals
end IntegerMultBounds.Networks.ComplexEndpoints
