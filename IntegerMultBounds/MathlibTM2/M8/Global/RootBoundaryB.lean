module

public import IntegerMultBounds.MathlibTM2.M8.Global.CompilerBoundaryB
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.RootFacts

/-! Connect root endpoint witnesses to all actual compiler frames on the
output and centre read slots. Concrete endpoint checks remain separate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames

theorem compiler_output_boundary (j : Nat) (hj : j < 3 * leafCount)
    (w : Nat × Nat) (hw : GeometryB.rootOk j w = true) :
    ∀ f ∈ fseq (.inl (.aux (dagB.compile.pend (.root j)))) (opBlocks dagB.opsB opFrame).flatten,
      Nested f (assignment.output j) := by
  have hroot : j < rootCount := by
    have hcount : rootCount = 3 * leafCount + 23 := rfl
    omega
  have he : Nested (frameOfLabel (rootLabel j)) (assignment.output j) := by
    simpa only [frameOfLabel, rootLabel, assignment,
      ite_eq_left (show j / 3 < leafCount by omega)] using GeometryB.rootOk_output j hj w hw
  exact fun f hf => (compiler_root_bound j hroot f hf).trans he

theorem compiler_centre_boundary (c : Fin 23) (w : Nat × Nat)
    (hw : GeometryB.rootOk (3 * leafCount + c.val) w = true) :
    ∀ f ∈ fseq (.inl (.aux (centreSlots c))) (opBlocks dagB.opsB opFrame).flatten,
      Nested f (starFrame c.val) := by
  have hroot : 3 * leafCount + c.val < rootCount := by
    have hcount : rootCount = 3 * leafCount + 23 := rfl
    omega
  have he : Nested (frameOfLabel (rootLabel (3 * leafCount + c.val))) (starFrame c.val) :=
    GeometryB.rootOk_centre c.val c.isLt w hw
  intro f hf
  have hr := compiler_root_bound (3 * leafCount + c.val) hroot f
    (by simpa only [centreSlots] using hf)
  exact hr.trans he

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
