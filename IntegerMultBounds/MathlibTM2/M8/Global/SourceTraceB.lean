module

public import IntegerMultBounds.MathlibTM2.M8.Global.SourceOrderingB
public import IntegerMultBounds.MathlibTM2.M8.Global.BlockTraceB

/-! Exact source-key frame traces, retaining the compiler's repeated frames. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

/-- The occurrences of one leaf in a source-use key, in key order. -/
def sourceUses (us : List Use) (n : Nat) : List Use :=
  us.filter fun u => decide (useNodeB u = n)

def sourceLabels (us : List Use) (n : Nat) : List Signed.Frame :=
  (sourceUses us n).map fun u => AssignmentB.startLabel (useSlotB u)

theorem source_key_trace (us : List Use) (n : Nat) :
    fseq (.inl (.x n)) (opBlocks (us.map sourceOpB) assignment.source).flatten =
      (sourceLabels us n).map frameOfLabel := by
  rw [fseq_opBlocks_x]
  simp [sourceLabels, sourceUses, List.filter_map, List.map_map, Function.comp_def,
    sourceOpB, assignment, Op.target]

/-- All remaining source occurrences belong to the frame-one uncompute. -/
def sourceUncompute (n : Nat) : List LMat :=
  fseq (.inl (.x n))
    (opBlocks (dagB.vNow planB ++ dagB.vLate planB ++ dagB.opsFirst planB ++
      dagB.opsRest planB).reverse (fun _ => 1)).flatten

theorem sourceUncompute_one (n : Nat) :
    ∀ F ∈ sourceUncompute n, F = (1 : LMat) :=
  opBlocks_const_frame _ 1 _

/-- The actual first stage sees the early key, late key, and frame-one uncompute. -/
theorem firstStage_source_label_trace (n : Nat) :
    fseq (.inl (.x n)) firstStage =
      (sourceLabels earlyV n).map frameOfLabel ++
      (sourceLabels lateV n).map frameOfLabel ++ sourceUncompute n := by
  have hearly : fseq (.inl (.x n)) (opBlocks (dagB.vNow planB) assignment.source).flatten =
      (sourceLabels earlyV n).map frameOfLabel := by
    rw [early_sources_materialized]
    exact source_key_trace earlyV n
  have hlate : fseq (.inl (.x n)) (opBlocks (dagB.vLate planB) assignment.source).flatten =
      (sourceLabels lateV n).map frameOfLabel := by
    rw [late_sources_materialized]
    exact source_key_trace lateV n
  exact (stage_source_trace assignment n).trans
    (congrArg₂ List.append (congrArg₂ List.append hearly hlate) rfl)

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
