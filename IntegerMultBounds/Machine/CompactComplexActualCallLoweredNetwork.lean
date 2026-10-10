import IntegerMultBounds.Machine.CompactComplexActualCallFrameEdge

/-! The original finite call schema supplies the complete original lowered
network's factor certificate, rather than an existentially selected replacement
family. This is array semantics and exact instruction counting, not tape execution. -/
namespace IntegerMultBounds.Machine.CompactComplexActualCallLoweredNetwork
noncomputable section
open Networks
open ComplexRecursiveCallSchema (Call Occurrence edge callsAt calls sites)
open CompactComplexActualCallFrameEdge (kernel)
attribute [local irreducible] ComplexRank25.program sites ComplexPhaseBudget.edges

def directions : ComplexFramedExecution.Directions :=
  List.ofFn (fun site : Occurrence => (callsAt site).map kernel)

private theorem original_edges :
    List.ofFn (fun site : Occurrence => (edge site).val)=ComplexPhaseBudget.edges := by
  change List.ofFn (fun site : Fin sites.length => (sites[site.val]).val)=_
  rw [List.ofFn_getElem_eq_map]
  unfold sites
  change ComplexPhaseBudget.edges.attach.map Subtype.val=ComplexPhaseBudget.edges
  simpa only [Function.comp_def,id_eq,List.map_id_fun] using
    (List.attach_map_val (l:=ComplexPhaseBudget.edges) (f:=id))

/-- Every signed direction and factor comes from the same actual call list
used by the recursive controller, in the original edge occurrence order. -/
theorem realizes : ComplexPhaseBudget.Realizes directions := by
  unfold ComplexPhaseBudget.Realizes
  rw [← original_edges]
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp only [directions,List.length_ofFn], ?_⟩
  intro i hi hj
  have hsite : i<sites.length := by simpa only [List.length_ofFn] using hi
  let site : Occurrence := ⟨i,hsite⟩
  simp only [directions,List.get_eq_getElem,List.getElem_ofFn]
  constructor
  · intro g hg
    obtain ⟨call,_hcall,rfl⟩ := List.mem_map.mp hg
    have hs := CompactComplexActualCallFrameEdge.kernel_inverse call
    rw [hs]
    cases call.inverse <;> simp
  · intro columns
    exact CompactComplexActualCallFrameEdge.calls_frame_edge columns site

/-- The exact factor count is the original recursive call count and rank sum. -/
theorem direction_count : (directions.map List.length).sum=ComplexRank25.rankSum := by
  have h : (directions.map List.length).sum=calls.length := by
    simp only [directions,calls,ComplexRecursiveCallSchema.callsFor,
      List.length_flatten,List.map_ofFn,Function.comp_def,List.length_map,callsAt]
  exact h.trans ComplexRecursiveCallSchema.calls_rankSum

/-- All original scalar gates and every dirty scratch incidence remain in
this actual-schema lowering of the named framed network. -/
theorem network_run (columns : ℕ)
    (stored : ComplexFramedExecution.Wire → BinaryColumns.Arrays (25^3) columns) :
    FramedFactorExecution.run (ComplexFramedExecution.lowered columns directions) stored=
      fun i => ComplexFramedExecution.frameOf columns
        (GlobalLabels.sink (Labels.binary 25) ComplexRank25.vector i)
        (ComplexFramedExecution.sign i •
          (ComplexFramedExecution.frameOf columns
            (GlobalLabels.source ComplexRank25.vector (ComplexFramedExecution.route i))).symm
            (stored (ComplexFramedExecution.route i))) :=
  ComplexFramedExecution.lowered_run columns directions realizes stored

theorem factor_count (columns : ℕ) :
    FramedFactorExecution.linearCount (ComplexFramedExecution.lowered columns directions)=
      ComplexRank25.rankSum :=
  (ComplexFramedExecution.lowered_count columns directions realizes).trans direction_count

end
end IntegerMultBounds.Machine.CompactComplexActualCallLoweredNetwork
