module

public import IntegerMultBounds.Machine.CompactComplexCompletedLiveLower
public import IntegerMultBounds.Machine.CompactComplexActualCallOrder
public import IntegerMultBounds.Machine.CompactComplexActualCallLoweredNetwork
public import IntegerMultBounds.Machine.CompactComplexActualScalarNetworkPrefix

/-! Literal group boundaries split the actual site-major call schedule.
Ordered compiler edge annotations retain both frames and the physical wire. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexActualEventTrace
noncomputable section
open Networks
open CompactComplexCompletedLiveLower
open ComplexRecursiveCallSchema (Call Occurrence callsAt calls sites edge role)
attribute [local irreducible] ComplexRank25.program sites ComplexPhaseBudget.edges ComplexPhaseBudget.updates
  ComplexFramedExecution.frameOf ComplexRank25.wires

/-- Flattening complete site prefixes consumes exactly their sum of lengths. -/
theorem flatten_take_lengths {α : Type*} (xss : List (List α)) (n : ℕ) :
    xss.flatten.take ((xss.take n).map List.length).sum=(xss.take n).flatten := by
  have h := List.take_append_drop n xss
  have hf := congrArg List.flatten h
  rw [List.flatten_append] at hf
  rw [←hf,←List.length_flatten,List.take_left]

theorem flatten_drop_lengths {α : Type*} (xss : List (List α)) (n : ℕ) :
    xss.flatten.drop ((xss.take n).map List.length).sum=(xss.drop n).flatten := by
  have h := List.take_append_drop n xss
  have hf := congrArg List.flatten h
  rw [List.flatten_append] at hf
  rw [←hf,←List.length_flatten,List.drop_left]

def siteCalls : List (List Call) := List.ofFn callsAt

theorem siteCalls_lengths : siteCalls.map List.length=CompactRecursiveDependencyBudget.siteDimensions := by
  simp only [siteCalls,CompactRecursiveDependencyBudget.siteDimensions,List.map_ofFn]
  exact congrArg List.ofFn (funext ComplexRecursiveCallSchema.callsAt_length)

theorem calls_drop_boundary (g : ℕ) :
    calls.drop (callBoundary g)=(siteCalls.drop (siteBoundary g)).flatten := by
  have h := flatten_drop_lengths siteCalls (siteBoundary g)
  rw [List.map_take,siteCalls_lengths] at h
  exact h

/-- Actual group call intervals consist of exactly their original edge
occurrences, with every coordinate retained in its original increasing order. -/
theorem callInterval_sites (g : CompactComplexScalarIntegerRows.GroupIndex) :
    callInterval g=((siteCalls.drop (siteBoundary g.val)).take
      (GroupedFrames.touches (CompactFramedScalarGrid.vertex g)).length).flatten := by
  unfold callInterval
  rw [calls_drop_boundary]
  have h := flatten_take_lengths (siteCalls.drop (siteBoundary g.val))
    (GroupedFrames.touches (CompactFramedScalarGrid.vertex g)).length
  rw [List.map_take,List.map_drop,siteCalls_lengths] at h
  exact h

section CompilerTrace
variable {ι L R E : Type*} [DecidableEq ι] [CommRing R] [DecidableEq R]
  [AddCommGroup E] [Module R E]

/-- Original compiler edge extraction preserving its actual physical wire. -/
def wireFrames : List (FramedCircuit.Instruction ι R E) →
    List (ι × FramedCircuit.Frame R E × FramedCircuit.Frame R E)
  | [] => []
  | .edge i old next::rest => (i,old,next)::wireFrames rest
  | .gate _::rest => wireFrames rest

/-- The same annotation on the original sequential label-update trace. -/
def traceFrames (frameOf : L → FramedCircuit.Frame R E) (current : ι → L) :
    List (ι × L) → List (ι × FramedCircuit.Frame R E × FramedCircuit.Frame R E)
  | [] => []
  | (i,next)::rest => (i,frameOf (current i),frameOf next)::
      traceFrames frameOf (Function.update current i next) rest

omit [DecidableEq ι] [DecidableEq R] in
@[simp] theorem wireFrames_append (p q : List (FramedCircuit.Instruction ι R E)) :
    wireFrames (p++q)=wireFrames p++wireFrames q := by
  induction p with
  | nil => rfl
  | cons instr p ih => cases instr <;> simp only [wireFrames,List.cons_append,ih]

omit [DecidableEq ι] [DecidableEq R] in
@[simp] theorem wireFrames_gates (gs : Circuit.Program ι R) :
    wireFrames (gs.map (FramedCircuit.Instruction.gate (E:=E)))=[] := by
  induction gs with
  | nil => rfl
  | cons g gs ih => exact ih

omit [DecidableEq R] in
theorem traceFrames_append (frameOf : L → FramedCircuit.Frame R E)
    (current : ι → L) (xs ys : List (ι × L)) :
    traceFrames frameOf current (xs++ys)=traceFrames frameOf current xs++
      traceFrames frameOf (RankTrace.finish current xs) ys := by
  induction xs generalizing current with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append,traceFrames,RankTrace.finish,ih]

omit [DecidableEq R] in
theorem wireFrames_edges (frameOf : L → FramedCircuit.Frame R E)
    (current desired : ι → L) (wires : List ι) :
    wireFrames (FramedCircuit.edges (GroupedModuleFrames.profile frameOf current)
      (GroupedModuleFrames.profile frameOf desired) wires)=
      traceFrames frameOf current (wires.map (fun i => (i,desired i))) := by
  induction wires generalizing current with
  | nil => rfl
  | cons i wires ih =>
    simp only [FramedCircuit.edges,wireFrames,List.map_cons,traceFrames]
    change (i,frameOf (current i),frameOf (desired i))::
      wireFrames (FramedCircuit.edges
        (Function.update (GroupedModuleFrames.profile frameOf current) i (frameOf (desired i)))
        (GroupedModuleFrames.profile frameOf desired) wires)=_
    rw [GroupedModuleFrames.profile_update,ih]

theorem wireFrames_compile (frameOf : L → FramedCircuit.Frame R E)
    (current : ι → L) (vs : List (GroupedFrames.Vertex ι L R)) :
    wireFrames (GroupedModuleFrames.compile frameOf current vs)=
      traceFrames frameOf current (GroupedFrames.updates vs) := by
  induction vs generalizing current with
  | nil => rfl
  | cons v vs ih =>
    rw [GroupedModuleFrames.compile,wireFrames_append,GroupedCircuit.compileFramed,
      wireFrames_append,wireFrames_gates,List.append_nil,ih]
    have he := wireFrames_edges frameOf current (fun _ => v.label) (GroupedCircuit.touched v.group)
    change wireFrames (FramedCircuit.edges (GroupedModuleFrames.profile frameOf current)
      (fun _ => frameOf v.label) (GroupedCircuit.touched v.group))=_ at he
    rw [he]
    simp only [GroupedFrames.updates,List.flatMap_cons,traceFrames_append,GroupedFrames.after,
      GroupedFrames.touches]

theorem wireFrames_network (frameOf : L → FramedCircuit.Frame R E)
    (wires : List ι) (input output : ι → L) (vs : List (GroupedFrames.Vertex ι L R)) :
    wireFrames (GroupedModuleFrames.network frameOf wires input output vs)=
      traceFrames frameOf input (GroupedFrames.networkUpdates wires output vs) := by
  rw [GroupedModuleFrames.network,wireFrames_append,wireFrames_compile,wireFrames_edges,
    GroupedFrames.networkUpdates,traceFrames_append,GroupedFrames.finalLabels_trace]

omit [DecidableEq R] in
theorem traceFrames_zip (frameOf : L → FramedCircuit.Frame R E)
    (current : ι → L) (us : List (ι × L)) :
    traceFrames frameOf current us=(us.zip (RankTrace.edges current us)).map
      (fun p => (p.1.1,frameOf p.2.1,frameOf p.2.2)) := by
  induction us generalizing current with
  | nil => rfl
  | cons u us ih => simp only [traceFrames,RankTrace.edges,List.zip_cons_cons,List.map_cons,ih]


omit [DecidableEq R] in
theorem traceFrames_length (frameOf : L → FramedCircuit.Frame R E)
    (current : ι → L) (us : List (ι × L)) :
    (traceFrames frameOf current us).length=us.length := by
  induction us generalizing current with
  | nil => rfl
  | cons u us ih => simp only [traceFrames,List.length_cons,ih]

def originalEdge (t : ι × FramedCircuit.Frame R E × FramedCircuit.Frame R E) :
    FramedCircuit.Instruction ι R E := .edge t.1 t.2.1 t.2.2

omit [DecidableEq R] in
theorem reconstruct_edges (current desired : ι → FramedCircuit.Frame R E) (wires : List ι) :
    (wireFrames (FramedCircuit.edges current desired wires)).map originalEdge=
      FramedCircuit.edges current desired wires := by
  induction wires generalizing current with
  | nil => rfl
  | cons i wires ih =>
    simp only [FramedCircuit.edges,wireFrames,List.map_cons,ih]
    rfl

end CompilerTrace


private theorem indexedMap {α β : Type*} (xs : List α) (n : ℕ) (h : n=xs.length)
    (bound : ∀ i : Fin n,i.val<xs.length) (f : α → β) :
    List.ofFn (fun i : Fin n => f (xs[i.val]'(bound i)))=xs.map f := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_map,h]
  · intro i hi hj
    simp only [List.getElem_ofFn,List.getElem_map]

private theorem zip_ofFn {α β : Type*} {n : ℕ} (f : Fin n → α) (g : Fin n → β) :
    (List.ofFn f).zip (List.ofFn g)=List.ofFn (fun i => (f i,g i)) := by
  apply List.ext_getElem
  · simp only [List.length_zip,List.length_ofFn,Nat.min_self]
  · intro i hi hj
    simp only [List.getElem_zip,List.getElem_ofFn]

private theorem zip_project {ι L β : Type*} (us : List (ι × L)) (es : List β) :
    (us.map Prod.fst).zip es=(us.zip es).map (fun p => (p.1.1,p.2)) := by
  induction us generalizing es with
  | nil => rfl
  | cons u us ih =>
    cases es with
    | nil => rfl
    | cons e es => simp only [List.map_cons,List.zip_cons_cons,ih]

theorem actual_site_roles : List.ofFn role=ComplexPhaseBudget.updates.map Prod.fst := by
  let bound : ∀site : Occurrence,site.val<ComplexPhaseBudget.updates.length := fun site => by
    have hi:=site.isLt
    simpa only [sites,List.length_attach,ComplexRecursiveCallSchema.edge_length] using hi
  have hr : role=(fun site : Occurrence => (ComplexPhaseBudget.updates[site.val]'(bound site)).1) := rfl
  have hl : sites.length=ComplexPhaseBudget.updates.length := by
    simp only [sites,List.length_attach,ComplexRecursiveCallSchema.edge_length]
  exact (congrArg List.ofFn hr).trans (indexedMap _ _ hl bound Prod.fst)

theorem actual_site_edges : List.ofFn (fun site : Occurrence => (edge site).val)=ComplexPhaseBudget.edges :=
  CompactComplexActualCallLoweredNetwork.original_edges

/-- Raw site annotations retain the literal role and ordered label pair. -/
theorem actual_site_trace :
    List.ofFn (fun site : Occurrence => (role site,(edge site).val))=
      (ComplexPhaseBudget.updates.zip ComplexPhaseBudget.edges).map (fun p => (p.1.1,p.2)) := by
  exact (zip_ofFn role (fun site : Occurrence => (edge site).val)).symm.trans
    ((congrArg₂ List.zip actual_site_roles actual_site_edges).trans
      (zip_project ComplexPhaseBudget.updates ComplexPhaseBudget.edges))

private theorem map_site_annotations {ι L β : Type*} {n : ℕ}
    (wire : Fin n → ι) (labels : Fin n → L × L)
    (us : List (ι × L)) (es : List (L × L)) (f : L → β)
    (h : List.ofFn (fun i => (wire i,labels i))=
      (us.zip es).map (fun p => (p.1.1,p.2))) :
    List.ofFn (fun i => (wire i,f (labels i).1,f (labels i).2))=
      (us.zip es).map (fun p => (p.1.1,f p.2.1,f p.2.2)) := by
  have hm := congrArg (List.map (fun p : ι × L × L => (p.1,f p.2.1,f p.2.2))) h
  simpa only [List.map_ofFn,List.map_map,Function.comp_def] using hm

private theorem actual_mapped_annotations {β : Type*} (f : ComplexPhaseBudget.Label → β) :
    (List.ofFn (fun site : Occurrence => (role site,(edge site).val))).map
      (fun p => (p.1,f p.2.1,f p.2.2))=
    ((ComplexPhaseBudget.updates.zip ComplexPhaseBudget.edges).map (fun p => (p.1.1,p.2))).map
      (fun p => (p.1,f p.2.1,f p.2.2)) :=
  congrArg (List.map (fun p => (p.1,f p.2.1,f p.2.2))) actual_site_trace


/-- Every actual site retains the wire and both frames of the corresponding
original compiler edge, including all terminal sink incidences. -/
theorem actual_site_wireFrames (columns : ℕ) :
    (List.ofFn (fun site : Occurrence => (role site,(edge site).val))).map
      (fun p => (p.1,ComplexFramedExecution.frameOf columns p.2.1,
        ComplexFramedExecution.frameOf columns p.2.2))=
      wireFrames (ComplexFramedExecution.network columns) := by
  have he : RankTrace.edges (GlobalLabels.source ComplexRank25.vector) ComplexPhaseBudget.updates=
      ComplexPhaseBudget.edges := by
    unfold ComplexPhaseBudget.edges
    rfl
  have hs := actual_mapped_annotations (ComplexFramedExecution.frameOf columns)
  simp only [List.map_map,Function.comp_def] at hs
  have ht := traceFrames_zip (ComplexFramedExecution.frameOf columns)
    (GlobalLabels.source ComplexRank25.vector) ComplexPhaseBudget.updates
  rw [he] at ht
  have hw : wireFrames (ComplexFramedExecution.network columns)=
      traceFrames (ComplexFramedExecution.frameOf columns)
        (GlobalLabels.source ComplexRank25.vector) ComplexPhaseBudget.updates := by
    rw [ComplexFramedExecution.network,wireFrames_network,←actual_update_schedule]
  exact hs.trans (ht.symm.trans hw.symm)

end
end IntegerMultBounds.Machine.CompactComplexActualEventTrace
