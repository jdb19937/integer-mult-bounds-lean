module

public import IntegerMultBounds.Machine.CompactComplexActualEventTrace

/-! Original site blocks and compiler group intervals for the actual events. -/
@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexActualEventNetwork
noncomputable section
open Networks
open CompactComplexCompletedLiveLower
open ComplexRecursiveCallSchema (Call Occurrence callsAt calls sites edge role)
open CompactComplexActualEventTrace
attribute [local irreducible] ComplexRank25.program sites ComplexPhaseBudget.edges ComplexPhaseBudget.updates
  ComplexFramedExecution.frameOf ComplexRank25.wires

abbrev Stored (columns : ℕ) := ComplexFramedExecution.Wire → BinaryColumns.Arrays (25^3) columns

def childInstruction (columns : ℕ) (call : Call) :
    FramedFactorExecution.Instruction ComplexFramedExecution.Wire ℚ (BinaryColumns.Arrays (25^3) columns) :=
  .linear call.role ((BinaryColumns.vectorFactor columns (CompactComplexActualCallFrameEdge.kernel call)).restrictScalars ℚ)

def siteEdge (columns : ℕ) (site : Occurrence) :
    FramedCircuit.Instruction ComplexFramedExecution.Wire ℚ (BinaryColumns.Arrays (25^3) columns) :=
  .edge (role site) (ComplexFramedExecution.frameOf columns (edge site).val.1)
    (ComplexFramedExecution.frameOf columns (edge site).val.2)

private theorem run_named_wire {α ι R E : Type*} [DecidableEq ι] [CommRing R]
    [AddCommGroup E] [Module R E] (wire : ι) (name : α → ι)
    (ops : α → E →ₗ[R] E) (step : α → E → E)
    (cs : List α) (stored : ι → E)
    (hn : ∀ c ∈ cs, name c=wire) (hop : ∀ c x, ops c x=step c x) :
    FramedFactorExecution.run (cs.map (fun c => FramedFactorExecution.Instruction.linear (name c) (ops c))) stored=
      Function.update stored wire (cs.foldl (fun x c => step c x) (stored wire)) := by
  revert hn
  induction cs generalizing stored with
  | nil =>
    intro hn
    simp only [List.map_nil,FramedFactorExecution.run,List.foldl_nil,Function.update_eq_self]
  | cons c cs ih =>
    intro hn
    have hc := hn c (List.mem_cons_self ..)
    have ht : ∀ d ∈ cs, name d=wire := fun d hd => hn d (List.mem_cons_of_mem c hd)
    simp only [List.map_cons,FramedFactorExecution.run,FramedFactorExecution.execute,hc,hop]
    rw [ih _ ht]
    simp only [Function.update_self,Function.update_idem,List.foldl_cons]

private theorem run_named_edge {α ι R E : Type*} [DecidableEq ι] [CommRing R]
    [AddCommGroup E] [Module R E] (wire : ι) (name : α → ι)
    (ops : α → E →ₗ[R] E) (step : α → E → E)
    (cs : List α) (stored : ι → E) (old next : FramedCircuit.Frame R E)
    (hn : ∀ c ∈ cs, name c=wire) (hop : ∀ c x, ops c x=step c x)
    (hfold : ∀ x, cs.foldl (fun x c => step c x) x=next (old.symm x)) :
    FramedFactorExecution.run (cs.map (fun c => FramedFactorExecution.Instruction.linear (name c) (ops c))) stored=
      FramedCircuit.execute (.edge wire old next) stored := by
  rw [run_named_wire wire name ops step cs stored hn hop,hfold]
  rfl

/-- Every literal site's chronological child instructions equal its original
compiler edge on the same physical wire, including all spectator registers. -/
theorem run_site_children (columns : ℕ) (site : Occurrence) (stored : Stored columns) :
    FramedFactorExecution.run ((callsAt site).map (childInstruction columns)) stored=
      FramedCircuit.execute (siteEdge columns site) stored :=
  run_named_edge (role site) Call.role
    (fun call => (BinaryColumns.vectorFactor columns (CompactComplexActualCallFrameEdge.kernel call)).restrictScalars ℚ)
    (fun call => BinaryColumns.vectorFactor columns (CompactComplexActualCallFrameEdge.kernel call))
    (callsAt site) stored
    (ComplexFramedExecution.frameOf columns (edge site).val.1)
    (ComplexFramedExecution.frameOf columns (edge site).val.2)
    (fun call hc => congrArg role (ComplexRecursiveCallSchema.callsAt_site site call hc))
    (fun _ _ => rfl) (CompactComplexActualCallOrder.calls_frame_edge site)

private theorem run_blocks {α β ι R E : Type*} [DecidableEq ι] [CommRing R]
    [AddCommGroup E] [Module R E] (children : α → List β)
    (instruction : β → FramedFactorExecution.Instruction ι R E)
    (edgeInstruction : α → FramedCircuit.Instruction ι R E)
    (hrun : ∀ a stored, FramedFactorExecution.run ((children a).map instruction) stored=
      FramedCircuit.execute (edgeInstruction a) stored)
    (ss : List α) (stored : ι → E) :
    FramedFactorExecution.run ((ss.flatMap children).map instruction) stored=
      FramedCircuit.run (ss.map edgeInstruction) stored := by
  induction ss generalizing stored with
  | nil => rfl
  | cons site ss ih =>
    simp only [List.flatMap_cons,List.map_append,List.map_cons,FramedFactorExecution.run_append,
      hrun,FramedCircuit.run,ih]

/-- Expanding a consecutive original site list into all of its literal child
calls preserves the original compiler's edge action in that same order. -/
theorem run_site_blocks (columns : ℕ) (ss : List Occurrence) (stored : Stored columns) :
    FramedFactorExecution.run ((ss.flatMap callsAt).map (childInstruction columns)) stored=
      FramedCircuit.run (ss.map (siteEdge columns)) stored :=
  run_blocks callsAt (childInstruction columns) (siteEdge columns) (run_site_children columns) ss stored

private theorem ofFn_named {α : Type*} {n : ℕ} (f : Fin n → α) :
    List.ofFn f=(List.ofFn id).map f := by
  simp only [List.map_ofFn,Function.comp_def,id_eq]

def siteNames : List Occurrence := List.ofFn id

theorem siteCalls_names : siteCalls=siteNames.map callsAt := ofFn_named callsAt

def groupSites (g : CompactComplexScalarIntegerRows.GroupIndex) : List Occurrence :=
  (siteNames.drop (siteBoundary g.val)).take
    (GroupedFrames.touches (CompactFramedScalarGrid.vertex g)).length

theorem callInterval_named_sites (g : CompactComplexScalarIntegerRows.GroupIndex) :
    callInterval g=(groupSites g).flatMap callsAt := by
  rw [callInterval_sites,siteCalls_names,←List.map_drop,←List.map_take]
  rfl

/-- Consume exactly the actual group's factor prefix before its named scalar
block; this action is the original compiler's ordered site-edge action. -/
theorem run_callInterval_sites (columns : ℕ) (g : CompactComplexScalarIntegerRows.GroupIndex)
    (stored : Stored columns) :
    FramedFactorExecution.run ((callInterval g).map (childInstruction columns)) stored=
      FramedCircuit.run ((groupSites g).map (siteEdge columns)) stored := by
  rw [callInterval_named_sites,run_site_blocks]

/-- The compiler prefix counts original edge occurrences, rather than gates
or a new event numbering. -/
theorem prefix_site_count (columns g : ℕ) :
    (wireFrames (CompactComplexActualScalarNetworkPrefix.networkPrefix columns g)).length=
      siteBoundary g := by
  unfold CompactComplexActualScalarNetworkPrefix.networkPrefix siteBoundary
  rw [wireFrames_compile,traceFrames_length]

theorem alignment_site_count (columns : ℕ) (g : CompactComplexScalarIntegerRows.GroupIndex) :
    (wireFrames (CompactComplexActualScalarNetworkPrefix.alignment columns g)).length=
      (GroupedFrames.touches (CompactFramedScalarGrid.vertex g)).length := by
  unfold CompactComplexActualScalarNetworkPrefix.alignment
  have he := wireFrames_edges (ComplexFramedExecution.frameOf columns)
    (CompactComplexActualScalarNetworkPrefix.labels g.val)
    (fun _ => (CompactFramedScalarGrid.vertex g).label)
    (GroupedCircuit.touched (CompactFramedScalarGrid.vertex g).group)
  change wireFrames (FramedCircuit.edges _ (fun _ => ComplexFramedExecution.frameOf columns
    (CompactFramedScalarGrid.vertex g).label) _)=_ at he
  rw [he,traceFrames_length]
  simp only [GroupedFrames.touches,List.length_map]

private theorem take_drop_middle {α : Type*} (xs ys zs : List α) :
    ((xs++ys++zs).drop xs.length).take ys.length=ys := by
  rw [List.append_assoc,List.drop_left,List.take_left]

/-- The site's original edge-count interval is exactly the original group's
compiler alignment, before any of that group's scalar gate instructions. -/
theorem original_group_frames (columns : ℕ) (g : CompactComplexScalarIntegerRows.GroupIndex) :
    ((wireFrames (ComplexFramedExecution.network columns)).drop (siteBoundary g.val)).take
      (GroupedFrames.touches (CompactFramedScalarGrid.vertex g)).length=
      wireFrames (CompactComplexActualScalarNetworkPrefix.alignment columns g) := by
  have hn := CompactComplexActualScalarNetworkPrefix.original_network_split columns (g.val+1)
  rw [CompactComplexActualScalarNetworkPrefix.prefix_step] at hn
  have hf := congrArg wireFrames hn
  simp only [wireFrames_append,wireFrames_gates,List.append_nil] at hf
  rw [hf,←prefix_site_count columns g.val,←alignment_site_count columns g]
  exact take_drop_middle _ _ _

private theorem siteNames_raw :
    siteNames.map (fun site => (role site,(edge site).val))=
      List.ofFn (fun site : Occurrence => (role site,(edge site).val)) :=
  (ofFn_named (fun site : Occurrence => (role site,(edge site).val))).symm

private theorem slice_mapped_trace {α β γ : Type*} (names : List α) (raw : List β)
    (frames : List γ) (f : α → β) (g : β → γ) (start len : ℕ)
    (hraw : names.map f=raw) (hframes : raw.map g=frames) :
    (((names.drop start).take len).map f).map g=(frames.drop start).take len := by
  rw [List.map_take,List.map_drop,List.map_take,List.map_drop,hraw,hframes]

private theorem groupSites_frames (columns : ℕ) (g : CompactComplexScalarIntegerRows.GroupIndex) :
    (((groupSites g).map (fun site => (role site,(edge site).val))).map
      (fun p => (p.1,ComplexFramedExecution.frameOf columns p.2.1,
        ComplexFramedExecution.frameOf columns p.2.2)))=
      wireFrames (CompactComplexActualScalarNetworkPrefix.alignment columns g) :=
  (slice_mapped_trace siteNames _ _ (fun site => (role site,(edge site).val))
    (fun p => (p.1,ComplexFramedExecution.frameOf columns p.2.1,
      ComplexFramedExecution.frameOf columns p.2.2)) (siteBoundary g.val)
    (GroupedFrames.touches (CompactFramedScalarGrid.vertex g)).length
    siteNames_raw (actual_site_wireFrames columns)).trans (original_group_frames columns g)

section Plain
variable {ι E : Type*} [DecidableEq ι]
def plainApply (a : ι × (E ≃ E) × (E ≃ E)) (stored : ι → E) : ι → E :=
  Function.update stored a.1 (a.2.2 (a.2.1.symm (stored a.1)))
end Plain

attribute [local irreducible] role edge
private theorem execute_site_plain (columns : ℕ) (site : Occurrence) (stored : Stored columns) :
    FramedCircuit.execute (siteEdge columns site) stored=
      plainApply (role site,(ComplexFramedExecution.frameOf columns (edge site).val.1).toEquiv,
        (ComplexFramedExecution.frameOf columns (edge site).val.2).toEquiv) stored := by
  rfl


private theorem run_map_step {α ι R E : Type*} [DecidableEq ι] [CommRing R]
    [AddCommGroup E] [Module R E] (instruction : α → FramedCircuit.Instruction ι R E)
    (step : α → (ι → E) → (ι → E))
    (hi : ∀ a s, FramedCircuit.execute (instruction a) s=step a s)
    (ss : List α) (stored : ι → E) :
    FramedCircuit.run (ss.map instruction) stored=ss.foldl (fun s a => step a s) stored := by
  induction ss generalizing stored with
  | nil => rfl
  | cons a ss ih =>
    simp only [List.map_cons,FramedCircuit.run,List.foldl_cons,hi]
    exact ih _

private def sitePlainStep (columns : ℕ) (site : Occurrence) (stored : Stored columns) : Stored columns :=
  plainApply (role site,(ComplexFramedExecution.frameOf columns (edge site).val.1).toEquiv,
    (ComplexFramedExecution.frameOf columns (edge site).val.2).toEquiv) stored

private theorem execute_site_step (columns : ℕ) (site : Occurrence) (stored : Stored columns) :
    FramedCircuit.execute (siteEdge columns site) stored=sitePlainStep columns site stored :=
  execute_site_plain columns site stored

attribute [local irreducible] sitePlainStep siteEdge
private theorem run_sites_step (columns : ℕ) (ss : List Occurrence) (stored : Stored columns) :
    FramedCircuit.run (ss.map (siteEdge columns)) stored=
      ss.foldl (fun s site => sitePlainStep columns site s) stored :=
  run_map_step (siteEdge columns) (sitePlainStep columns) (execute_site_step columns) ss stored

private theorem fold_named_steps {α β ι E : Type*} [DecidableEq ι]
    (raw : α → β) (annotate : β → ι × (E ≃ E) × (E ≃ E))
    (step : α → (ι → E) → (ι → E))
    (hstep : ∀ a s, step a s=plainApply (annotate (raw a)) s)
    (ss : List α) (stored : ι → E) :
    ss.foldl (fun s a => step a s) stored=
      ((ss.map raw).map annotate).foldl (fun s a => plainApply a s) stored := by
  induction ss generalizing stored with
  | nil => rfl
  | cons a ss ih =>
    simp only [List.foldl_cons,List.map_cons]
    rw [hstep a stored]
    exact ih _

private theorem site_step_annotation (columns : ℕ) (site : Occurrence) (stored : Stored columns) :
    sitePlainStep columns site stored=
      plainApply (role site,(ComplexFramedExecution.frameOf columns (edge site).val.1).toEquiv,
        (ComplexFramedExecution.frameOf columns (edge site).val.2).toEquiv) stored := by
  unfold sitePlainStep
  rfl


private def rawSite (site : Occurrence) : ComplexFramedExecution.Wire × ComplexPhaseBudget.Label × ComplexPhaseBudget.Label :=
  (role site,(edge site).val)
private def plainAnnotation (columns : ℕ)
    (p : ComplexFramedExecution.Wire × ComplexPhaseBudget.Label × ComplexPhaseBudget.Label) :
    ComplexFramedExecution.Wire × (BinaryColumns.Arrays (25^3) columns ≃ BinaryColumns.Arrays (25^3) columns) ×
      (BinaryColumns.Arrays (25^3) columns ≃ BinaryColumns.Arrays (25^3) columns) :=
  (p.1,(ComplexFramedExecution.frameOf columns p.2.1).toEquiv,
    (ComplexFramedExecution.frameOf columns p.2.2).toEquiv)
private theorem plainAnnotation_pair (columns : ℕ) (wire : ComplexFramedExecution.Wire)
    (labels : ComplexPhaseBudget.Label × ComplexPhaseBudget.Label) :
    plainAnnotation columns (wire,labels)=
      (wire,(ComplexFramedExecution.frameOf columns labels.1).toEquiv,
        (ComplexFramedExecution.frameOf columns labels.2).toEquiv) := by
  unfold plainAnnotation
  rfl
private theorem rawSite_def (site : Occurrence) : rawSite site=(role site,(edge site).val) := rfl
attribute [local irreducible] plainAnnotation rawSite
private theorem step_named_annotation (columns : ℕ) (site : Occurrence) (stored : Stored columns) :
    sitePlainStep columns site stored=plainApply (plainAnnotation columns (rawSite site)) stored := by
  rw [site_step_annotation,rawSite_def,plainAnnotation_pair]
private theorem run_sites_named_annotations (columns : ℕ) (ss : List Occurrence) (stored : Stored columns) :
    FramedCircuit.run (ss.map (siteEdge columns)) stored=
      ((ss.map rawSite).map (plainAnnotation columns)).foldl (fun s a => plainApply a s) stored :=
  (run_sites_step columns ss stored).trans
    (fold_named_steps rawSite (plainAnnotation columns) (sitePlainStep columns)
      (step_named_annotation columns) ss stored)
/-- Forget only the linear-structure witnesses; retain the literal wire and
both executable frame bijections in their original order. -/
private def forgetFrames {ι R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    (a : ι × FramedCircuit.Frame R E × FramedCircuit.Frame R E) :
    ι × (E ≃ E) × (E ≃ E) :=
  (a.1,a.2.1.toEquiv,a.2.2.toEquiv)

/-- Edge-list execution is exactly the chronological fold of its ordinary
bijections. The induction retains the updated frame profile at every step. -/
private theorem run_edges_plain {ι R E : Type*} [DecidableEq ι] [CommRing R]
    [AddCommGroup E] [Module R E]
    (current desired : ι → FramedCircuit.Frame R E) (wires : List ι)
    (stored : ι → E) :
    FramedCircuit.run (FramedCircuit.edges current desired wires) stored=
      ((wireFrames (FramedCircuit.edges current desired wires)).map forgetFrames).foldl
        (fun s a => plainApply a s) stored := by
  induction wires generalizing current stored with
  | nil => rfl
  | cons i wires ih =>
    simp only [FramedCircuit.edges,FramedCircuit.run,wireFrames,List.map_cons,List.foldl_cons]
    exact ih (Function.update current i (desired i))
      (Function.update stored i (desired i ((current i).symm (stored i))))



private def frameAnnotation (columns : ℕ)
    (p : ComplexFramedExecution.Wire × ComplexPhaseBudget.Label × ComplexPhaseBudget.Label) :=
  (p.1,ComplexFramedExecution.frameOf columns p.2.1,
    ComplexFramedExecution.frameOf columns p.2.2)
private theorem rawSite_fun : rawSite=(fun site => (role site,(edge site).val)) := by
  funext site
  exact rawSite_def site
private theorem frameAnnotation_fun (columns : ℕ) : frameAnnotation columns=
    (fun p => (p.1,ComplexFramedExecution.frameOf columns p.2.1,
      ComplexFramedExecution.frameOf columns p.2.2)) := rfl
attribute [local irreducible] frameAnnotation

private theorem map_frame_forget (columns : ℕ)
    (xs : List (ComplexFramedExecution.Wire × ComplexPhaseBudget.Label × ComplexPhaseBudget.Label)) :
    (xs.map (frameAnnotation columns)).map forgetFrames=xs.map (plainAnnotation columns) := by
  rw [List.map_map]
  apply congrArg (fun f => xs.map f)
  funext p
  delta frameAnnotation plainAnnotation forgetFrames
  rfl

private theorem groupSites_named_frames (columns : ℕ)
    (g : CompactComplexScalarIntegerRows.GroupIndex) :
    ((groupSites g).map rawSite).map (frameAnnotation columns)=
      wireFrames (CompactComplexActualScalarNetworkPrefix.alignment columns g) := by
  rw [rawSite_fun,frameAnnotation_fun]
  exact groupSites_frames columns g

private theorem groupSites_named_plain (columns : ℕ)
    (g : CompactComplexScalarIntegerRows.GroupIndex) :
    ((groupSites g).map rawSite).map (plainAnnotation columns)=
      (wireFrames (CompactComplexActualScalarNetworkPrefix.alignment columns g)).map forgetFrames := by
  have h := congrArg (List.map (forgetFrames (R:=ℚ))) (groupSites_named_frames columns g)
  rw [map_frame_forget] at h
  exact h

private theorem run_groupSites_alignment_named (columns : ℕ)
    (g : CompactComplexScalarIntegerRows.GroupIndex) (stored : Stored columns) :
    FramedCircuit.run ((groupSites g).map (siteEdge columns)) stored=
      FramedCircuit.run (CompactComplexActualScalarNetworkPrefix.alignment columns g) stored := by
  rw [run_sites_named_annotations,groupSites_named_plain]
  unfold CompactComplexActualScalarNetworkPrefix.alignment
  exact (run_edges_plain _ _ _ stored).symm

def terminalSites : List Occurrence := siteNames.drop (siteBoundary ComplexRank25.program.length)

private theorem original_terminal_frames (columns : ℕ) :
    (wireFrames (ComplexFramedExecution.network columns)).drop
      (siteBoundary ComplexRank25.program.length)=
      wireFrames (CompactComplexActualScalarNetworkPrefix.networkTail columns ComplexRank25.program.length) := by
  have h := congrArg wireFrames (CompactComplexActualScalarNetworkPrefix.original_network_split
    columns ComplexRank25.program.length)
  rw [wireFrames_append] at h
  rw [h,←prefix_site_count columns ComplexRank25.program.length,List.drop_left]

private theorem terminalSites_named_frames (columns : ℕ) :
    (terminalSites.map rawSite).map (frameAnnotation columns)=
      wireFrames (CompactComplexActualScalarNetworkPrefix.networkTail columns ComplexRank25.program.length) := by
  rw [rawSite_fun,frameAnnotation_fun]
  unfold terminalSites
  rw [List.map_drop,List.map_drop,siteNames_raw,actual_site_wireFrames,original_terminal_frames]

private theorem terminalSites_named_plain (columns : ℕ) :
    (terminalSites.map rawSite).map (plainAnnotation columns)=
      (wireFrames (CompactComplexActualScalarNetworkPrefix.networkTail columns ComplexRank25.program.length)).map
        forgetFrames := by
  have h := congrArg (List.map (forgetFrames (R:=ℚ))) (terminalSites_named_frames columns)
  rw [map_frame_forget] at h
  exact h

private theorem run_sites_edge_program (columns : ℕ) (ss : List Occurrence)
    (p : List (FramedCircuit.Instruction ComplexFramedExecution.Wire ℚ (BinaryColumns.Arrays (25^3) columns)))
    (current desired : ComplexFramedExecution.Wire → FramedCircuit.Frame ℚ (BinaryColumns.Arrays (25^3) columns))
    (wires : List ComplexFramedExecution.Wire)
    (hp : p=FramedCircuit.edges current desired wires)
    (hf : (ss.map rawSite).map (plainAnnotation columns)=(wireFrames p).map forgetFrames)
    (stored : Stored columns) :
    FramedCircuit.run (ss.map (siteEdge columns)) stored=FramedCircuit.run p stored := by
  rw [run_sites_named_annotations,hf,hp]
  exact (run_edges_plain current desired wires stored).symm

private theorem compile_drop_end_edges {ι L R E : Type*} [DecidableEq ι] [CommRing R] [DecidableEq R]
    [AddCommGroup E] [Module R E] (frameOf : L → FramedCircuit.Frame R E)
    (current : ι → L) (p : List (GroupedFrames.Vertex ι L R))
    (old next : ι → FramedCircuit.Frame R E) (wires : List ι) :
    GroupedModuleFrames.compile frameOf current (p.drop p.length)++FramedCircuit.edges old next wires=
      FramedCircuit.edges old next wires := by
  rw [List.drop_length]
  rfl

private theorem terminal_tail_edges (columns : ℕ) :
    CompactComplexActualScalarNetworkPrefix.networkTail columns ComplexRank25.program.length=
      FramedCircuit.edges
        (GroupedModuleFrames.profile (ComplexFramedExecution.frameOf columns)
          (GroupedFrames.finalLabels CompactComplexActualScalarNetworkPrefix.inputLabels ComplexRank25.program))
        (GroupedModuleFrames.profile (ComplexFramedExecution.frameOf columns)
          (GlobalLabels.sink (Labels.binary 25) ComplexRank25.vector)) ComplexRank25.wires :=
  compile_drop_end_edges (ComplexFramedExecution.frameOf columns)
    (CompactComplexActualScalarNetworkPrefix.labels ComplexRank25.program.length)
    ComplexRank25.program _ _ ComplexRank25.wires

private theorem run_terminalSites_sink_named (columns : ℕ) (stored : Stored columns) :
    FramedCircuit.run (terminalSites.map (siteEdge columns)) stored=
      FramedCircuit.run (CompactComplexActualScalarNetworkPrefix.networkTail columns ComplexRank25.program.length)
        stored :=
  run_sites_edge_program columns terminalSites
    (CompactComplexActualScalarNetworkPrefix.networkTail columns ComplexRank25.program.length)
    _ _ ComplexRank25.wires (terminal_tail_edges columns) (terminalSites_named_plain columns) stored


/-- Every actual group's chronological child calls execute its original
compiler alignment, including all spectator registers. -/
theorem run_callInterval_alignment (columns : ℕ)
    (g : CompactComplexScalarIntegerRows.GroupIndex) (stored : Stored columns) :
    FramedFactorExecution.run ((callInterval g).map (childInstruction columns)) stored=
      FramedCircuit.run (CompactComplexActualScalarNetworkPrefix.alignment columns g) stored := by
  rw [run_callInterval_sites,run_groupSites_alignment_named]

private theorem terminalCalls_named_sites :
    calls.drop (callBoundary ComplexRank25.program.length)=terminalSites.flatMap callsAt := by
  rw [calls_drop_boundary,siteCalls_names,←List.map_drop]
  rfl

/-- Every terminal child call executes the original compiler's sink suffix. -/
theorem run_terminalCalls_sink (columns : ℕ) (stored : Stored columns) :
    FramedFactorExecution.run ((calls.drop (callBoundary ComplexRank25.program.length)).map
      (childInstruction columns)) stored=
      FramedCircuit.run (CompactComplexActualScalarNetworkPrefix.networkTail columns ComplexRank25.program.length)
        stored := by
  rw [terminalCalls_named_sites,run_site_blocks,run_terminalSites_sink_named]

end
end IntegerMultBounds.Machine.CompactComplexActualEventNetwork
