module

public import IntegerMultBounds.MathlibTM2.M8.Global.DesignB
public import IntegerMultBounds.MathlibTM2.M8.Global.StageFrames
public import IntegerMultBounds.MathlibTM2.M8.Local.FrameFlowB

/-! Connect per-operation frame flow to the actual framed design-B gates.
Internal serving advances the pivot through its copy frames; V-leaf serving
preserves the kept source frame. Newly copied slots receive their own starts. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

def opFrame (op : Op) : LMat := if op.isSrc then assignment.source op else assignment.side op

theorem opFrame_copy (p s n : Nat) :
    opFrame (.copy p s n) = frameOfLabel (AssignmentB.startLabel s) := rfl

theorem opFrame_src (s n : Nat) :
    opFrame (.src s n) = frameOfLabel (AssignmentB.startLabel s) := rfl

theorem opFrame_add (p o n : Nat) :
    opFrame (.add p o n) = frameOfLabel (AssignmentB.nodeLabel n) := rfl

theorem after_add_frame (ops : List Op) (p o n : Nat) :
    FrameFlow.last opFrame ((ops ++ [Op.add p o n]).map dagB.vop) p =
      some (frameOfLabel (AssignmentB.nodeLabel n)) := by
  simp [Dag.vop, FrameFlow.last_append_single, Op.slots, opFrame_add]

theorem after_add_other_frame (ops : List Op) (p o n : Nat) :
    FrameFlow.last opFrame ((ops ++ [Op.add p o n]).map dagB.vop) o =
      some (frameOfLabel (AssignmentB.nodeLabel n)) := by
  simp [Dag.vop, FrameFlow.last_append_single, Op.slots, opFrame_add]

theorem after_source_frame (ops : List Op) (p n : Nat) :
    FrameFlow.last opFrame ((ops ++ [Op.src p n]).map dagB.vop) p =
      some (frameOfLabel (AssignmentB.startLabel p)) := by
  simp [Dag.vop, FrameFlow.last_append_single, Op.slots, opFrame_src]

theorem opFrame_vop_copy (p s n : Nat) :
    opFrame (dagB.vop (.copy p s n)) = frameOfLabel (AssignmentB.startLabel s) := by
  by_cases hn : n < dagB.v <;> simp only [Dag.vop, hn, ite_true, ite_false, opFrame_src, opFrame_copy]

theorem fseq_opBlocks (s : Nat) (ops : List Op) (frame : Op → LMat) :
    fseq (.inl (.aux s)) (opBlocks ops frame).flatten = FrameFlow.framesOf frame s ops := by
  have h : (opBlocks ops frame).flatten = ops.map fun op => ⟨gL (opGate op), frame op⟩ := by
    induction ops with
    | nil => rfl
    | cons op ops ih => simpa only [opBlocks, List.map_cons, List.flatten_cons, single,
        List.singleton_append, List.map_cons] using congrArg (⟨gL (opGate op), frame op⟩ :: ·) ih
  rw [h]
  simp only [fseq, List.filter_map, List.map_map, Function.comp_def, aux_mem_opGate,
    FrameFlow.framesOf]

theorem opBlocks_aux_chain (R : LMat → LMat → Prop) (frame : Op → LMat)
    (ops : List Op) (cur : Nat → Option LMat) (h : FrameFlow.Mono R frame ops cur) (s : Nat) :
    List.IsChain R ((cur s).toList ++ fseq (.inl (.aux s)) (opBlocks ops frame).flatten) := by
  rw [fseq_opBlocks]
  exact FrameFlow.mono_chain R frame ops cur h s

theorem copies_pivot_frames (p n : Nat) (fs : List Nat) :
    fseq (.inl (.aux p)) (opBlocks (copies p fs n) assignment.side).flatten =
      fs.map fun s => frameOfLabel (AssignmentB.startLabel s) := by
  rw [fseq_opBlocks, FrameFlow.copies_pivot]
  rfl

theorem served_internal_aux_chain (n p : Nat) (hn : leafCount ≤ n) (us : List Use)
    (st : State) (cur : Nat → Option LMat) (hp : p < st.next)
    (hmono : FrameFlow.Mono Nested opFrame (st.ops.map dagB.vop) cur)
    (hfresh : ∀ s, st.next ≤ s →
      ((st.ops.map dagB.vop).foldl (FrameFlow.touch opFrame) cur) s = none)
    (hchain : List.IsChain Nested
      ((((st.ops.map dagB.vop).foldl (FrameFlow.touch opFrame) cur) p).toList ++
        (List.range' st.next (us.length - 1)).map fun s => frameOfLabel (AssignmentB.startLabel s)))
    (s : Nat) :
    List.IsChain Nested ((cur s).toList ++
      fseq (.inl (.aux s)) (opBlocks ((State.serve n p st us).ops.map dagB.vop) opFrame).flatten) := by
  apply opBlocks_aux_chain Nested opFrame _ cur _ s
  apply FrameFlow.serve_mono_internal dagB Nested opFrame n p hn us st cur hp hmono hfresh
  simpa only [opFrame_copy] using hchain

theorem served_leaf_aux_chain (n p : Nat) (hn : n < leafCount) (us : List Use)
    (st : State) (cur : Nat → Option LMat)
    (hmono : FrameFlow.Mono Nested opFrame (st.ops.map dagB.vop) cur)
    (hfresh : ∀ s, st.next ≤ s →
      ((st.ops.map dagB.vop).foldl (FrameFlow.touch opFrame) cur) s = none) (s : Nat) :
    List.IsChain Nested ((cur s).toList ++
      fseq (.inl (.aux s)) (opBlocks ((State.serve n p st us).ops.map dagB.vop) opFrame).flatten) := by
  apply opBlocks_aux_chain Nested opFrame _ cur _ s
  exact FrameFlow.serve_mono_leaf dagB Nested opFrame n p hn us st cur hmono hfresh

/-- The kept internal-node slot retains its last actual copy frame. -/
theorem kept_frame_internal (n p : Nat) (hn : leafCount ≤ n) (us : List Use) (st : State) :
    FrameFlow.last opFrame ((State.serve n p st us).ops.map dagB.vop) p =
      (((List.range' st.next (us.length - 1)).map fun s =>
        frameOfLabel (AssignmentB.startLabel s)).getLast?).or
          (FrameFlow.last opFrame (st.ops.map dagB.vop) p) := by
  simpa only [opFrame_copy] using FrameFlow.serve_pivot_internal dagB opFrame n p hn us st

/-- Independent V sources never advance the kept leaf slot's frame. -/
theorem kept_frame_leaf (n p : Nat) (hn : n < leafCount) (us : List Use) (st : State)
    (hp : p < st.next) :
    FrameFlow.last opFrame ((State.serve n p st us).ops.map dagB.vop) p =
      FrameFlow.last opFrame (st.ops.map dagB.vop) p :=
  FrameFlow.serve_pivot_leaf dagB opFrame n p hn us st hp

theorem copied_frame (n p : Nat) (us : List Use) (st : State) (hp : p < st.next)
    (s : Nat) (hs : s ∈ List.range' st.next (us.length - 1)) :
    FrameFlow.last opFrame ((State.serve n p st us).ops.map dagB.vop) s =
      some (frameOfLabel (AssignmentB.startLabel s)) := by
  rw [FrameFlow.serve_copy_frame dagB opFrame n p us st hp s hs, opFrame_vop_copy]

/-- The frame left in an internal pivot after its serving copies. -/
def copyEnd (n : Nat) (us : List Use) (st : State) : LMat :=
  (((List.range' st.next (us.length - 1)).map fun s =>
    frameOfLabel (AssignmentB.startLabel s)).getLast?).getD
      (frameOfLabel (AssignmentB.nodeLabel n))

theorem copyEnd_eq (n : Nat) (us : List Use) (st : State) :
    copyEnd n us st = if us.length ≤ 1 then frameOfLabel (AssignmentB.nodeLabel n)
      else frameOfLabel (AssignmentB.startLabel (st.next + (us.length - 1) - 1)) := by
  unfold copyEnd
  rw [List.getLast?_map, List.getLast?_range']
  by_cases h : us.length - 1 = 0
  · simp [h, show us.length ≤ 1 by omega]
  · simp [h, show ¬us.length ≤ 1 by omega]

/-- Frame of every newly served internal use, including the kept head use. -/
theorem served_internal_use_frame (n p : Nat) (hn : leafCount ≤ n) (us : List Use)
    (st : State) (hnd : us.Nodup) (hp : p < st.next)
    (hcur : FrameFlow.last opFrame (st.ops.map dagB.vop) p =
      some (frameOfLabel (AssignmentB.nodeLabel n))) (u : Use) (hu : u ∈ us) :
    FrameFlow.last opFrame ((State.serve n p st us).ops.map dagB.vop)
      ((State.serve n p st us).pend u) =
        some (if (State.serve n p st us).pend u = p then copyEnd n us st
          else frameOfLabel (AssignmentB.startLabel ((State.serve n p st us).pend u))) := by
  rw [FrameFlow.serve_use_frame dagB opFrame n p us st hnd hp u hu]
  by_cases hs : (State.serve n p st us).pend u = p
  · rw [ite_eq_left hs, ite_eq_left hs, kept_frame_internal n p hn us st, hcur]
    unfold copyEnd
    cases h : ((List.range' st.next (us.length - 1)).map fun s =>
      frameOfLabel (AssignmentB.startLabel s)).getLast? <;> rfl
  · rw [ite_eq_right hs, ite_eq_right hs, opFrame_vop_copy]

/-- Every served leaf use has its own V-start frame, including the kept use. -/
theorem served_leaf_use_frame (n p : Nat) (hn : n < leafCount) (us : List Use)
    (st : State) (hnd : us.Nodup) (hp : p < st.next)
    (hcur : FrameFlow.last opFrame (st.ops.map dagB.vop) p =
      some (frameOfLabel (AssignmentB.startLabel p))) (u : Use) (hu : u ∈ us) :
    FrameFlow.last opFrame ((State.serve n p st us).ops.map dagB.vop)
      ((State.serve n p st us).pend u) =
        some (frameOfLabel (AssignmentB.startLabel ((State.serve n p st us).pend u))) := by
  rw [FrameFlow.serve_use_frame dagB opFrame n p us st hnd hp u hu]
  by_cases hs : (State.serve n p st us).pend u = p
  · rw [ite_eq_left hs, kept_frame_leaf n p hn us st hp, hcur, hs]
  · rw [ite_eq_right hs, opFrame_vop_copy]

/-- Every newly served use of an actual leaf compiler step has its own start frame. -/
theorem leaf_step_use_frame (n : Nat) (hn : n < leafCount) (st : State)
    (u : Use) (hu : u ∈ dagB.freeUses n) :
    FrameFlow.last opFrame ((dagB.step st n).ops.map dagB.vop) ((dagB.step st n).pend u) =
      some (frameOfLabel (AssignmentB.startLabel ((dagB.step st n).pend u))) := by
  let st' : State := { st with next := st.next + 1, ops := st.ops ++ [Op.src st.next n] }
  have hstep : dagB.step st n = State.serve n st.next st' (dagB.freeUses n) := by
    simp only [Dag.step, show n < dagB.v from hn, ite_true, st']
  rw [hstep]
  apply served_leaf_use_frame n st.next hn (dagB.freeUses n) st' (dagB.freeUses_nodup n)
  · change st.next < st.next + 1
    omega
  · exact after_source_frame st.ops st.next n
  · exact hu

/-- Internal compiler steps give copied uses their starts and the kept use the
last actual copy frame. This also covers linked nodes, with either pivot. -/
theorem internal_step_use_frames (n : Nat) (hn : leafCount ≤ n) (st : State)
    (hleft : st.pend (.gate n false) < st.next) (hright : st.pend (.gate n true) < st.next) :
    ∃ p, (p = st.pend (.gate n false) ∨ p = st.pend (.gate n true)) ∧
      ∀ u ∈ dagB.freeUses n,
        FrameFlow.last opFrame ((dagB.step st n).ops.map dagB.vop) ((dagB.step st n).pend u) =
          some (if (dagB.step st n).pend u = p then copyEnd n (dagB.freeUses n) st
            else frameOfLabel (AssignmentB.startLabel ((dagB.step st n).pend u))) := by
  obtain ⟨p, o, st', hp, _ho, hops, hnext, hstep⟩ := FrameFlow.step_internal_shape dagB n hn st
  have hplt : p < st'.next := by
    rw [hnext]
    rcases hp with rfl | rfl
    · exact hleft
    · exact hright
  have hcur : FrameFlow.last opFrame (st'.ops.map dagB.vop) p =
      some (frameOfLabel (AssignmentB.nodeLabel n)) := by
    rw [hops]
    exact after_add_frame st.ops p o n
  have hend : copyEnd n (dagB.freeUses n) st' = copyEnd n (dagB.freeUses n) st := by
    simp only [copyEnd, hnext]
  refine ⟨p, hp, fun u hu => ?_⟩
  have h := served_internal_use_frame n p hn (dagB.freeUses n) st'
    (dagB.freeUses_nodup n) hplt hcur u hu
  rwa [← hstep, hend] at h

/-- A linked use keeps the donor's addition frame; serving copies of the
pivot do not change the other argument slot used by that link. -/
theorem linked_step_use_frame (n : Nat) (hn : leafCount ≤ n) (hN : n < nodeCount)
    (st : State) (hleft : st.pend (.gate n false) < st.next)
    (hright : st.pend (.gate n true) < st.next)
    (hdistinct : st.pend (.gate n false) ≠ st.pend (.gate n true))
    (o : Bool) (t : Nat) (pos : Bool) (hlink : dagB.link n = some (o, t, pos)) :
    FrameFlow.last opFrame ((dagB.step st n).ops.map dagB.vop) ((dagB.step st n).pend (.gate t pos)) =
      some (frameOfLabel (AssignmentB.nodeLabel n)) := by
  let piv := if o then st.pend (.gate n false) else st.pend (.gate n true)
  let oth := if o then st.pend (.gate n true) else st.pend (.gate n false)
  let st' := ({ st with ops := st.ops ++ [Op.add piv oth n] }).assign oth (.gate t pos)
  have hstep : dagB.step st n = State.serve n piv st' (dagB.freeUses n) := by
    simp only [Dag.step, show ¬n < dagB.v from Nat.not_lt.mpr hn, ite_false, hlink, piv, oth, st']
  have hpiv : piv < st'.next := by
    change piv < st.next
    dsimp only [piv]
    split_ifs <;> assumption
  have hoth : oth < st'.next := by
    change oth < st.next
    dsimp only [oth]
    split_ifs <;> assumption
  have hne : oth ≠ piv := by
    dsimp only [oth, piv]
    split_ifs <;> first | exact hdistinct | exact Ne.symm hdistinct
  have hlu : dagB.linkUse n = some (.gate t pos) := by simp [Dag.linkUse, hlink]
  have hfree : Use.gate t pos ∉ dagB.freeUses n := by
    intro h
    have hf := (dagB.mem_freeUses.mp h).2
    rw [show dagB.linkedB (.gate t pos) = true from (dagB.linkedB_iff _).mpr ⟨n, hN, hlu⟩] at hf
    cases hf
  have hspec := State.serve_spec (fun _ => 0) n piv (dagB.freeUses n) st'
    (dagB.freeUses_nodup n) hpiv (fun s _ => Dag.contents_zero st' s)
  have hpend : (State.serve n piv st' (dagB.freeUses n)).pend (.gate t pos) = oth := by
    rw [hspec.2.2.2.1 _ hfree]
    simp only [st', State.assign_pend, Function.update_self]
  rw [hstep, hpend, FrameFlow.serve_old_frame dagB opFrame n piv (dagB.freeUses n) st' oth hoth hne]
  exact after_add_other_frame st.ops piv oth n

theorem compile_step (n : Nat) : dagB.compileTo (n + 1) = dagB.step (dagB.compileTo n) n := by
  simp only [Dag.compileTo, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem compiler_argument_slots (n : Nat) (hn : leafCount ≤ n) (hN : n < nodeCount) :
    (dagB.compileTo n).pend (.gate n false) < (dagB.compileTo n).next ∧
    (dagB.compileTo n).pend (.gate n true) < (dagB.compileTo n).next ∧
    (dagB.compileTo n).pend (.gate n false) ≠ (dagB.compileTo n).pend (.gate n true) := by
  have hi := dagB.inv_compileTo dagB_valid (fun _ => 0) n (Nat.le_of_lt hN)
  have hleft := dagB.pending_arg dagB_valid hn hN false
  have hright := dagB.pending_arg dagB_valid hn hN true
  refine ⟨hi.slot_lt _ hleft, hi.slot_lt _ hright, fun h => ?_⟩
  have he := hi.inj _ _ hleft hright h
  cases he

theorem compiled_leaf_use_frame (n : Nat) (hn : n < leafCount)
    (u : Use) (hu : u ∈ dagB.freeUses n) :
    FrameFlow.last opFrame ((dagB.compileTo (n + 1)).ops.map dagB.vop)
      ((dagB.compileTo (n + 1)).pend u) =
        some (frameOfLabel (AssignmentB.startLabel ((dagB.compileTo (n + 1)).pend u))) := by
  rw [compile_step]
  exact leaf_step_use_frame n hn _ u hu

theorem compiled_linked_use_frame (n : Nat) (hn : leafCount ≤ n) (hN : n < nodeCount)
    (o : Bool) (t : Nat) (pos : Bool) (hlink : dagB.link n = some (o, t, pos)) :
    FrameFlow.last opFrame ((dagB.compileTo (n + 1)).ops.map dagB.vop)
      ((dagB.compileTo (n + 1)).pend (.gate t pos)) =
        some (frameOfLabel (AssignmentB.nodeLabel n)) := by
  obtain ⟨hl, hr, hd⟩ := compiler_argument_slots n hn hN
  rw [compile_step]
  exact linked_step_use_frame n hn hN _ hl hr hd o t pos hlink

theorem compiled_internal_use_frames (n : Nat) (hn : leafCount ≤ n) (hN : n < nodeCount) :
    ∃ p, (p = (dagB.compileTo n).pend (.gate n false) ∨
        p = (dagB.compileTo n).pend (.gate n true)) ∧
      ∀ u ∈ dagB.freeUses n,
        FrameFlow.last opFrame ((dagB.compileTo (n + 1)).ops.map dagB.vop)
          ((dagB.compileTo (n + 1)).pend u) =
            some (if (dagB.compileTo (n + 1)).pend u = p then
              copyEnd n (dagB.freeUses n) (dagB.compileTo n)
              else frameOfLabel (AssignmentB.startLabel ((dagB.compileTo (n + 1)).pend u))) := by
  obtain ⟨hl, hr, _⟩ := compiler_argument_slots n hn hN
  rw [compile_step]
  exact internal_step_use_frames n hn _ hl hr

/-- Explicit frame of a free use, indexed by its serving order. -/
def freeUseLabel (n i : Nat) : Signed.Frame :=
  let next := (dagB.compileTo n).next
  if n < leafCount then AssignmentB.startLabel (next + i)
  else if i = 0 then
    if (dagB.freeUses n).length ≤ 1 then AssignmentB.nodeLabel n
    else AssignmentB.startLabel (next + ((dagB.freeUses n).length - 1) - 1)
  else AssignmentB.startLabel (next + (i - 1))

/-- Concrete birth frames require only the allocation count and serving index. -/
theorem compiled_free_use_frame (n : Nat) (hN : n < nodeCount)
    (i : Nat) (hi : i < (dagB.freeUses n).length) :
    FrameFlow.last opFrame ((dagB.compileTo (n + 1)).ops.map dagB.vop)
      ((dagB.compileTo (n + 1)).pend (dagB.freeUses n)[i]) =
        some (frameOfLabel (freeUseLabel n i)) := by
  let st := dagB.compileTo n
  have hu : (dagB.freeUses n)[i] ∈ dagB.freeUses n := List.getElem_mem hi
  by_cases hn : n < leafCount
  · have h := compiled_leaf_use_frame n hn _ hu
    have hs : (dagB.compileTo (n + 1)).pend (dagB.freeUses n)[i] = st.next + i := by
      rw [compile_step]
      unfold Dag.step
      rw [ite_eq_left (show n < dagB.v from hn), FrameFlow.serve_pend_index _ _ _ _ (dagB.freeUses_nodup n) i hi]
      split_ifs <;> simp_all [st]
      omega
    simpa only [hs, freeUseLabel, ite_eq_left hn] using h
  · have hn' : leafCount ≤ n := Nat.le_of_not_gt hn
    obtain ⟨p, o, st', hp, _ho, hops, hnext, hstep⟩ := FrameFlow.step_internal_shape dagB n hn' st
    obtain ⟨hl, hr, _⟩ := compiler_argument_slots n hn' hN
    have hplt : p < st'.next := by
      rw [hnext]
      rcases hp with rfl | rfl
      · exact hl
      · exact hr
    have hcur : FrameFlow.last opFrame (st'.ops.map dagB.vop) p =
        some (frameOfLabel (AssignmentB.nodeLabel n)) := by
      rw [hops]
      exact after_add_frame st.ops p o n
    have hf := served_internal_use_frame n p hn' (dagB.freeUses n) st'
      (dagB.freeUses_nodup n) hplt hcur _ hu
    have hs := FrameFlow.serve_pend_index n p (dagB.freeUses n) st'
      (dagB.freeUses_nodup n) i hi
    rw [compile_step]
    change FrameFlow.last opFrame ((dagB.step st n).ops.map dagB.vop)
      ((dagB.step st n).pend (dagB.freeUses n)[i]) = _
    rw [hstep, hf, hs]
    by_cases hi0 : i = 0
    · simp only [hi0, ite_true, copyEnd_eq, hnext, freeUseLabel, ite_eq_right hn]
      split_ifs <;> rfl
    · have hne : st'.next + (i - 1) ≠ p := by omega
      simp only [hi0, ite_false, hne, freeUseLabel, ite_eq_right hn]
      rw [hnext]

/-- Every pending free use has its explicit birth label at every later prefix. -/
theorem pending_free_use_frame (n k : Nat) (hk : k ≤ nodeCount)
    (i : Nat) (hi : i < (dagB.freeUses n).length)
    (hu : dagB.Pending k (dagB.freeUses n)[i]) :
    FrameFlow.last opFrame ((dagB.compileTo k).ops.map dagB.vop)
      ((dagB.compileTo k).pend (dagB.freeUses n)[i]) =
        some (frameOfLabel (freeUseLabel n i)) := by
  have hs := dagB.srcNode_free (List.getElem_mem hi)
  have hlt := FrameFlow.pending_src_lt dagB dagB_valid hu
  rw [hs] at hlt
  rw [FrameFlow.pending_birth_frame dagB dagB_valid opFrame k hk _ hu
    (by simpa only [hs] using hlt), hs]
  exact compiled_free_use_frame n (by omega) i hi

/-- Linked uses retain the donor's addition frame until they are consumed. -/
theorem pending_linked_use_frame (n k : Nat) (hk : k ≤ nodeCount)
    (o : Bool) (t : Nat) (pos : Bool) (hlink : dagB.link n = some (o, t, pos))
    (hu : dagB.Pending k (.gate t pos)) :
    FrameFlow.last opFrame ((dagB.compileTo k).ops.map dagB.vop)
      ((dagB.compileTo k).pend (.gate t pos)) =
        some (frameOfLabel (AssignmentB.nodeLabel n)) := by
  obtain ⟨hn, hN⟩ := dagB_valid.link_donor n o t pos hlink
  have hs := dagB.srcNode_linked dagB_valid hN
    (dagB.linkUse_eq.mpr ⟨o, t, pos, hlink, rfl⟩)
  rw [FrameFlow.pending_birth_frame dagB dagB_valid opFrame k hk _ hu
    (FrameFlow.pending_src_lt dagB dagB_valid hu), hs]
  exact compiled_linked_use_frame n hn hN o t pos hlink

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
