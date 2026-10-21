module

public import IntegerMultBounds.MathlibTM2.M8.Global.CopyFramesB
public import IntegerMultBounds.MathlibTM2.M8.Local.WitnessOrderB
public import IntegerMultBounds.MathlibTM2.M8.Local.FrameCompile

/-! Direct frame labels for compiler arguments and roots. Every lookup uses
checked local serving orders and allocation counts, without evaluating a compiler prefix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

def freeLabel (n i : Nat) : Signed.Frame :=
  let next := slotsBefore n
  if n < leafCount then AssignmentB.startLabel (next + i)
  else if i = 0 then
    if (bAt n).2.length ≤ 1 then AssignmentB.nodeLabel n
    else AssignmentB.startLabel (next + ((bAt n).2.length - 1) - 1)
  else AssignmentB.startLabel (next + (i - 1))

theorem freeUseLabel_eq (n : Nat) (hn : n < nodeCount) (i : Nat) :
    freeUseLabel n i = freeLabel n i := by
  simp only [freeUseLabel, freeLabel, dagB_compileTo_next n (Nat.le_of_lt hn),
    dagB_freeUses_eq n hn]

theorem pending_free_label (n k : Nat) (hn : n < nodeCount) (hk : k ≤ nodeCount)
    (u : Use) (hu : u ∈ dagB.freeUses n) (hp : dagB.Pending k u) :
    FrameFlow.last opFrame ((dagB.compileTo k).ops.map dagB.vop) ((dagB.compileTo k).pend u) =
      some (frameOfLabel (freeLabel n ((bAt n).2.idxOf u))) := by
  have hm : u ∈ (bAt n).2 := by rwa [← dagB_freeUses_eq n hn]
  have hi : (bAt n).2.idxOf u < (dagB.freeUses n).length := by
    rw [dagB_freeUses_eq n hn]
    exact List.idxOf_lt_length_iff.mpr hm
  have he : (dagB.freeUses n)[(bAt n).2.idxOf u] = u := by
    simp only [dagB_freeUses_eq n hn]
    exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hm)
  have hf := pending_free_use_frame n k hk _ hi (by rwa [he])
  rwa [he, freeUseLabel_eq n hn] at hf

def argumentLabel (k : Nat) (pos : Bool) : Signed.Frame :=
  match (recAt k).donor pos with
  | some n => AssignmentB.nodeLabel n
  | none => freeLabel ((recAt k).arg pos)
      ((bAt ((recAt k).arg pos)).2.idxOf (.gate k pos))

/-- The actual frame consumed by an addition is a direct local table lookup. -/
theorem argument_frame (k : Nat) (hv : leafCount ≤ k) (hk : k < nodeCount) (pos : Bool) :
    FrameFlow.last opFrame ((dagB.compileTo k).ops.map dagB.vop)
      ((dagB.compileTo k).pend (.gate k pos)) = some (frameOfLabel (argumentLabel k pos)) := by
  have hp := dagB.pending_arg dagB_valid hv hk pos
  cases hd : (recAt k).donor pos with
  | none =>
    have hu : Use.gate k pos ∈ dagB.freeUses ((recAt k).arg pos) := by
      rw [Dag.mem_freeUses, Dag.mem_uses_gate]
      exact ⟨⟨hk, hv, rfl⟩, linkedB_of_donor hd⟩
    simpa only [argumentLabel, hd, show dagB.arg k pos = (recAt k).arg pos from rfl] using pending_free_label _ k
      ((dagB_valid.arg_lt k hv hk pos).trans hk) (Nat.le_of_lt hk) _ hu hp
  | some n =>
    have hok := donor_ok_at hk pos
    rw [hd] at hok
    obtain ⟨hn, L, hL, ht, hpos⟩ := donorOk_some hok
    have hl : dagB.link n = some (L.operand, k, pos) := by simp [dagB, dag, hL, ht, hpos]
    simpa only [argumentLabel, hd] using
      pending_linked_use_frame n k (Nat.le_of_lt hk) L.operand k pos hl hp

def rootLabel (j : Nat) : Signed.Frame :=
  let n := (roots.get rootWidth j).node
  freeLabel n ((bAt n).2.idxOf (.root j))

/-- Final read slots retain their explicit free-use labels. -/
theorem root_frame (j : Nat) (hj : j < rootCount) :
    FrameFlow.last opFrame (dagB.compile.ops.map dagB.vop) (dagB.compile.pend (.root j)) =
      some (frameOfLabel (rootLabel j)) := by
  have hu : Use.root j ∈ dagB.freeUses (dagB.rootNode j) :=
    dagB.mem_freeUses.mpr ⟨(dagB.mem_uses_root _ j).mpr ⟨hj, rfl⟩, dagB.root_not_linked j⟩
  rw [Dag.compile]
  have h := pending_free_label (dagB.rootNode j) dagB.N (dagB_valid.root_lt j hj)
    (show dagB.N ≤ nodeCount from le_rfl) (.root j) hu (dagB.root_pending dagB_valid hj)
  simpa only [rootLabel, show dagB.rootNode j = (roots.get rootWidth j).node from rfl] using h

theorem opFrame_eq_opLabel : opFrame = FrameFlow.opLabel
    (fun n => frameOfLabel (AssignmentB.nodeLabel n))
    (fun s => frameOfLabel (AssignmentB.startLabel s)) := by
  funext op
  cases op <;> rfl

/-- Whole-compiler nesting reduces to direct incoming labels and local copy chains. -/
theorem compilerTo_mono
    (hsource : ∀ k, leafCount ≤ k → k < nodeCount → ∀ pos,
      Nested (frameOfLabel (argumentLabel k pos)) (frameOfLabel (AssignmentB.nodeLabel k)))
    (hcopies : ∀ k, leafCount ≤ k → k < nodeCount →
      List.IsChain Nested (frameOfLabel (AssignmentB.nodeLabel k) ::
        (List.range' (slotsBefore k) ((bAt k).2.length - 1)).map
          fun s => frameOfLabel (AssignmentB.startLabel s))) :
    ∀ k, k ≤ nodeCount →
      FrameFlow.Mono Nested opFrame ((dagB.compileTo k).ops.map dagB.vop) (fun _ => none) := by
  intro j hj
  rw [opFrame_eq_opLabel]
  apply FrameFlow.compileTo_mono dagB dagB_valid Nested
    (fun n => frameOfLabel (AssignmentB.nodeLabel n))
    (fun s => frameOfLabel (AssignmentB.startLabel s)) ?_ ?_ j hj
  · intro k hv hk pos a ha
    have hf := argument_frame k hv hk pos
    rw [opFrame_eq_opLabel] at hf
    rw [hf] at ha
    cases Option.some.inj ha
    exact hsource k hv hk pos
  · intro k hv hk
    simpa only [dagB_compileTo_next k (Nat.le_of_lt hk), dagB_freeUses_eq k hk] using
      hcopies k hv hk

/-- The actual framed compiler gates inherit those structural wire chains. -/
theorem compilerTo_aux_chain
    (hsource : ∀ k, leafCount ≤ k → k < nodeCount → ∀ pos,
      Nested (frameOfLabel (argumentLabel k pos)) (frameOfLabel (AssignmentB.nodeLabel k)))
    (hcopies : ∀ k, leafCount ≤ k → k < nodeCount →
      List.IsChain Nested (frameOfLabel (AssignmentB.nodeLabel k) ::
        (List.range' (slotsBefore k) ((bAt k).2.length - 1)).map
          fun s => frameOfLabel (AssignmentB.startLabel s)))
    (k : Nat) (hk : k ≤ nodeCount) (s : Nat) :
    List.IsChain Nested
      (fseq (.inl (.aux s)) (opBlocks ((dagB.compileTo k).ops.map dagB.vop) opFrame).flatten) := by
  simpa only [Option.toList_none, List.nil_append] using
    opBlocks_aux_chain Nested opFrame ((dagB.compileTo k).ops.map dagB.vop) (fun _ => none)
      (compilerTo_mono hsource hcopies k hk) s

theorem compiler_aux_chain
    (hsource : ∀ k, leafCount ≤ k → k < nodeCount → ∀ pos,
      Nested (frameOfLabel (argumentLabel k pos)) (frameOfLabel (AssignmentB.nodeLabel k)))
    (hcopies : ∀ k, leafCount ≤ k → k < nodeCount →
      List.IsChain Nested (frameOfLabel (AssignmentB.nodeLabel k) ::
        (List.range' (slotsBefore k) ((bAt k).2.length - 1)).map
          fun s => frameOfLabel (AssignmentB.startLabel s))) (s : Nat) :
    List.IsChain Nested (fseq (.inl (.aux s)) (opBlocks dagB.opsB opFrame).flatten) := by
  simpa only [Dag.opsB, Dag.compile] using
    compilerTo_aux_chain hsource hcopies dagB.N le_rfl s

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
