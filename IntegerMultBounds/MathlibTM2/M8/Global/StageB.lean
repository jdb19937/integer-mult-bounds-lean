module

public import IntegerMultBounds.MathlibTM2.M8.Global.CentreBlocks
public import IntegerMultBounds.MathlibTM2.M8.Local.ScalarB

/-! The executable design-B stage, with independently supplied frames. Scalar
correctness is structural and does not depend on how those frames were selected. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

structure FrameAssignment where
  readoutOrder : List ℕ := planB.keyD
  sigma : ℕ → LMat
  source : Op → LMat
  side : Op → LMat
  output : ℕ → LMat

def centreSlots (c : Fin 23) : ℕ := dagB.compile.pend (.root (3 * leafCount + c))
def centreTargets (c : Fin 23) : List ℕ := targets (3 * leafCount + c)

def nowSlots : List ℕ := (List.range dagB.compile.next).filter fun s => !planB.isDef s
def lateSlots (keyD : List ℕ) : List ℕ := keyed keyD ((List.range dagB.compile.next).filter planB.isDef)
def outputRoots : List ℕ := (List.range dagB.rootCount).filter fun j => !planB.cen j

def readBlocks (F : FrameAssignment) (ss : List ℕ) : List (List (FGate LW 23)) :=
  ss.flatMap fun s => (dagB.readout targets leafCount s).map fun g => single (gL g) (F.sigma s)

def opBlocks (ops : List Op) (frame : Op → LMat) : List (List (FGate LW 23)) :=
  ops.map fun op => single (gL (opGate op)) (frame op)

def outBlocks (F : FrameAssignment) : List (List (FGate LW 23)) :=
  outputRoots.flatMap fun j => (targets j).map fun t =>
    single (gL (ReversibleFanout.add (.y t) (.aux (dagB.compile.pend (.root j))))) (F.output j)

def preBlocks (F : FrameAssignment) : List (List (FGate LW 23)) :=
  readBlocks F nowSlots ++ opBlocks (dagB.vNow planB) F.source ++
    opBlocks (dagB.opsFirst planB) F.side

def postBlocks (F : FrameAssignment) : List (List (FGate LW 23)) :=
  readBlocks F (lateSlots F.readoutOrder) ++ opBlocks (dagB.vLate planB) F.source ++
    opBlocks (dagB.opsRest planB) F.side ++ outBlocks F ++
    opBlocks (dagB.vNow planB ++ dagB.vLate planB ++ dagB.opsFirst planB ++
      dagB.opsRest planB).reverse (fun _ => 1)

def blocks (F : FrameAssignment) : List (List (FGate LW 23)) :=
  preBlocks F ++ (List.finRange 23).map (centreBlockAt centreSlots centreTargets) ++ postBlocks F

def stage (F : FrameAssignment) : List (FGate LW 23) := (blocks F).flatten

def preProgram : Circuit.Program Reg (ZMod 2) :=
  dagB.rdNow targets leafCount planB ++ (dagB.vNow planB).map opGate ++
    (dagB.opsFirst planB).map opGate

def postProgram (keyD : List ℕ) : Circuit.Program Reg (ZMod 2) :=
  dagB.rdLate targets leafCount (planWithReadoutOrder keyD) ++ (dagB.vLate planB).map opGate ++
    (dagB.opsRest planB).map opGate ++ dagB.outReads targets planB ++
    ((dagB.vNow planB ++ dagB.vLate planB ++ dagB.opsFirst planB ++
      dagB.opsRest planB).map opGate).reverse

theorem readBlocks_gates (F : FrameAssignment) (ss : List ℕ) :
    (readBlocks F ss).flatMap gatesOf = (dagB.readouts targets leafCount ss).map gL := by
  simp only [readBlocks, List.flatMap_assoc, Dag.readouts, List.map_flatMap]
  apply List.flatMap_congr
  intro s _
  exact singles_gates _ _

theorem outBlocks_gates (F : FrameAssignment) :
    (outBlocks F).flatMap gatesOf = (dagB.outReads targets planB).map gL := by
  simp only [outBlocks, Dag.outReads, Dag.rootReadsAt, outputRoots,
    List.flatMap_assoc, List.map_flatMap]
  apply List.flatMap_congr
  intro j _
  exact singles_map_gates _ _ _

theorem opBlocks_gates (ops : List Op) (frame : Op → LMat) :
    (opBlocks ops frame).flatMap gatesOf = (ops.map opGate).map gL :=
  singles_map_gates ops opGate frame

theorem preBlocks_gates (F : FrameAssignment) :
    (preBlocks F).flatMap gatesOf = preProgram.map gL := by
  simp only [preBlocks, List.flatMap_append, readBlocks_gates, opBlocks_gates,
    preProgram, List.map_append, Dag.rdNow, nowSlots]

theorem postBlocks_gates (F : FrameAssignment) :
    (postBlocks F).flatMap gatesOf = (postProgram F.readoutOrder).map gL := by
  simp only [postBlocks, List.flatMap_append, readBlocks_gates, opBlocks_gates,
    outBlocks_gates, postProgram, List.map_append, List.map_reverse, Dag.rdLate, lateSlots, planWithReadoutOrder]
  rfl

theorem centre_indices :
    (List.range dagB.rootCount).filter planB.cen =
      (List.finRange 23).map fun c => 3 * leafCount + c.val := by
  have hr : dagB.rootCount = 3 * leafCount + 23 := rfl
  have hfin : (List.finRange 23).map Fin.val = List.range 23 := by
    apply List.ext_get <;> simp
  rw [hr, List.range_add, List.filter_append]
  have hlow : (List.range (3 * leafCount)).filter planB.cen = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro j hj
    simp only [planB, cenB, Nat.ble_eq]
    have := List.mem_range.mp hj
    omega
  have hhigh : ((List.range 23).map (3 * leafCount + ·)).filter planB.cen =
      (List.range 23).map (3 * leafCount + ·) := by
    apply List.filter_eq_self.mpr
    intro j hj
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hj
    simp [planB, cenB]
  rw [hlow, hhigh, List.nil_append, ← hfin, List.map_map]
  rfl

theorem centreReads_gates :
    dagB.centreReads targets planB =
      (List.finRange 23).flatMap (centreReadsAt centreSlots centreTargets) := by
  simp only [Dag.centreReads, Dag.rootReadsAt, centre_indices, List.flatMap_map]
  rfl

theorem word_split (keyD : List ℕ) : wordWithReadoutOrder keyD = preProgram ++
    (List.finRange 23).flatMap (centreReadsAt centreSlots centreTargets) ++ postProgram keyD := by
  simp only [wordWithReadoutOrder, Dag.wordB, preProgram, postProgram]
  rw [show dagB.centreReads targets (planWithReadoutOrder keyD) =
    (List.finRange 23).flatMap (centreReadsAt centreSlots centreTargets) from centreReads_gates]
  simp only [Dag.rdNow, Dag.vNow, Dag.vLate, Dag.opsFirst, Dag.opsRest, Dag.outReads,
    planWithReadoutOrder, BPlan.isDef, List.append_assoc]
  rfl


theorem stage_run (F : FrameAssignment) (d : LW → ZMod 2)
    (hz : ∀ c, d (.inr c) = 0) :
    regs (Circuit.run (gatesOf (stage F)) d) = Circuit.run (wordWithReadoutOrder F.readoutOrder) (regs d) := by
  rw [stage, gatesOf_flatten, blocks, List.flatMap_append, List.flatMap_append,
    preBlocks_gates, postBlocks_gates, word_split]
  exact run_with_centres centreSlots centreTargets (List.finRange 23) (List.nodup_finRange 23)
    preProgram (postProgram F.readoutOrder) d (fun c _ => hz c)

theorem stage_target (F : FrameAssignment) (d : LW → ZMod 2)
    (hz : ∀ c, d (.inr c) = 0) {t : ℕ} (ht : t < leafCount) :
    Circuit.run (gatesOf (stage F)) d (.inl (.y t)) = d (.inl (.y t)) + d (.inl (.x t)) := by
  exact (congrFun (stage_run F d hz) (.y t)).trans (wordWithReadoutOrder_target F.readoutOrder (regs d) ht)

theorem stage_other (F : FrameAssignment) (d : LW → ZMod 2)
    (hz : ∀ c, d (.inr c) = 0) (r : Reg) (hr : r.isY = false) :
    Circuit.run (gatesOf (stage F)) d (.inl r) = d (.inl r) := by
  exact (congrFun (stage_run F d hz) r).trans (wordWithReadoutOrder_other F.readoutOrder (regs d) r hr)

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
