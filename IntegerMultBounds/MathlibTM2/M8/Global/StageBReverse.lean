module

public import IntegerMultBounds.MathlibTM2.M8.Global.StageB

/-! The second design-B stage reverses the register blocks and complements
frames, keeping each centre's temporary block in its original internal order. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

def secondStage (F : FrameAssignment) : List (FGate LW 23) :=
  complB (postBlocks F).flatten.reverse ++
    ((List.finRange 23).reverse.map fun c => complB (centreBlockAt centreSlots centreTargets c)).flatten ++
    complB (preBlocks F).flatten.reverse

theorem gatesOf_append (a b : List (FGate LW 23)) :
    gatesOf (a ++ b) = gatesOf a ++ gatesOf b := List.map_append

theorem gatesOf_reverse (a : List (FGate LW 23)) :
    gatesOf a.reverse = (gatesOf a).reverse := List.map_reverse

theorem secondStage_gates (F : FrameAssignment) : gatesOf (secondStage F) =
    (postProgram F.readoutOrder).reverse.map gL ++
      ((List.finRange 23).reverse.map (centreBlockAt centreSlots centreTargets)).flatMap gatesOf ++
      preProgram.reverse.map gL := by
  have hc : gatesOf
      (((List.finRange 23).reverse.map fun c =>
        complB (centreBlockAt centreSlots centreTargets c)).flatten) =
      ((List.finRange 23).reverse.map (centreBlockAt centreSlots centreTargets)).flatMap gatesOf := by
    rw [gatesOf_flatten, List.flatMap_map, List.flatMap_map]
    congr 1
    funext c
    exact gatesOf_complB _
  rw [secondStage, gatesOf_append, gatesOf_append, gatesOf_complB, gatesOf_complB, hc,
    gatesOf_reverse, gatesOf_reverse, gatesOf_flatten, gatesOf_flatten,
    postBlocks_gates, preBlocks_gates, List.map_reverse, List.map_reverse]
  simp only [List.map_reverse]


theorem secondStage_run (F : FrameAssignment) (d : LW → ZMod 2)
    (hz : ∀ c, d (.inr c) = 0) :
    regs (Circuit.run (gatesOf (secondStage F)) d) =
      Circuit.run (wordWithReadoutOrder F.readoutOrder).reverse (regs d) := by
  have hz' : ∀ c ∈ List.finRange 23,
      Circuit.run ((postProgram F.readoutOrder).reverse.map gL) d (.inr c) = 0 := by
    intro c _
    rw [run_gL_inr]
    exact hz c
  rw [secondStage_gates, Circuit.run_append, Circuit.run_append, regs_run_gL,
    centreBlocksAt_reverse_run centreSlots centreTargets (List.finRange 23)
      (List.nodup_finRange 23) _ hz', regs_run_gL,
    word_split, List.reverse_append, List.reverse_append,
    Circuit.run_append, Circuit.run_append]

theorem secondStage_target (F : FrameAssignment) (d : LW → ZMod 2)
    (hz : ∀ c, d (.inr c) = 0) {t : ℕ} (ht : t < leafCount) :
    Circuit.run (gatesOf (secondStage F)) d (.inl (.y t)) =
      d (.inl (.y t)) + d (.inl (.x t)) := by
  exact (congrFun (secondStage_run F d hz) (.y t)).trans
    (wordWithReadoutOrder_reverse_target F.readoutOrder (regs d) ht)

theorem secondStage_other (F : FrameAssignment) (d : LW → ZMod 2)
    (hz : ∀ c, d (.inr c) = 0) (r : Reg) (hr : r.isY = false) :
    Circuit.run (gatesOf (secondStage F)) d (.inl r) = d (.inl r) := by
  exact (congrFun (secondStage_run F d hz) r).trans
    (wordWithReadoutOrder_reverse_other F.readoutOrder (regs d) r hr)

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
