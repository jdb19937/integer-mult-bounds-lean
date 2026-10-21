module

public import IntegerMultBounds.MathlibTM2.M8.Global.StageBReverse
public import IntegerMultBounds.MathlibTM2.M8.Frames.AssignmentB.Checks
public import IntegerMultBounds.MathlibTM2.M8.Frames.SignedFull.BankChecks
public import IntegerMultBounds.MathlibTM2.M8.Frames.SignedFrames

/-! The concrete design-B stages. The frames are checked bank projectors in
compiler numbering. Wire-chain alignment and global cost integration remain
separate obligations; these stages do not yet supply the public theorem. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

def frameOfLabel (label : Signed.Frame) : LMat := label.eval SignedFull.bankEntry

theorem frameOfLabel_idem (label : Signed.Frame)
    (h : label.validCheck SignedFull.bankSize = true) :
    frameOfLabel label * frameOfLabel label = frameOfLabel label :=
  label.idem SignedFull.bankEntry SignedFull.bankSize (fun i _ => SignedFull.bankEntry_checked i) h

theorem frameOfLabel_lframe (label : Signed.Frame)
    (h : label.validCheck SignedFull.bankSize = true) : LFrame (frameOfLabel label) := by
  cases label with
  | zero => exact lframe_zero
  | one => exact lframe_one
  | positive i =>
    have hu := (RootBank.Record.check_spec (SignedFull.bankEntry_checked i)).2.1
    change LFrame (proj formG (rootMat (SignedFull.bankEntry i).basis))
    rw [← rootMatZ_cast] at hu ⊢
    exact lframe_of (proj_idem hu) (frame_height_le8 (rootMatZ_le _) hu)
  | negative i =>
    exact ⟨frameOfLabel_idem _ h,
      (RootBank.Record.bounded _ (SignedFull.bankEntry_checked i)).mono
        ((two_mul_ten_pow 200).trans (ten_pow_mono (by norm_num)))⟩

def assignment : FrameAssignment where
  readoutOrder := AssignmentB.readoutOrder
  sigma s := frameOfLabel (AssignmentB.sigmaLabel s)
  source op := frameOfLabel (AssignmentB.startLabel op.target)
  side op := match op with
    | .add _ _ n => frameOfLabel (AssignmentB.nodeLabel n)
    | .copy _ s _ => frameOfLabel (AssignmentB.startLabel s)
    | .src s _ => frameOfLabel (AssignmentB.startLabel s)
  output j := if j / 3 < leafCount then hyperFrame (leafTriple (j / 3)) else 0

theorem sigma_idem (s : ℕ) : assignment.sigma s * assignment.sigma s = assignment.sigma s :=
  frameOfLabel_idem _ (AssignmentB.sigmaLabel_valid s)

theorem source_idem (op : Op) : assignment.source op * assignment.source op = assignment.source op :=
  frameOfLabel_idem _ (AssignmentB.startLabel_valid op.target)

theorem side_idem (op : Op) : assignment.side op * assignment.side op = assignment.side op := by
  cases op with
  | src s _ | copy _ s _ => exact frameOfLabel_idem _ (AssignmentB.startLabel_valid s)
  | add _ _ n => exact frameOfLabel_idem _ (AssignmentB.nodeLabel_valid n)

theorem output_idem (j : ℕ) : assignment.output j * assignment.output j = assignment.output j := by
  dsimp only [assignment]
  split_ifs with h
  · exact hyperFrame_idem ⟨leafTriple_card h, leafTriple_lt h⟩
  · simp

theorem sigma_lframe (s : ℕ) : LFrame (assignment.sigma s) :=
  frameOfLabel_lframe _ (AssignmentB.sigmaLabel_valid s)

theorem source_lframe (op : Op) : LFrame (assignment.source op) :=
  frameOfLabel_lframe _ (AssignmentB.startLabel_valid op.target)

theorem side_lframe (op : Op) : LFrame (assignment.side op) := by
  cases op with
  | src s _ | copy _ s _ => exact frameOfLabel_lframe _ (AssignmentB.startLabel_valid s)
  | add _ _ n => exact frameOfLabel_lframe _ (AssignmentB.nodeLabel_valid n)

theorem output_lframe (j : ℕ) : LFrame (assignment.output j) := by
  dsimp only [assignment]
  split_ifs with h
  · exact lframe_compl (lineFrame_idem ⟨leafTriple_card h, leafTriple_lt h⟩)
      (lineFrame_bounded ⟨leafTriple_card h, leafTriple_lt h⟩)
  · exact lframe_zero

def firstStage : List (FGate LW 23) := stage assignment

def finalStage : List (FGate LW 23) := secondStage assignment

theorem firstStage_target (d : LW → ZMod 2) (hz : ∀ c, d (.inr c) = 0)
    {t : ℕ} (ht : t < leafCount) :
    Circuit.run (gatesOf firstStage) d (.inl (.y t)) = d (.inl (.y t)) + d (.inl (.x t)) :=
  stage_target assignment d hz ht

theorem finalStage_target (d : LW → ZMod 2) (hz : ∀ c, d (.inr c) = 0)
    {t : ℕ} (ht : t < leafCount) :
    Circuit.run (gatesOf finalStage) d (.inl (.y t)) = d (.inl (.y t)) + d (.inl (.x t)) :=
  secondStage_target assignment d hz ht

theorem firstStage_other (d : LW → ZMod 2) (hz : ∀ c, d (.inr c) = 0)
    (r : Reg) (hr : r.isY = false) : Circuit.run (gatesOf firstStage) d (.inl r) = d (.inl r) :=
  stage_other assignment d hz r hr

theorem finalStage_other (d : LW → ZMod 2) (hz : ∀ c, d (.inr c) = 0)
    (r : Reg) (hr : r.isY = false) : Circuit.run (gatesOf finalStage) d (.inl r) = d (.inl r) :=
  secondStage_other assignment d hz r hr

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
