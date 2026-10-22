module

public import IntegerMultBounds.MathlibTM2.M8.Global.DesignB
public import IntegerMultBounds.MathlibTM2.M8.Frames.AssignmentB.RankFacts
public import IntegerMultBounds.MathlibTM2.M8.Global.GaugedExitB
public import IntegerMultBounds.MathlibTM2.M8.Global.MoveMoments

/-! Executable single-exchange exits for the actual design-B side gauges. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

/-- Complementation exchanges positive and negative descriptions of a checked bank frame. -/
theorem frameOfLabel_compl_lframe (label : Signed.Frame)
    (h : label.validCheck SignedFull.bankSize = true) : LFrame (1 - frameOfLabel label) := by
  cases label with
  | zero => simpa only [frameOfLabel, Signed.Frame.eval, sub_zero] using lframe_one
  | one => simpa only [frameOfLabel, Signed.Frame.eval, sub_self] using lframe_zero
  | positive i =>
    have hn : (Signed.Frame.negative i).validCheck SignedFull.bankSize = true := h
    simpa only [frameOfLabel, Signed.Frame.eval, RootBank.Record.frame, rootFrame] using
      frameOfLabel_lframe (.negative i) hn
  | negative i =>
    have hp : (Signed.Frame.positive i).validCheck SignedFull.bankSize = true := h
    simpa only [frameOfLabel, Signed.Frame.eval, RootBank.Record.frame, rootFrame, sub_sub_cancel] using
      frameOfLabel_lframe (.positive i) hp

theorem sigma_compl_lframe (s : Nat) : LFrame (1 - assignment.sigma s) :=
  frameOfLabel_compl_lframe _ (AssignmentB.sigmaLabel_valid s)

variable {ι : Type}

/-- The first-stage side slot exits from `I ⊗ Q` to the complement of `σ ⊗ Q`. -/
def sideExit1 (i : ι) (T : V) (s : Nat) : FStep ι 529 :=
  .exit i (lift1 (lineOf T) 1) (lift1 (lineOf T) (assignment.sigma s))

/-- The reflected side slot exits to the complement of its entrance gauge. -/
def sideExit2 (i : ι) (S : V) (s : Nat) : FStep ι 529 :=
  .exit i (lift2 (lineOf S) (1 - assignment.sigma s)) (lift2 (lineOf S) 0)

section
variable [DecidableEq ι]

theorem sideExit1_ok (i : ι) (T : V) (s : Nat) (fr : ι → Mat 529) (z : ι → Prop)
    (hi : fr i = lift1 (lineOf T) 1) : (sideExit1 i T s).Ok fr z :=
  gauged_exit1_ok i fr z (lframe_lineOf T) (sigma_lframe s) (sigma_compl_lframe s) hi

theorem sideExit2_ok (i : ι) (S : V) (s : Nat) (fr : ι → Mat 529) (z : ι → Prop)
    (hi : fr i = lift2 (lineOf S) (1 - assignment.sigma s)) : (sideExit2 i S s).Ok fr z :=
  gauged_exit2_ok i fr z (lframe_lineOf S)
    (lframe_compl (lineOf_idem S) (lineFrame_bounded (leafTriple_isTriple S.2)))
    (sigma_compl_lframe s) hi

end

/-- The first exit's whole-projector charge agrees with the design-B ledger. -/
theorem sideExit1_rank (i : ι) (T : V) (s : Nat) :
    edgeRanks [sideExit1 i T s] = 506 + (assignment.sigma s).rank := by
  simpa only [edgeRanks, sideExit1, add_zero] using
    gauged_exit1_rank (lineOf_idem T) (sigma_idem s) (rank_lineOf T)

/-- The reflected exit has the same whole-projector charge. -/
theorem sideExit2_rank (i : ι) (S : V) (s : Nat) :
    edgeRanks [sideExit2 i S s] = 506 + (assignment.sigma s).rank := by
  simpa only [edgeRanks, sideExit2, add_zero] using
    gauged_exit2_rank (lineOf_idem S) (sigma_idem s) (rank_lineOf S)

/-- The first exit contributes one term to every move moment. -/
theorem sideExit1_moment {M : Type} [AddCommMonoid M] (φ : Nat → M)
    (i : ι) (T : V) (s : Nat) :
    edgeMoment φ [sideExit1 i T s] = φ (506 + (assignment.sigma s).rank) := by
  simp only [edgeMoment, sideExit1, add_zero,
    gauged_exit1_rank (lineOf_idem T) (sigma_idem s) (rank_lineOf T)]

/-- The reflected exit also contributes a single whole-projector term. -/
theorem sideExit2_moment {M : Type} [AddCommMonoid M] (φ : Nat → M)
    (i : ι) (S : V) (s : Nat) :
    edgeMoment φ [sideExit2 i S s] = φ (506 + (assignment.sigma s).rank) := by
  simp only [edgeMoment, sideExit2, add_zero,
    gauged_exit2_rank (lineOf_idem S) (sigma_idem s) (rank_lineOf S)]

/-- Every allocated readout frame leaves a proper exterior child. -/
theorem sigma_rank_le (s : Nat) (hs : s < 28866) : (assignment.sigma s).rank ≤ 22 :=
  AssignmentB.sigma_rank_le s hs

theorem sideExit1_rank_lt (i : ι) (T : V) (s : Nat) (hs : s < 28866) :
    edgeRanks [sideExit1 i T s] < 529 := by
  rw [sideExit1_rank]
  have h := sigma_rank_le s hs
  omega

theorem sideExit2_rank_lt (i : ι) (S : V) (s : Nat) (hs : s < 28866) :
    edgeRanks [sideExit2 i S s] < 529 := by
  rw [sideExit2_rank]
  have h := sigma_rank_le s hs
  omega

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
