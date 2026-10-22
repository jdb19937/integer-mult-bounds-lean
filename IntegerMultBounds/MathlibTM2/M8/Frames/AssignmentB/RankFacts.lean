module

public import IntegerMultBounds.MathlibTM2.M8.Frames.AssignmentB.Checks
public import IntegerMultBounds.MathlibTM2.M8.Frames.AssignmentB.RankChecked
public import IntegerMultBounds.MathlibTM2.M8.Frames.SignedFull.BankChecks
public import IntegerMultBounds.MathlibTM2.M8.Frames.SignedFrames
public import IntegerMultBounds.MathlibTM2.M8.Local.ReadoutCoverageChecksB

/-! Every allocated readout frame has rank at most 22. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames.AssignmentB
noncomputable section
open Local

theorem sigma_rank_le (s : Nat) (hs : s < 28866) :
    ((sigmaLabel s).eval SignedFull.bankEntry).rank ≤ 22 := by
  have h := Tree.all_get sigmaRankOk (fun _ => true) 28866 sigmaTable 32768 0
    KeyOrderB.sigmaTable_perfect sigma_rank_checked s (by omega) (by simpa using hs)
  have h : sigmaRankOk s (sigmaLabel s) = true := by
    simpa only [sigmaLabel, sigmaWidth, Nat.zero_add] using h
  unfold sigmaRankOk at h
  rw [Signed.Frame.rank_eval SignedFull.bankEntry SignedFull.bankSize
    (fun i _ => SignedFull.bankEntry_checked i) (sigmaLabel s) (sigmaLabel_valid s)]
  exact Nat.ble_eq.mp h

end
end IntegerMultBounds.MathlibTM2.M8.Frames.AssignmentB
