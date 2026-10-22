module

public import IntegerMultBounds.MathlibTM2.M8.Local.CovarianceFactsB
public import IntegerMultBounds.MathlibTM2.M8.Local.CovarianceChecksB
public import IntegerMultBounds.MathlibTM2.M8.Local.CovarianceRootChecksB
public import IntegerMultBounds.MathlibTM2.M8.Local.WitnessOrderB
public import IntegerMultBounds.MathlibTM2.M8.Local.Scalar

/-! Checked concrete coefficient equations and agreement with the actual root targets. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds.MathlibTM2.M8.Local
open Classical
open CovarianceB MaskWeightsB

theorem covariance_node_checked (n : Nat) (hn : n < nodeCount) :
    CovarianceB.nodeOk coefficientMasks n (bAt n) = true := by
  simpa only [bAt, width, Nat.zero_add] using
    Tree.all_get _ _ _ bdata 65536 0 bdata_perfect covariance_checked n
      (by exact hn.trans (by decide)) (by simpa using hn)

/-- Root-mask centre enumeration is precisely the existing readout target list. -/
theorem covariance_centreTargets (c : Nat) :
    CovarianceB.centreTargets c = targets (3 * leafCount + c) := by
  rw [targets, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  unfold CovarianceB.centreTargets
  apply List.filter_congr
  intro t _
  cases hs : (records.get width t).supp with
  | three a b d =>
    by_cases ha : c = a <;> by_cases hb : c = b <;> by_cases hd : c = d <;>
      simp [leafTriple, recAt, hs, ha, hb, hd, Bool.eq_false_iff, Nat.beq_eq]
  | two a b z => simp [leafTriple, recAt, hs]
  | one a p => simp [leafTriple, recAt, hs]

/-- Every concrete root mask has the actual compiler root's target coefficients. -/
theorem covariance_root_coefficient (j : Nat) (hj : j < rootCount) (t : Nat) :
    coeff (coefficientMasks.root j) t = ((targets j).count t : ZMod 2) := by
  by_cases ho : j < 3 * leafCount
  · change coeff (rootMask j) t = _
    rw [rootMask, ite_eq_left ho, coeff_shiftLeft, count_out ho]
    split_ifs <;> simp
  · have hc : j - 3 * leafCount < 23 := by
      change j < 5336 at hj
      change ¬j < 3 * 1771 at ho
      change j - 3 * 1771 < 23
      omega
    have he : j = 3 * leafCount + (j - 3 * leafCount) := by omega
    rw [he]
    have hcheck : centreOk coefficientMasks (j - 3 * leafCount) = true :=
      List.all_eq_true.mp centres_checked _ (List.mem_range.mpr hc)
    rw [← covariance_centreTargets]
    exact centreOk_coeff coefficientMasks _ hcheck t

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
