module

public import IntegerMultBounds.MathlibTM2.M8.Frames.TargetGeometryB.HintKernel

/-! Soundness of target block-mask hints is structural in the readout list. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames.TargetGeometryB
noncomputable section
open Local

/-- A covering mask rules out a target bit in every slot when that bit is absent. -/
theorem Hint.bit_false (h : Hint) (hc : h.covers = true) (t : Nat)
    (ht : h.mask.testBit t = false) (s : Nat) (hs : s ∈ h.slots) :
    (CovarianceB.slotMask s).testBit t = false := by
  have he := Nat.beq_eq.mp (List.all_eq_true.mp hc s hs)
  have hb := congrArg (fun m : Nat => m.testBit t) he
  simpa only [Nat.land_eq, Nat.testBit_and, ht, Bool.and_false] using hb.symm

/-- The accelerated label list is exactly the filtered actual readout sequence. -/
theorem fastLabels_eq (hs : List Hint) (hc : hs.all Hint.covers = true) (t : Nat) :
    fastLabels hs t =
      (((hs.flatMap Hint.slots).filter fun s => (CovarianceB.slotMask s).testBit t).map AssignmentB.sigmaLabel) := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hc
    simp only [fastLabels, List.flatMap_cons] at ih ⊢
    rw [ih hc.2, List.filter_append, List.map_append]
    cases ht : h.mask.testBit t with
    | true => simp
    | false =>
      have he : h.slots.filter (fun s => (CovarianceB.slotMask s).testBit t) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro s hs
        exact Bool.eq_false_iff.mp (h.bit_false hc.1 t ht s hs)
      simp [he]

/-- A fixed small partition has a structural proof, independent of its concrete list. -/
theorem split_four (xs : List Nat) :
    xs.take 32 ++ (xs.drop 32).take 32 ++ (xs.drop 64).take 32 ++ xs.drop 96 = xs := by
  have h := List.take_append_drop 32 (xs.drop 64)
  have h' := List.take_append_drop 32 (xs.drop 32)
  have h'' := List.take_append_drop 32 xs
  simp only [List.drop_drop, Nat.reduceAdd] at h h'
  calc
    _ = xs.take 32 ++ ((xs.drop 32).take 32 ++ ((xs.drop 64).take 32 ++ xs.drop 96)) := by
      simp only [List.append_assoc]
    _ = xs := by rw [h, h', h'']

end
end IntegerMultBounds.MathlibTM2.M8.Frames.TargetGeometryB
