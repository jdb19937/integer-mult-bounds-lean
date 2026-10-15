module

public import IntegerMultBounds.MathlibTM2.Fast.CompactReservationGeometry

/-! The reserved piece records cover the back and active coordinates exactly once.
Together with the high row/front kernel coordinates they cover the original
selected interval. This is coverage of records, not an execution theorem. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open CompactGadgetReservationCapacity
noncomputable section

theorem compactReservedPcs_vals (K a oS B J D ρ : ℕ) :
    ((compactReservedPcs K a oS B (oS+K*B) J D).flatMap (synPcVals ρ K)).Perm
      ((List.range (B+D)).map fun i => ρ+oS+K*i) := by
  unfold compactReservedPcs
  rw [List.flatMap_append,range_add_map]
  apply List.Perm.append
  · by_cases hB : B=0
    · simp [hB]
    · simp only [ite_eq_right hB,List.flatMap_singleton,synPcVals,bits]
      apply List.Perm.of_eq
      apply List.map_congr_left
      intro i _
      omega
  · refine (synPcs_vals_full K a D (oS+K*B) J ρ).trans ?_
    apply List.Perm.of_eq
    apply List.map_congr_left
    intro i _
    ring

/-- The remaining high coordinates are precisely the row and front reservations. -/
theorem compactReservation_full_coverage {d g K D : ℕ}
    (h : CompactReservationFits d g K D) (a oS J ρ : ℕ) :
    (((compactReservedPcs K a oS (backChunks d g K) (oS+K*backChunks d g K) J
        (compactReservationActive d g K D)).flatMap (synPcVals ρ K)) ++
      (List.range (CompactGlobalRowPadding.rowAxes NW m d+frontChunks d g K)).map
        (fun i => ρ+oS+K*(backChunks d g K+compactReservationActive d g K D+i))).Perm
      ((List.range D).map fun i => ρ+oS+K*i) := by
  have he := compactReservation_axes h
  have he' : D = (backChunks d g K+compactReservationActive d g K D)+
      (CompactGlobalRowPadding.rowAxes NW m d+frontChunks d g K) := by omega
  conv_rhs => rw [he',range_add_map]
  exact (compactReservedPcs_vals K a oS (backChunks d g K) J
    (compactReservationActive d g K D) ρ).append (List.Perm.refl _)

end
end IntegerMultBounds.MathlibTM2.Fast
