module

public import IntegerMultBounds.MathlibTM2.M8.Local.WordB

/-! Phase ordering preserves the complete operation multiset. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local.Dag
noncomputable section
open Classical

theorem source_phases_perm (D : Dag) (pl : BPlan) : (D.vNow pl ++ D.vLate pl).Perm D.srcB := by
  unfold vNow vLate keyedOps
  exact (List.Perm.append (List.mergeSort_perm _ _) (List.mergeSort_perm _ _)).trans
    (List.perm_append_comm.trans (List.filter_append_perm _ _))

theorem orderedOps_perm (D : Dag) (pl : BPlan) :
    (D.vNow pl ++ D.vLate pl ++ D.opsFirst pl ++ D.opsRest pl).Perm D.opsB := by
  have hs : (D.opsFirst pl ++ D.opsRest pl).Perm D.sideB := List.filter_append_perm _ _
  have hp := (source_phases_perm D pl).append hs
  have ht : (D.srcB ++ D.sideB).Perm D.opsB := List.filter_append_perm _ _
  simpa only [List.append_assoc] using hp.trans ht

end
end IntegerMultBounds.MathlibTM2.M8.Local.Dag
