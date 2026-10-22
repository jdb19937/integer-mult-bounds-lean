module

public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Facts
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Slots00
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Slots01
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Slots02
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Slots03
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Slots04
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Slots05
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Slots06
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Slots07

/-! The checked readout-to-start boundary for every allocated slot. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB
noncomputable section
open Local

private theorem slotChunk (k : Nat) (t : Local.Tree Nat) (ht : t.Perfect 4096)
    (hall : Tree.all slotOk (fun _ => true) slotCount t (4096 * k) 4096 = true)
    (hget : ∀ i < 4096, slotTree.get 32768 (4096 * k + i) = t.get 4096 i)
    (i : Nat) (hi : i < 4096) (hn : 4096 * k + i < slotCount) :
    slotOk (4096 * k + i) (slotTree.get 32768 (4096 * k + i)) = true := by
  rw [hget i hi]
  exact Tree.all_get _ _ _ t 4096 (4096 * k) ht hall i hi hn

theorem slotOk_at (s : Nat) (hs : s < slotCount) : slotOk s (slotTree.get 32768 s) = true := by
  have hs' : s < 28866 := hs
  obtain ⟨k, i, hi, rfl⟩ : ∃ k i, i < 4096 ∧ s = 4096 * k + i :=
    ⟨s / 4096, s % 4096, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod s 4096).symm⟩
  have hk : k < 8 := by omega
  interval_cases k
  · exact slotChunk 0 slots00 slots00_perfect slots00_checked slotTree_get_00 i hi hs
  · exact slotChunk 1 slots01 slots01_perfect slots01_checked slotTree_get_01 i hi hs
  · exact slotChunk 2 slots02 slots02_perfect slots02_checked slotTree_get_02 i hi hs
  · exact slotChunk 3 slots03 slots03_perfect slots03_checked slotTree_get_03 i hi hs
  · exact slotChunk 4 slots04 slots04_perfect slots04_checked slotTree_get_04 i hi hs
  · exact slotChunk 5 slots05 slots05_perfect slots05_checked slotTree_get_05 i hi hs
  · exact slotChunk 6 slots06 slots06_perfect slots06_checked slotTree_get_06 i hi hs
  · exact slotChunk 7 slots07 slots07_perfect slots07_checked slotTree_get_07 i hi hs

theorem sigma_start_nested (s : Nat) (hs : s < slotCount) :
    Nested ((AssignmentB.sigmaLabel s).eval SignedFull.bankEntry)
      ((AssignmentB.startLabel s).eval SignedFull.bankEntry) := by
  have h := slotOk_at s hs
  unfold slotOk at h
  exact (List.isChain_cons_cons.mp (chainAt_path _ _ h)).1

theorem slotsBefore_final : slotsBefore nodeCount = slotCount := by decide +kernel

end
end IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB
