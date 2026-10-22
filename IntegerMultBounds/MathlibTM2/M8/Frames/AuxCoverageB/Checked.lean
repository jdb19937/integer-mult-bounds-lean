module

public import Mathlib.Tactic.IntervalCases
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Nodes00
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Nodes01
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Nodes02
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Nodes03
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Nodes04
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Nodes05
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Nodes06
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Nodes07
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Nodes08
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Nodes09
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Nodes10
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Nodes11
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Nodes12
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Nodes13
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Nodes14
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Nodes15
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Slots00
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Slots01
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Slots02
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Slots03
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Slots04
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Slots05
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Slots06
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Slots07
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Roots00
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Roots01
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Roots02
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Roots03
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Roots04
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Roots05
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Roots06
public import IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB.Checks.Roots07

/-! Generated canonical-chain membership facts. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB
noncomputable section
open Local

theorem nodeOk_at (n : Nat) (h : n < nodeCount) :
    nodeOk n (Local.SlotAssignmentB.argumentSlots.get 65536 n) = true := by
  have hb : n < 64042 := h
  obtain ⟨k, i, hi, rfl⟩ : ∃ k i, i < 4096 ∧ n = 4096 * k + i :=
    ⟨n / 4096, n % 4096, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4096).symm⟩
  have hk : k < 16 := by omega
  interval_cases k
  · rw [Local.SlotAssignmentB.argumentSlots_get_00 i hi]
    exact Tree.all_get _ _ _ Local.SlotAssignmentB.arguments00 4096 (4096 * 0)
      Local.SlotAssignmentB.arguments00_perfect arguments00_checked i hi h
  · rw [Local.SlotAssignmentB.argumentSlots_get_01 i hi]
    exact Tree.all_get _ _ _ Local.SlotAssignmentB.arguments01 4096 (4096 * 1)
      Local.SlotAssignmentB.arguments01_perfect arguments01_checked i hi h
  · rw [Local.SlotAssignmentB.argumentSlots_get_02 i hi]
    exact Tree.all_get _ _ _ Local.SlotAssignmentB.arguments02 4096 (4096 * 2)
      Local.SlotAssignmentB.arguments02_perfect arguments02_checked i hi h
  · rw [Local.SlotAssignmentB.argumentSlots_get_03 i hi]
    exact Tree.all_get _ _ _ Local.SlotAssignmentB.arguments03 4096 (4096 * 3)
      Local.SlotAssignmentB.arguments03_perfect arguments03_checked i hi h
  · rw [Local.SlotAssignmentB.argumentSlots_get_04 i hi]
    exact Tree.all_get _ _ _ Local.SlotAssignmentB.arguments04 4096 (4096 * 4)
      Local.SlotAssignmentB.arguments04_perfect arguments04_checked i hi h
  · rw [Local.SlotAssignmentB.argumentSlots_get_05 i hi]
    exact Tree.all_get _ _ _ Local.SlotAssignmentB.arguments05 4096 (4096 * 5)
      Local.SlotAssignmentB.arguments05_perfect arguments05_checked i hi h
  · rw [Local.SlotAssignmentB.argumentSlots_get_06 i hi]
    exact Tree.all_get _ _ _ Local.SlotAssignmentB.arguments06 4096 (4096 * 6)
      Local.SlotAssignmentB.arguments06_perfect arguments06_checked i hi h
  · rw [Local.SlotAssignmentB.argumentSlots_get_07 i hi]
    exact Tree.all_get _ _ _ Local.SlotAssignmentB.arguments07 4096 (4096 * 7)
      Local.SlotAssignmentB.arguments07_perfect arguments07_checked i hi h
  · rw [Local.SlotAssignmentB.argumentSlots_get_08 i hi]
    exact Tree.all_get _ _ _ Local.SlotAssignmentB.arguments08 4096 (4096 * 8)
      Local.SlotAssignmentB.arguments08_perfect arguments08_checked i hi h
  · rw [Local.SlotAssignmentB.argumentSlots_get_09 i hi]
    exact Tree.all_get _ _ _ Local.SlotAssignmentB.arguments09 4096 (4096 * 9)
      Local.SlotAssignmentB.arguments09_perfect arguments09_checked i hi h
  · rw [Local.SlotAssignmentB.argumentSlots_get_10 i hi]
    exact Tree.all_get _ _ _ Local.SlotAssignmentB.arguments10 4096 (4096 * 10)
      Local.SlotAssignmentB.arguments10_perfect arguments10_checked i hi h
  · rw [Local.SlotAssignmentB.argumentSlots_get_11 i hi]
    exact Tree.all_get _ _ _ Local.SlotAssignmentB.arguments11 4096 (4096 * 11)
      Local.SlotAssignmentB.arguments11_perfect arguments11_checked i hi h
  · rw [Local.SlotAssignmentB.argumentSlots_get_12 i hi]
    exact Tree.all_get _ _ _ Local.SlotAssignmentB.arguments12 4096 (4096 * 12)
      Local.SlotAssignmentB.arguments12_perfect arguments12_checked i hi h
  · rw [Local.SlotAssignmentB.argumentSlots_get_13 i hi]
    exact Tree.all_get _ _ _ Local.SlotAssignmentB.arguments13 4096 (4096 * 13)
      Local.SlotAssignmentB.arguments13_perfect arguments13_checked i hi h
  · rw [Local.SlotAssignmentB.argumentSlots_get_14 i hi]
    exact Tree.all_get _ _ _ Local.SlotAssignmentB.arguments14 4096 (4096 * 14)
      Local.SlotAssignmentB.arguments14_perfect arguments14_checked i hi h
  · rw [Local.SlotAssignmentB.argumentSlots_get_15 i hi]
    exact Tree.all_get _ _ _ Local.SlotAssignmentB.arguments15 4096 (4096 * 15)
      Local.SlotAssignmentB.arguments15_perfect arguments15_checked i hi h

theorem slotOk_at (s : Nat) (h : s < GeometryB.slotCount) :
    slotOk s (GeometryB.slotTree.get 32768 s) = true := by
  have hb : s < 28866 := h
  obtain ⟨k, i, hi, rfl⟩ : ∃ k i, i < 4096 ∧ s = 4096 * k + i :=
    ⟨s / 4096, s % 4096, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod s 4096).symm⟩
  have hk : k < 8 := by omega
  interval_cases k
  · rw [GeometryB.slotTree_get_00 i hi]
    exact Tree.all_get _ _ _ GeometryB.slots00 4096 (4096 * 0)
      GeometryB.slots00_perfect slots00_checked i hi h
  · rw [GeometryB.slotTree_get_01 i hi]
    exact Tree.all_get _ _ _ GeometryB.slots01 4096 (4096 * 1)
      GeometryB.slots01_perfect slots01_checked i hi h
  · rw [GeometryB.slotTree_get_02 i hi]
    exact Tree.all_get _ _ _ GeometryB.slots02 4096 (4096 * 2)
      GeometryB.slots02_perfect slots02_checked i hi h
  · rw [GeometryB.slotTree_get_03 i hi]
    exact Tree.all_get _ _ _ GeometryB.slots03 4096 (4096 * 3)
      GeometryB.slots03_perfect slots03_checked i hi h
  · rw [GeometryB.slotTree_get_04 i hi]
    exact Tree.all_get _ _ _ GeometryB.slots04 4096 (4096 * 4)
      GeometryB.slots04_perfect slots04_checked i hi h
  · rw [GeometryB.slotTree_get_05 i hi]
    exact Tree.all_get _ _ _ GeometryB.slots05 4096 (4096 * 5)
      GeometryB.slots05_perfect slots05_checked i hi h
  · rw [GeometryB.slotTree_get_06 i hi]
    exact Tree.all_get _ _ _ GeometryB.slots06 4096 (4096 * 6)
      GeometryB.slots06_perfect slots06_checked i hi h
  · rw [GeometryB.slotTree_get_07 i hi]
    exact Tree.all_get _ _ _ GeometryB.slots07 4096 (4096 * 7)
      GeometryB.slots07_perfect slots07_checked i hi h

theorem rootOk_at (j : Nat) (h : j < rootCount) :
    rootOk j (GeometryB.endpointTree.get 8192 j) = true := by
  have hb : j < 5336 := h
  obtain ⟨k, i, hi, rfl⟩ : ∃ k i, i < 1024 ∧ j = 1024 * k + i :=
    ⟨j / 1024, j % 1024, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod j 1024).symm⟩
  have hk : k < 8 := by omega
  interval_cases k
  · rw [GeometryB.endpointTree_get_00 i hi]
    exact Tree.all_get _ _ _ GeometryB.endpoints00 1024 (1024 * 0)
      GeometryB.endpoints00_perfect endpoints00_checked i hi h
  · rw [GeometryB.endpointTree_get_01 i hi]
    exact Tree.all_get _ _ _ GeometryB.endpoints01 1024 (1024 * 1)
      GeometryB.endpoints01_perfect endpoints01_checked i hi h
  · rw [GeometryB.endpointTree_get_02 i hi]
    exact Tree.all_get _ _ _ GeometryB.endpoints02 1024 (1024 * 2)
      GeometryB.endpoints02_perfect endpoints02_checked i hi h
  · rw [GeometryB.endpointTree_get_03 i hi]
    exact Tree.all_get _ _ _ GeometryB.endpoints03 1024 (1024 * 3)
      GeometryB.endpoints03_perfect endpoints03_checked i hi h
  · rw [GeometryB.endpointTree_get_04 i hi]
    exact Tree.all_get _ _ _ GeometryB.endpoints04 1024 (1024 * 4)
      GeometryB.endpoints04_perfect endpoints04_checked i hi h
  · rw [GeometryB.endpointTree_get_05 i hi]
    exact Tree.all_get _ _ _ GeometryB.endpoints05 1024 (1024 * 5)
      GeometryB.endpoints05_perfect endpoints05_checked i hi h
  · rw [GeometryB.endpointTree_get_06 i hi]
    exact Tree.all_get _ _ _ GeometryB.endpoints06 1024 (1024 * 6)
      GeometryB.endpoints06_perfect endpoints06_checked i hi h
  · rw [GeometryB.endpointTree_get_07 i hi]
    exact Tree.all_get _ _ _ GeometryB.endpoints07 1024 (1024 * 7)
      GeometryB.endpoints07_perfect endpoints07_checked i hi h
end
end IntegerMultBounds.MathlibTM2.M8.Frames.AuxCoverageB
