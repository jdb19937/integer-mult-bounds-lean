module

public import Mathlib.Tactic.IntervalCases
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.RootData
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Endpoints00
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Endpoints01
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Endpoints02
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Endpoints03
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Endpoints04
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Endpoints05
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Endpoints06
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Endpoints07

/-! Every concrete compiler root has a checked endpoint witness. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB
noncomputable section
open Local

private theorem rootChunk (k : Nat) (t : Tree (Nat × Nat)) (ht : t.Perfect 1024)
    (hall : Tree.all rootOk (fun _ => true) rootCount t (1024 * k) 1024 = true)
    (hget : ∀ i < 1024, endpointTree.get 8192 (1024 * k + i) = t.get 1024 i)
    (i : Nat) (hi : i < 1024) (hn : 1024 * k + i < rootCount) :
    rootOk (1024 * k + i) (endpointTree.get 8192 (1024 * k + i)) = true := by
  rw [hget i hi]
  exact Tree.all_get _ _ _ t 1024 (1024 * k) ht hall i hi hn

theorem rootOk_at (j : Nat) (hj : j < rootCount) :
    rootOk j (endpointTree.get 8192 j) = true := by
  have hj' : j < 5336 := hj
  obtain ⟨k, i, hi, rfl⟩ : ∃ k i, i < 1024 ∧ j = 1024 * k + i :=
    ⟨j / 1024, j % 1024, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod j 1024).symm⟩
  have hk : k < 8 := by omega
  interval_cases k
  · exact rootChunk 0 endpoints00 endpoints00_perfect endpoints00_checked endpointTree_get_00 i hi hj
  · exact rootChunk 1 endpoints01 endpoints01_perfect endpoints01_checked endpointTree_get_01 i hi hj
  · exact rootChunk 2 endpoints02 endpoints02_perfect endpoints02_checked endpointTree_get_02 i hi hj
  · exact rootChunk 3 endpoints03 endpoints03_perfect endpoints03_checked endpointTree_get_03 i hi hj
  · exact rootChunk 4 endpoints04 endpoints04_perfect endpoints04_checked endpointTree_get_04 i hi hj
  · exact rootChunk 5 endpoints05 endpoints05_perfect endpoints05_checked endpointTree_get_05 i hi hj
  · exact rootChunk 6 endpoints06 endpoints06_perfect endpoints06_checked endpointTree_get_06 i hi hj
  · exact rootChunk 7 endpoints07 endpoints07_perfect endpoints07_checked endpointTree_get_07 i hi hj

end
end IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB
