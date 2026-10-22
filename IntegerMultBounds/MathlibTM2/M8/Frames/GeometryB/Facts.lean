module

public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Data
public import IntegerMultBounds.MathlibTM2.M8.Frames.SignedFull.LookupChecks
public import IntegerMultBounds.MathlibTM2.M8.Frames.SignedFull.BankChecks
public import IntegerMultBounds.MathlibTM2.M8.Frames.ChainLookupFacts
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Edges00
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Edges01
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Edges02
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Edges03
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Edges04
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Edges05
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Edges06
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Edges07
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Edges08
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Edges09
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Edges10
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Edges11
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Edges12
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Edges13
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Edges14
public import IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB.Checks.Edges15

/-! Discharge the compiler's incoming-frame and copy-chain obligations by
reusing ordered pairs in the already certified full chains. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB
noncomputable section
open Local

private theorem edgeChunk (k : Nat) (t : Local.Tree (Nat × Nat × Nat)) (ht : t.Perfect 4096)
    (hall : Tree.all nodeOk (fun _ => true) nodeCount t (4096 * k) 4096 = true)
    (hget : ∀ i < 4096, edges.get 65536 (4096 * k + i) = t.get 4096 i)
    (i : Nat) (hi : i < 4096) (hn : 4096 * k + i < nodeCount) :
    nodeOk (4096 * k + i) (edges.get 65536 (4096 * k + i)) = true := by
  rw [hget i hi]
  exact Tree.all_get _ _ _ t 4096 (4096 * k) ht hall i hi hn

theorem nodeOk_at (n : Nat) (hn : n < nodeCount) : nodeOk n (edges.get 65536 n) = true := by
  have hn' : n < 64042 := hn
  obtain ⟨k, i, hi, rfl⟩ : ∃ k i, i < 4096 ∧ n = 4096 * k + i :=
    ⟨n / 4096, n % 4096, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4096).symm⟩
  have hk : k < 16 := by omega
  interval_cases k
  · exact edgeChunk 0 edges00 edges00_perfect edges00_checked edges_get_00 i hi hn
  · exact edgeChunk 1 edges01 edges01_perfect edges01_checked edges_get_01 i hi hn
  · exact edgeChunk 2 edges02 edges02_perfect edges02_checked edges_get_02 i hi hn
  · exact edgeChunk 3 edges03 edges03_perfect edges03_checked edges_get_03 i hi hn
  · exact edgeChunk 4 edges04 edges04_perfect edges04_checked edges_get_04 i hi hn
  · exact edgeChunk 5 edges05 edges05_perfect edges05_checked edges_get_05 i hi hn
  · exact edgeChunk 6 edges06 edges06_perfect edges06_checked edges_get_06 i hi hn
  · exact edgeChunk 7 edges07 edges07_perfect edges07_checked edges_get_07 i hi hn
  · exact edgeChunk 8 edges08 edges08_perfect edges08_checked edges_get_08 i hi hn
  · exact edgeChunk 9 edges09 edges09_perfect edges09_checked edges_get_09 i hi hn
  · exact edgeChunk 10 edges10 edges10_perfect edges10_checked edges_get_10 i hi hn
  · exact edgeChunk 11 edges11 edges11_perfect edges11_checked edges_get_11 i hi hn
  · exact edgeChunk 12 edges12 edges12_perfect edges12_checked edges_get_12 i hi hn
  · exact edgeChunk 13 edges13 edges13_perfect edges13_checked edges_get_13 i hi hn
  · exact edgeChunk 14 edges14 edges14_perfect edges14_checked edges_get_14 i hi hn
  · exact edgeChunk 15 edges15 edges15_perfect edges15_checked edges_get_15 i hi hn

theorem nodeOk_parts (n : Nat) (hv : leafCount ≤ n) (hn : n < nodeCount) :
    (ChainLookup.pathCheck SignedFull.bankSize (SignedFull.chainAt (edges.get 65536 n).1)
      [AssignmentB.argumentLabel n false, AssignmentB.nodeLabel n] = true ∧
    ChainLookup.pathCheck SignedFull.bankSize (SignedFull.chainAt (edges.get 65536 n).2.1)
      [AssignmentB.argumentLabel n true, AssignmentB.nodeLabel n] = true) ∧
    ChainLookup.pathCheck SignedFull.bankSize (SignedFull.chainAt (edges.get 65536 n).2.2)
      (copyLabels n) = true := by
  have h := nodeOk_at n hn
  unfold nodeOk at h
  simpa only [ite_eq_right (Nat.not_lt.mpr hv), Bool.and_eq_true] using h

theorem chainAt_path (i : Nat) (frames : List Signed.Frame)
    (h : ChainLookup.pathCheck SignedFull.bankSize (SignedFull.chainAt i) frames = true) :
    List.IsChain Nested (frames.map (Signed.Frame.eval SignedFull.bankEntry)) :=
  ChainLookup.pathCheck_chain SignedFull.bankEntry SignedFull.bankSize
    (fun i _ => SignedFull.bankEntry_checked i) (SignedFull.chainAt i)
    (SignedFull.chainAt_checked i) frames h

theorem argument_nested (n : Nat) (hv : leafCount ≤ n) (hn : n < nodeCount) (pos : Bool) :
    Nested ((AssignmentB.argumentLabel n pos).eval SignedFull.bankEntry)
      ((AssignmentB.nodeLabel n).eval SignedFull.bankEntry) := by
  have h := (nodeOk_parts n hv hn).1
  have hp : ∃ i, ChainLookup.pathCheck SignedFull.bankSize (SignedFull.chainAt i)
      [AssignmentB.argumentLabel n pos, AssignmentB.nodeLabel n] = true := by
    cases pos
    · exact ⟨_, h.1⟩
    · exact ⟨_, h.2⟩
  obtain ⟨i, hi⟩ := hp
  exact (List.isChain_cons_cons.mp (chainAt_path i _ hi)).1

theorem copies_chain (n : Nat) (hv : leafCount ≤ n) (hn : n < nodeCount) :
    List.IsChain Nested ((AssignmentB.nodeLabel n).eval SignedFull.bankEntry ::
      (List.range' (slotsBefore n) ((bAt n).2.length - 1)).map
        fun s => (AssignmentB.startLabel s).eval SignedFull.bankEntry) := by
  have h := chainAt_path _ _ (nodeOk_parts n hv hn).2
  simpa only [copyLabels, List.map_cons, List.map_map, Function.comp_def] using h

end
end IntegerMultBounds.MathlibTM2.M8.Frames.GeometryB
