module

public import IntegerMultBounds.MathlibTM2.M8.Frames.SuppRank
public import IntegerMultBounds.MathlibTM2.M8.Local.Witness
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Rank00
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Rank01
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Rank02
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Rank03
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Rank04
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Rank05
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Rank06
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Rank07
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Rank08
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Rank09
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Rank10
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Rank11
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Rank12
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Rank13
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Rank14
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Rank15

/-!
# The ranks of the node frames

The rank of every node frame is its entry of the table `dims` (`nodeFrame_rank`): the checks of
`Checks/Rank*` pass `rankOk` at every node, and a passed check is the rank by
`Frames.suppFrame_rank`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Global

open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames

noncomputable section

theorem pointOf_eq (s : Supp) : pointOf s = s.point := by cases s <;> rfl

theorem rankOk_spec {n : ℕ} (hn : n < nodeCount) (h : rankOk dims n (recAt n) = true) :
    (nodeFrame n).rank = dims.get width n := by
  unfold rankOk at h
  rw [pointOf_eq] at h
  split at h
  · next M hM =>
    rw [Bool.and_eq_true, beq_iff] at h
    rw [nodeFrame, suppFrame_rank (recOk_at n hn) hM h.1, h.2]
  · cases h

private theorem rankChunk (k : ℕ) (t : Local.Tree NodeRec) (ht : t.Perfect 4096)
    (hall : Tree.all (rankOk dims) (fun _ => true) nodeCount t (4096 * k) 4096 = true)
    (hget : ∀ i < 4096, records.get 65536 (4096 * k + i) = t.get 4096 i)
    (i : ℕ) (hi : i < 4096) (hn : 4096 * k + i < nodeCount) :
    rankOk dims (4096 * k + i) (recAt (4096 * k + i)) = true := by
  rw [recAt, width, hget i hi]
  exact Local.Tree.all_get _ _ _ t 4096 (4096 * k) ht hall i hi hn

/-- **The rank of a node frame** is its table entry. -/
theorem nodeFrame_rank {n : ℕ} (hn : n < nodeCount) : (nodeFrame n).rank = dims.get width n := by
  refine rankOk_spec hn ?_
  have hn' : n < 64042 := hn
  obtain ⟨k, i, hi, rfl⟩ : ∃ k i, i < 4096 ∧ n = 4096 * k + i :=
    ⟨n / 4096, n % 4096, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4096).symm⟩
  have hk : k < 16 := by omega
  interval_cases k
  · exact rankChunk 0 rec00 rec00_perfect rank00 records_get_00 i hi hn
  · exact rankChunk 1 rec01 rec01_perfect rank01 records_get_01 i hi hn
  · exact rankChunk 2 rec02 rec02_perfect rank02 records_get_02 i hi hn
  · exact rankChunk 3 rec03 rec03_perfect rank03 records_get_03 i hi hn
  · exact rankChunk 4 rec04 rec04_perfect rank04 records_get_04 i hi hn
  · exact rankChunk 5 rec05 rec05_perfect rank05 records_get_05 i hi hn
  · exact rankChunk 6 rec06 rec06_perfect rank06 records_get_06 i hi hn
  · exact rankChunk 7 rec07 rec07_perfect rank07 records_get_07 i hi hn
  · exact rankChunk 8 rec08 rec08_perfect rank08 records_get_08 i hi hn
  · exact rankChunk 9 rec09 rec09_perfect rank09 records_get_09 i hi hn
  · exact rankChunk 10 rec10 rec10_perfect rank10 records_get_10 i hi hn
  · exact rankChunk 11 rec11 rec11_perfect rank11 records_get_11 i hi hn
  · exact rankChunk 12 rec12 rec12_perfect rank12 records_get_12 i hi hn
  · exact rankChunk 13 rec13 rec13_perfect rank13 records_get_13 i hi hn
  · exact rankChunk 14 rec14 rec14_perfect rank14 records_get_14 i hi hn
  · exact rankChunk 15 rec15 rec15_perfect rank15 records_get_15 i hi hn

theorem dims_le {n : ℕ} (hn : n < nodeCount) : dims.get width n ≤ 23 := by
  rw [← nodeFrame_rank hn]
  exact (Matrix.rank_le_card_width _).trans_eq (Fintype.card_fin 23)

end

end IntegerMultBounds.MathlibTM2.M8.Global
