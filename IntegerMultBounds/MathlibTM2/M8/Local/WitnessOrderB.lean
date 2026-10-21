module

public import IntegerMultBounds.MathlibTM2.M8.Local.FrameFlowB
public import IntegerMultBounds.MathlibTM2.M8.Local.WitnessB
public import IntegerMultBounds.MathlibTM2.M8.Local.SourceNodes
public import IntegerMultBounds.MathlibTM2.M8.Local.SlotCount
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Order00
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Order01
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Order02
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Order03
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Order04
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Order05
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Order06
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Order07
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Order08
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Order09
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Order10
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Order11
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Order12
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Order13
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Order14
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Order15
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.RootOrder

/-! Identify the complete local serving orders with the actual compiler.
The checks certify use membership locally; sorting and uniqueness are structural. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local
noncomputable section
open Classical

private theorem orderChunk (k : Nat) (t : Tree (Nat × List Use)) (ht : t.Perfect 4096)
    (hall : Tree.all bOrderOk (fun _ => true) nodeCount t (4096 * k) 4096 = true)
    (hget : ∀ i < 4096, bdata.get 65536 (4096 * k + i) = t.get 4096 i)
    (i : Nat) (hi : i < 4096) (hn : 4096 * k + i < nodeCount) :
    bOrderOk (4096 * k + i) (bAt (4096 * k + i)) = true := by
  rw [bAt, width, hget i hi]
  exact Tree.all_get _ _ _ t 4096 (4096 * k) ht hall i hi hn

theorem bOrderOk_at (n : Nat) (hn : n < nodeCount) : bOrderOk n (bAt n) = true := by
  have hn' : n < 64042 := hn
  obtain ⟨k, i, hi, rfl⟩ : ∃ k i, i < 4096 ∧ n = 4096 * k + i :=
    ⟨n / 4096, n % 4096, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4096).symm⟩
  have hk : k < 16 := by omega
  interval_cases k
  · exact orderChunk 0 bdata00 bdata00_perfect border00 bdata_get_00 i hi hn
  · exact orderChunk 1 bdata01 bdata01_perfect border01 bdata_get_01 i hi hn
  · exact orderChunk 2 bdata02 bdata02_perfect border02 bdata_get_02 i hi hn
  · exact orderChunk 3 bdata03 bdata03_perfect border03 bdata_get_03 i hi hn
  · exact orderChunk 4 bdata04 bdata04_perfect border04 bdata_get_04 i hi hn
  · exact orderChunk 5 bdata05 bdata05_perfect border05 bdata_get_05 i hi hn
  · exact orderChunk 6 bdata06 bdata06_perfect border06 bdata_get_06 i hi hn
  · exact orderChunk 7 bdata07 bdata07_perfect border07 bdata_get_07 i hi hn
  · exact orderChunk 8 bdata08 bdata08_perfect border08 bdata_get_08 i hi hn
  · exact orderChunk 9 bdata09 bdata09_perfect border09 bdata_get_09 i hi hn
  · exact orderChunk 10 bdata10 bdata10_perfect border10 bdata_get_10 i hi hn
  · exact orderChunk 11 bdata11 bdata11_perfect border11 bdata_get_11 i hi hn
  · exact orderChunk 12 bdata12 bdata12_perfect border12 bdata_get_12 i hi hn
  · exact orderChunk 13 bdata13 bdata13_perfect border13 bdata_get_13 i hi hn
  · exact orderChunk 14 bdata14 bdata14_perfect border14 bdata_get_14 i hi hn
  · exact orderChunk 15 bdata15 bdata15_perfect border15 bdata_get_15 i hi hn

theorem bOrderOk_parts (n : Nat) (hn : n < nodeCount) :
    ((bAt n).2.all (freeB n) = true ∧ (bAt n).2.Nodup) ∧
      (leafCount ≤ n → argumentOrderOk n false = true ∧ argumentOrderOk n true = true) := by
  have h := bOrderOk_at n hn
  unfold bOrderOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1.1, fun hv => ?_⟩
  simpa [Nat.ble_eq.mpr hv] using h.1.2

theorem free_use_in_order {n : Nat} {u : Use} (hu : u ∈ dagB.freeUses n) :
    u ∈ (bAt n).2 := by
  have hm := (dagB.mem_freeUses.mp hu).1
  cases u with
  | gate t pos =>
    obtain ⟨htN, ht, ha⟩ := (dagB.mem_uses_gate n t pos).mp hm
    have hd : (recAt t).donor pos = none :=
      (src_eq ht htN pos).2.mp (show dag.linkedB (.gate t pos) = false from
        (dagB.mem_freeUses.mp hu).2)
    have h := (bOrderOk_parts t htN).2 ht
    have hp : argumentOrderOk t pos = true := by cases pos <;> tauto
    simpa only [argumentOrderOk, show records.get width t = recAt t from rfl, hd,
      show (recAt t).arg pos = n from ha, List.contains_iff_mem] using hp
  | root j =>
    obtain ⟨hj, ha⟩ := (dagB.mem_uses_root n j).mp hm
    change j < rootCount at hj
    have h := Tree.all_get _ _ _ roots 8192 0 roots_perfect rootOrders j
      (by have : j < 5336 := hj; omega) (by simpa using hj)
    simpa only [Nat.zero_add, rootOrderOk, show rootWidth = 8192 from rfl,
      show (roots.get 8192 j).node = n from ha, List.contains_iff_mem] using h

/-- The stored serving list is the compiler's exact free-use order. -/
theorem dagB_freeUses_eq (n : Nat) (hn : n < nodeCount) :
    dagB.freeUses n = (bAt n).2 := by
  have h := (bOrderOk_parts n hn).1
  apply FrameFlow.freeUses_eq_order dagB n (bAt n).2 h.2
  · intro u
    exact ⟨free_use_in_order, fun hu => freeB_mem (List.all_eq_true.mp h.1 u hu)⟩
  · intro u
    rfl

theorem slotsBefore_zero : slotsBefore 0 = 0 := by decide +kernel

theorem slotsBefore_succ (n : Nat) (hn : n < nodeCount) :
    slotsBefore (n + 1) = slotsBefore n + ((bAt n).2.length - 1) +
      (if n < leafCount then 1 else 0) := by
  have h := bOrderOk_at n hn
  unfold bOrderOk at h
  simp only [Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.2

/-- The cached allocation counts are the actual compiler's next-slot counts. -/
theorem dagB_compileTo_next (n : Nat) (hn : n ≤ nodeCount) :
    (dagB.compileTo n).next = slotsBefore n := by
  induction n with
  | zero => simpa only [Dag.compileTo, List.range_zero, List.foldl_nil, Dag.start] using
      slotsBefore_zero.symm
  | succ n ih =>
    have hs : dagB.compileTo (n + 1) = dagB.step (dagB.compileTo n) n := by
      simp [Dag.compileTo, List.range_succ, List.foldl_append]
    rw [hs, dagB.step_next dagB_valid _ (by change n < nodeCount; omega), ih (by omega),
      dagB_freeUses_eq n (by omega), slotsBefore_succ n (by omega)]
    rfl

end
end IntegerMultBounds.MathlibTM2.M8.Local
