module

public import IntegerMultBounds.MathlibTM2.M8.Local.FrameFlowB
public import IntegerMultBounds.MathlibTM2.M8.Local.SlotCount

/-! The V-source list is exactly the consecutive fresh slots of the leaves. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local
noncomputable section
open Classical

namespace Dag

/-- Source operations contributed by a leaf's allocated slots. -/
def sourceBlock (D : Dag) (n : Nat) : List Op :=
  (List.range' (D.compileTo n).next (D.freeUses n).length).map (fun s => .src s n)

theorem copies_sources (D : Dag) (p n : Nat) (fs : List Nat) :
    ((copies p fs n).map D.vop).filter Op.isSrc =
      if n < D.v then fs.map (fun s => .src s n) else [] := by
  induction fs with
  | nil => simp [copies]
  | cons s fs ih =>
    change (D.vop (.copy p s n) :: (copies p fs n).map D.vop).filter Op.isSrc = _
    by_cases hn : n < D.v <;> simp only [vop, hn, ite_true, ite_false,
      List.filter_cons, Op.isSrc, Bool.false_eq_true, ih, List.map_cons]

theorem step_sources (D : Dag) (hv : D.Valid) (st : State) (n : Nat) (hn : n < D.N) :
    ((D.step st n).ops.map D.vop).filter Op.isSrc =
      (st.ops.map D.vop).filter Op.isSrc ++
        if n < D.v then (List.range' st.next (D.freeUses n).length).map (fun s => .src s n) else [] := by
  by_cases hleaf : n < D.v
  · rw [step, ite_eq_left hleaf, (State.serve_ops _ _ _ _).1]
    simp only [List.map_append, List.filter_append, copies_sources, ite_eq_left hleaf,
      List.map_singleton, vop, List.filter_cons, Op.isSrc, List.filter_nil,
      ite_true, List.append_assoc]
    have hlen := D.freeUses_length_pos hv hn
    obtain ⟨k, hk⟩ : ∃ k, (D.freeUses n).length = k + 1 := ⟨(D.freeUses n).length - 1, by omega⟩
    rw [hk]
    simp only [Nat.add_sub_cancel, List.range'_succ, List.map_cons, List.singleton_append]
  · obtain ⟨p, o, st', _, _, hops, hnext, hstep⟩ :=
      FrameFlow.step_internal_shape D n (Nat.le_of_not_gt hleaf) st
    rw [hstep, (State.serve_ops _ _ _ _).1, List.map_append, List.filter_append,
      copies_sources, ite_eq_right hleaf, List.append_nil, hops]
    simp [List.map_append, List.filter_append, vop, Op.isSrc, hleaf]

/-- Source extraction commutes with the compiler loop; internal nodes add no sources. -/
theorem compileTo_sources (D : Dag) (hv : D.Valid) : ∀ k, k ≤ D.N →
    ((D.compileTo k).ops.map D.vop).filter Op.isSrc =
      ((List.range k).filter fun n => decide (n < D.v)).flatMap D.sourceBlock := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have he : D.compileTo (k + 1) = D.step (D.compileTo k) k := by
      simp only [compileTo, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [he, step_sources D hv _ k (by omega), ih (by omega)]
    simp only [List.range_succ, List.filter_append, List.flatMap_append]
    by_cases hleaf : k < D.v <;> simp [hleaf, sourceBlock]

/-- Filtering a longer initial interval at a shorter endpoint gives that interval. -/
theorem filter_range_lt (v N : Nat) (hv : v ≤ N) :
    (List.range N).filter (fun n => decide (n < v)) = List.range v := by
  have he : N = v + (N - v) := by omega
  rw [he, List.range_add, List.filter_append]
  have hfirst : (List.range v).filter (fun n => decide (n < v)) = List.range v :=
    List.filter_eq_self.mpr (fun n hn => by simpa using List.mem_range.mp hn)
  have hrest : ((List.range (N - v)).map (v + ·)).filter (fun n => decide (n < v)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro n hn
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hn
    simp
  rw [hfirst, hrest, List.append_nil]

/-- The complete source list consists of the leaf allocation blocks. -/
theorem srcB_eq_sourceBlocks (D : Dag) (hv : D.Valid) :
    D.srcB = (List.range D.v).flatMap D.sourceBlock := by
  rw [srcB, opsB, compile, compileTo_sources D hv D.N le_rfl,
    filter_range_lt D.v D.N hv.v_le]

/-- Source targets are unique because every source is fresh at its occurrence. -/
theorem srcB_targets_nodup (D : Dag) (hv : D.Valid) : (D.srcB.map Op.target).Nodup := by
  change (D.srcB.map Op.target).Pairwise (· ≠ ·)
  rw [List.pairwise_map]
  have h := (D.opsB_fresh hv).filter Op.isSrc
  apply h.imp_of_mem
  intro a b ha hb hab
  have ha := (List.mem_filter.mp ha).2
  have hb := (List.mem_filter.mp hb).2
  cases a with
  | src s n =>
    cases b with
    | src t m =>
      intro he
      exact (hab t m rfl) (by simpa only [Op.slots, List.mem_singleton, Op.target] using he.symm)
    | add | copy => simp [Op.isSrc] at hb
  | add | copy => simp [Op.isSrc] at ha

/-- Extracting one leaf from disjoint source blocks keeps exactly that block. -/
theorem sourceBlocks_leaf_targets (blocks : Nat → List Nat) (ns : List Nat) (hnd : ns.Nodup)
    (n : Nat) :
    (((ns.flatMap fun i => (blocks i).map (fun s => Op.src s i)).filter
      fun op => decide (op.node = n)).map Op.target) = if n ∈ ns then blocks n else [] := by
  have hblock (i : Nat) :
      (((blocks i).map (fun s => Op.src s i)).filter fun op => decide (op.node = n)).map Op.target =
        if i = n then blocks i else [] := by
    by_cases hi : i = n <;> simp [List.filter_map, Op.node, Op.target, hi, Function.comp_def]
  induction ns with
  | nil => simp
  | cons i ns ih =>
    rw [List.flatMap_cons, List.filter_append, List.map_append, hblock, ih hnd.tail]
    by_cases hi : i = n
    · subst i
      simp [(List.nodup_cons.mp hnd).1]
    · simp [hi, Ne.symm hi]

/-- One leaf's actual source targets are precisely its fresh allocation interval. -/
theorem srcB_leaf_targets (D : Dag) (hv : D.Valid) (n : Nat) (hn : n < D.v) :
    ((D.srcB.filter fun op => decide (op.node = n)).map Op.target) =
      List.range' (D.compileTo n).next (D.freeUses n).length := by
  rw [srcB_eq_sourceBlocks D hv]
  change (((List.range D.v).flatMap fun i =>
    (List.range' (D.compileTo i).next (D.freeUses i).length).map (fun s => Op.src s i)).filter
      (fun op => decide (op.node = n))).map Op.target = _
  simpa only [List.mem_range, ite_eq_left hn] using
    sourceBlocks_leaf_targets (fun i => List.range' (D.compileTo i).next (D.freeUses i).length)
      (List.range D.v) List.nodup_range n

end Dag
end
end IntegerMultBounds.MathlibTM2.M8.Local
