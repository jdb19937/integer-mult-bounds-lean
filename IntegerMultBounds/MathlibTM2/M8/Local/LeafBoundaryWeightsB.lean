module

public import IntegerMultBounds.MathlibTM2.M8.Local.BoundaryWeightsB

/-! Preservation of the combined observation boundary through leaf allocation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local.AdjointB
noncomputable section
open Classical

/-- Leaf serving assigns its uses exactly the consecutive newly allocated slots. -/
theorem leaf_served_weights (n : Nat) (us : List Use) (st : State) (hnd : us.Nodup)
    (c : Use → ZMod 2) (g : Reg →₀ ZMod 2)
    (hc : ∀ u ∈ us,
      c u = g (Reg.aux ((State.serve n st.next {st with next := st.next + 1, ops := st.ops ++ [.src st.next n]} us).pend u))) :
    (us.map fun u => Finsupp.single
      (Reg.aux ((State.serve n st.next {st with next := st.next + 1, ops := st.ops ++ [.src st.next n]} us).pend u)) (c u)).sum =
      ((List.range' st.next us.length).map fun s => Finsupp.single (Reg.aux s) (g (Reg.aux s))).sum := by
  have hm : us.map (fun u => Finsupp.single
      (Reg.aux ((State.serve n st.next {st with next := st.next + 1, ops := st.ops ++ [.src st.next n]} us).pend u)) (c u)) =
      us.map (fun u => Finsupp.single
      (Reg.aux ((State.serve n st.next {st with next := st.next + 1, ops := st.ops ++ [.src st.next n]} us).pend u))
        (g (Reg.aux ((State.serve n st.next {st with next := st.next + 1, ops := st.ops ++ [.src st.next n]} us).pend u)))) := by
    apply List.map_congr_left
    intro u hu
    rw [hc u hu]
  rw [hm]
  cases us with
  | nil => rfl
  | cons u us =>
    have hs := serve_observations n st.next u us {st with next := st.next + 1, ops := st.ops ++ [.src st.next n]} hnd
      (fun s => Finsupp.single (Reg.aux s) (g (Reg.aux s)))
    simpa only [List.length_cons, List.range'_succ, List.map_cons] using congrArg List.sum hs

/-- No pending use can be consumed by a leaf node. -/
theorem pending_live_leaf (D : Dag) (hv : D.Valid) (k : Nat) (hn : k < D.v)
    (u : Use) (hu : D.Pending k u) : Dag.Live (k + 1) u := by
  have hs := D.pending_mem_useSet hv hu
  cases u with
  | root r => trivial
  | gate t pos =>
    have ht := (D.mem_useSet_gate t pos).mp hs
    simp only [Dag.Live]
    omega

/-- The old frontier is unchanged by a leaf; its new part observes just the fresh slots. -/
theorem pendingWeights_step_leaf (D : Dag) (hv : D.Valid) (k : Nat) (hn : k < D.v)
    (st : State) (c : Use → ZMod 2) (g : Reg →₀ ZMod 2)
    (hc : ∀ u ∈ D.freeUses k, c u = g (Reg.aux ((D.step st k).pend u))) :
    D.pendingWeights (k + 1) (D.step st k) c = D.pendingWeights k st c +
      ((List.range' st.next (D.freeUses k).length).map
        fun s => Finsupp.single (Reg.aux s) (g (Reg.aux s))).sum := by
  have hk : k < D.N := lt_of_lt_of_le hn hv.v_le
  rw [D.pendingWeights_succ hv k hk, D.linkUse_none_of_lt hv hn]
  simp only [Option.toList_none, List.toFinset_nil, Finset.sum_empty, add_zero]
  have hfilter : (D.pendingUses k).filter (Dag.Live (k + 1)) = D.pendingUses k := by
    apply Finset.filter_eq_self.mpr
    intro u hu
    exact pending_live_leaf D hv k hn u ((D.mem_pendingUses hv k u).mp hu)
  rw [hfilter]
  congr 1
  · apply Finset.sum_congr rfl
    intro u hu
    rw [FrameFlow.step_pend_after_source D hv st k hk u
      (FrameFlow.pending_src_lt D hv ((D.mem_pendingUses hv k u).mp hu))]
  · rw [List.sum_toFinset _ (D.freeUses_nodup k)]
    have hpend : (D.step st k).pend =
        (State.serve k st.next {st with next := st.next + 1, ops := st.ops ++ [.src st.next k]} (D.freeUses k)).pend := by
      rw [Dag.step, ite_eq_left hn]
    simp only [hpend] at hc ⊢
    exact leaf_served_weights k (D.freeUses k) st (D.freeUses_nodup k) c g hc

/-- Leaf allocation preserves live observations plus all future garbage weights. -/
theorem boundaryWeights_step_leaf (D : Dag) (hv : D.Valid) (k : Nat) (hn : k < D.v)
    (st : State) (c : Use → ZMod 2) (g : Reg →₀ ZMod 2)
    (hc : ∀ u ∈ D.freeUses k, c u = g (Reg.aux ((D.step st k).pend u))) :
    boundaryWeights D (k + 1) (D.step st k) c g = boundaryWeights D k st c g := by
  have hnxt : (D.step st k).next = st.next + (D.freeUses k).length := by
    rw [Dag.step, ite_eq_left hn, (State.serve_ops _ _ _ _).2]
    have hpos := List.length_pos_iff.mpr (hv.free_ne k (lt_of_lt_of_le hn hv.v_le))
    dsimp only
    omega
  rw [boundaryWeights, pendingWeights_step_leaf D hv k hn st c g hc, hnxt,
    add_assoc, ← futureWeights_split, boundaryWeights]

/-- The combined observation is preserved when the leaf block is pulled back
through the already compiled prefix. -/
theorem boundary_pullOps_step_leaf (D : Dag) (hv : D.Valid) (k : Nat) (hn : k < D.v)
    (st : State) (c : Use → ZMod 2) (g : Reg →₀ ZMod 2)
    (hc : ∀ u ∈ D.freeUses k, c u = g (Reg.aux ((D.step st k).pend u))) :
    AuxEq (pullOps ((D.step st k).ops.map D.vop)
      (boundaryWeights D (k + 1) (D.step st k) c g))
      (pullOps (st.ops.map D.vop) (boundaryWeights D k st c g)) := by
  rw [boundaryWeights_step_leaf D hv k hn st c g hc]
  exact auxEq_step_leaf D st k hn _

end
end IntegerMultBounds.MathlibTM2.M8.Local.AdjointB
