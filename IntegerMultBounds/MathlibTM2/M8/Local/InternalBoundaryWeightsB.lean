module

public import IntegerMultBounds.MathlibTM2.M8.Local.LeafBoundaryWeightsB

/-! The live boundary of an addition consists of survivors and its two arguments. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local.AdjointB
noncomputable section
open Classical

/-- Observations of uses that survive the current node. -/
def survivorWeights (D : Dag) (k : Nat) (st : State) (c : Use → ZMod 2) : Reg →₀ ZMod 2 :=
  ∑ u ∈ (D.pendingUses k).filter (Dag.Live (k + 1)),
    Finsupp.single (Reg.aux (st.pend u)) (c u)

/-- Exactly the two arguments disappear from an internal node's old frontier. -/
theorem pendingUses_consumed (D : Dag) (hv : D.Valid) (k : Nat)
    (hn : D.v ≤ k) (hk : k < D.N) :
    (D.pendingUses k).filter (fun u => ¬Dag.Live (k + 1) u) =
      {Use.gate k false, Use.gate k true} := by
  ext u
  simp only [Finset.mem_filter, D.mem_pendingUses hv, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hp, hl⟩
    cases u with
    | root r => exact (hl trivial).elim
    | gate t pos =>
      have ht := hp.1
      simp only [Dag.Live] at ht hl
      have he : t = k := by omega
      subst t
      cases pos <;> simp
  · rintro (rfl | rfl)
    · exact ⟨D.pending_arg hv hn hk false, by simp [Dag.Live]⟩
    · exact ⟨D.pending_arg hv hn hk true, by simp [Dag.Live]⟩

/-- The old boundary separates into survivors and the two operand observations. -/
theorem pendingWeights_internal (D : Dag) (hv : D.Valid) (k : Nat)
    (hn : D.v ≤ k) (hk : k < D.N) (st : State) (c : Use → ZMod 2) :
    D.pendingWeights k st c = survivorWeights D k st c +
      (Finsupp.single (Reg.aux (st.pend (.gate k false))) (c (.gate k false)) +
       Finsupp.single (Reg.aux (st.pend (.gate k true))) (c (.gate k true))) := by
  have hs := Finset.sum_filter_add_sum_filter_not (D.pendingUses k)
    (Dag.Live (k + 1)) (fun u => Finsupp.single (Reg.aux (st.pend u)) (c u))
  rw [pendingUses_consumed D hv k hn hk] at hs
  simpa [Dag.pendingWeights, survivorWeights] using hs.symm

/-- Surviving uses keep their slot assignments, even across linked allocation. -/
theorem survivorWeights_step (D : Dag) (hv : D.Valid) (k : Nat) (hk : k < D.N)
    (st : State) (c : Use → ZMod 2) :
    survivorWeights D k (D.step st k) c = survivorWeights D k st c := by
  apply Finset.sum_congr rfl
  intro u hu
  obtain ⟨hu, _⟩ := Finset.mem_filter.mp hu
  rw [FrameFlow.step_pend_after_source D hv st k hk u
    (FrameFlow.pending_src_lt D hv ((D.mem_pendingUses hv k u).mp hu))]

/-- Neither consumed argument slot contributes a surviving-use observation. -/
theorem survivorWeights_argument (D : Dag) (hv : D.Valid) (k : Nat)
    (hn : D.v ≤ k) (hk : k < D.N) (st : State) (c : Use → ZMod 2)
    (hinj : ∀ u v, D.Pending k u → D.Pending k v → st.pend u = st.pend v → u = v)
    (pos : Bool) : survivorWeights D k st c (Reg.aux (st.pend (.gate k pos))) = 0 := by
  simp only [survivorWeights, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro u hu
  obtain ⟨hu, hl⟩ := Finset.mem_filter.mp hu
  have he : st.pend u ≠ st.pend (.gate k pos) := by
    intro he
    have hu' := hinj u (.gate k pos) ((D.mem_pendingUses hv k u).mp hu)
      (D.pending_arg hv hn hk pos) he
    subst u
    simp [Dag.Live] at hl
  simp [he]

/-- Only non-kept free uses consume fresh garbage weights in an internal serving block. -/
theorem internal_served_weights (n p : Nat) (u : Use) (us : List Use) (st : State)
    (hnd : (u :: us).Nodup) (c : Use → ZMod 2) (g : Reg →₀ ZMod 2)
    (hc : ∀ v ∈ us, c v = g (Reg.aux ((State.serve n p st (u :: us)).pend v))) :
    ((u :: us).map fun v => Finsupp.single
      (Reg.aux ((State.serve n p st (u :: us)).pend v)) (c v)).sum =
      Finsupp.single (Reg.aux p) (c u) +
        ((List.range' st.next us.length).map fun s => Finsupp.single (Reg.aux s) (g (Reg.aux s))).sum := by
  have hp := FrameFlow.serve_pend_index n p (u :: us) st hnd 0 (by simp)
  simp only [List.getElem_cons_zero, ite_true] at hp
  rw [List.map_cons, List.sum_cons, hp]
  congr 1
  have hm : us.map (fun v => Finsupp.single
      (Reg.aux ((State.serve n p st (u :: us)).pend v)) (c v)) =
      us.map (fun v => Finsupp.single
      (Reg.aux ((State.serve n p st (u :: us)).pend v))
        (g (Reg.aux ((State.serve n p st (u :: us)).pend v)))) := by
    apply List.map_congr_left
    intro v hv
    rw [hc v hv]
  rw [hm]
  exact congrArg List.sum (serveRest_observations n p us (st.assign p u)
    (List.nodup_cons.mp hnd).2 (fun s => Finsupp.single (Reg.aux s) (g (Reg.aux s))))

/-- In an unlinked addition, transferring fresh-slot garbage leaves only the kept
use, surviving uses and future garbage at the post-node boundary. -/
theorem boundaryWeights_unlinked_shape (D : Dag) (hv : D.Valid) (k : Nat)
    (hn : D.v ≤ k) (hk : k < D.N) (hl : D.link k = none)
    (st : State) (u : Use) (us : List Use) (hu : D.freeUses k = u :: us)
    (c : Use → ZMod 2) (g : Reg →₀ ZMod 2)
    (hc : ∀ v ∈ us, c v = g (Reg.aux ((D.step st k).pend v))) :
    boundaryWeights D (k + 1) (D.step st k) c g =
      survivorWeights D k st c +
        Finsupp.single (Reg.aux (st.pend (.gate k false))) (c u) + futureWeights st.next g := by
  let pre : State := {st with ops := st.ops ++
    [.add (st.pend (.gate k false)) (st.pend (.gate k true)) k]}
  have hstep : D.step st k = State.serve k (st.pend (.gate k false)) pre (u :: us) := by
    simp [Dag.step, Nat.not_lt.mpr hn, hl, hu, pre]
  have hnd : (u :: us).Nodup := hu ▸ D.freeUses_nodup k
  have hnext : (D.step st k).next = st.next + us.length := by
    rw [hstep, (State.serve_ops _ _ _ _).2]
    simp [pre]
  have hf : (∑ v ∈ (D.freeUses k).toFinset,
      Finsupp.single (Reg.aux ((D.step st k).pend v)) (c v)) =
      Finsupp.single (Reg.aux (st.pend (.gate k false))) (c u) +
        ((List.range' st.next us.length).map
          fun s => Finsupp.single (Reg.aux s) (g (Reg.aux s))).sum := by
    rw [List.sum_toFinset _ (D.freeUses_nodup k), hu, hstep]
    have hc' := hc
    rw [hstep] at hc'
    exact internal_served_weights k _ u us pre hnd c g hc'
  have hlink : D.linkUse k = none := by simp [Dag.linkUse, hl]
  rw [boundaryWeights, D.pendingWeights_succ hv k hk, hlink]
  simp only [Option.toList_none, List.toFinset_nil, Finset.sum_empty, add_zero]
  change survivorWeights D k (D.step st k) c + _ + _ = _
  rw [survivorWeights_step D hv k hk, hf, hnext]
  calc
    _ = survivorWeights D k st c +
        Finsupp.single (Reg.aux (st.pend (.gate k false))) (c u) +
          (((List.range' st.next us.length).map
            fun s => Finsupp.single (Reg.aux s) (g (Reg.aux s))).sum +
            futureWeights (st.next + us.length) g) := by ac_rfl
    _ = _ := by rw [← futureWeights_split]

/-- Unlinked additions preserve the combined boundary under the node-weight
recurrence. No clean-register assumption is imposed on the proposed garbage. -/
theorem boundary_pullOps_step_unlinked (D : Dag) (hv : D.Valid) (k : Nat)
    (hn : D.v ≤ k) (hk : k < D.N) (hl : D.link k = none)
    (st : State) (hi : D.Inv (fun _ => 0) k st)
    (u : Use) (us : List Use) (hu : D.freeUses k = u :: us)
    (c : Use → ZMod 2) (g : Reg →₀ ZMod 2)
    (hc : ∀ v ∈ us, c v = g (Reg.aux ((D.step st k).pend v)))
    (ha : ∀ pos, c (.gate k pos) = ((D.freeUses k).map c).sum) :
    pullOps ((D.step st k).ops.map D.vop)
      (boundaryWeights D (k + 1) (D.step st k) c g) =
      pullOps (st.ops.map D.vop) (boundaryWeights D k st c g) := by
  let p := st.pend (.gate k false)
  let q := st.pend (.gate k true)
  let w := boundaryWeights D (k + 1) (D.step st k) c g
  let b := ((D.freeUses k).map c).sum
  have hp : p < st.next := hi.slot_lt _ (D.pending_arg hv hn hk false)
  have hsp : survivorWeights D k st c (Reg.aux p) = 0 :=
    survivorWeights_argument D hv k hn hk st c hi.inj false
  have hshape := boundaryWeights_unlinked_shape D hv k hn hk hl st u us hu c g hc
  change w = survivorWeights D k st c + Finsupp.single (Reg.aux p) (c u) +
    futureWeights st.next g at hshape
  have hwp : w (Reg.aux p) = c u := by
    rw [hshape]
    simp [hsp, Nat.not_le.mpr hp]
  let pre : State := {st with ops := st.ops ++ [.add p q k]}
  have hstep : D.step st k = State.serve k p pre (u :: us) := by
    simp [Dag.step, Nat.not_lt.mpr hn, hl, hu, pre, p, q]
  have hnd : (u :: us).Nodup := hu ▸ D.freeUses_nodup k
  have hcoef : ∀ v ∈ u :: us, w (Reg.aux ((State.serve k p pre (u :: us)).pend v)) = c v := by
    intro v hv'
    have hf : v ∈ D.freeUses k := by rwa [hu]
    have hpend : D.Pending (k + 1) v :=
      (D.pending_succ_iff hv k v).mpr (Or.inr (Or.inl hf))
    have hi' := D.inv_step hv (fun _ => 0) hk hi
    rw [← hstep]
    change (D.pendingWeights (k + 1) (D.step st k) c +
      futureWeights (D.step st k).next g) (Reg.aux ((D.step st k).pend v)) = c v
    rw [Finsupp.add_apply, D.pendingWeights_at hv _ _ c hi'.inj v hpend]
    simp [Nat.not_le.mpr (hi'.slot_lt v hpend)]
  have hsum : c u + ((List.range' st.next us.length).map fun f => w (Reg.aux f)).sum = b := by
    have hs := served_observation_sum k p u us pre hnd w c hcoef
    rw [hwp] at hs
    simpa only [pre, hu, b] using hs
  have hcopy : w + Finsupp.single (Reg.aux p)
      (((List.range' st.next us.length).map fun f => w (Reg.aux f)).sum) =
      survivorWeights D k st c + Finsupp.single (Reg.aux p) b + futureWeights st.next g := by
    calc
      _ = (survivorWeights D k st c + Finsupp.single (Reg.aux p) (c u) +
          futureWeights st.next g) + Finsupp.single (Reg.aux p)
          (((List.range' st.next us.length).map fun f => w (Reg.aux f)).sum) := by rw [hshape]
      _ = survivorWeights D k st c + Finsupp.single (Reg.aux p)
          (c u + ((List.range' st.next us.length).map fun f => w (Reg.aux f)).sum) +
          futureWeights st.next g := by rw [Finsupp.single_add]; ac_rfl
      _ = _ := by rw [hsum]
  have hweight : (survivorWeights D k st c + Finsupp.single (Reg.aux p) b +
      futureWeights st.next g) (Reg.aux p) = b := by simp [hsp, Nat.not_le.mpr hp]
  rw [pullOps_step_unlinked D st k hn hl hp]
  change pullOps (st.ops.map D.vop) (pullOp (.add p q k)
    (w + Finsupp.single (Reg.aux p)
      (((List.range' st.next ((D.freeUses k).length - 1)).map fun f => w (Reg.aux f)).sum))) = _
  simp only [hu, List.length_cons, Nat.add_sub_cancel] 
  rw [hcopy, pullOp, pullAdd, hweight]
  congr 1
  rw [boundaryWeights, pendingWeights_internal D hv k hn hk st c, ha false, ha true]
  change _ = (survivorWeights D k st c +
    (Finsupp.single (Reg.aux p) b + Finsupp.single (Reg.aux q) b)) + futureWeights st.next g
  ac_rfl

/-- Algebra of a node boundary: the pivot's served sum propagates to both
operands, while a retained observation stays on the other operand. -/
theorem pull_node_boundary (p q n next : Nat) (hp : p < next) (hpq : p ≠ q)
    (S w g : Reg →₀ ZMod 2) (a b d : ZMod 2) (fs : List Nat)
    (hsp : S (Reg.aux p) = 0)
    (hshape : w = S + Finsupp.single (Reg.aux p) a +
      Finsupp.single (Reg.aux q) d + futureWeights next g)
    (hsum : a + (fs.map fun f => w (Reg.aux f)).sum = b) :
    pullOp (.add p q n) (w + Finsupp.single (Reg.aux p)
      ((fs.map fun f => w (Reg.aux f)).sum)) =
      S + Finsupp.single (Reg.aux p) b + Finsupp.single (Reg.aux q) (b + d) +
        futureWeights next g := by
  have hcopy : w + Finsupp.single (Reg.aux p) ((fs.map fun f => w (Reg.aux f)).sum) =
      S + Finsupp.single (Reg.aux p) b + Finsupp.single (Reg.aux q) d + futureWeights next g := by
    calc
      _ = (S + Finsupp.single (Reg.aux p) a + Finsupp.single (Reg.aux q) d +
          futureWeights next g) + Finsupp.single (Reg.aux p)
          ((fs.map fun f => w (Reg.aux f)).sum) := by rw [hshape]
      _ = S + Finsupp.single (Reg.aux p) (a + (fs.map fun f => w (Reg.aux f)).sum) +
          Finsupp.single (Reg.aux q) d + futureWeights next g := by
            rw [Finsupp.single_add]; ac_rfl
      _ = _ := by rw [hsum]
  have hweight : (S + Finsupp.single (Reg.aux p) b + Finsupp.single (Reg.aux q) d +
      futureWeights next g) (Reg.aux p) = b := by
    simp [hsp, hpq, Nat.not_le.mpr hp]
  rw [hcopy, pullOp, pullAdd, hweight, Finsupp.single_add]
  simp only [add_assoc, add_comm, add_left_comm]

/-- Linked serving leaves the linked observation on the retained operand slot. -/
theorem boundaryWeights_linked_shape (D : Dag) (hv : D.Valid) (k : Nat)
    (hn : D.v ≤ k) (hk : k < D.N) (o : Bool) (t : Nat) (pos : Bool)
    (hl : D.link k = some (o, t, pos)) (st : State)
    (u : Use) (us : List Use) (hu : D.freeUses k = u :: us)
    (c : Use → ZMod 2) (g : Reg →₀ ZMod 2)
    (hc : ∀ v ∈ us, c v = g (Reg.aux ((D.step st k).pend v))) :
    let p := if o then st.pend (.gate k false) else st.pend (.gate k true)
    let q := if o then st.pend (.gate k true) else st.pend (.gate k false)
    boundaryWeights D (k + 1) (D.step st k) c g =
      survivorWeights D k st c + Finsupp.single (Reg.aux p) (c u) +
        Finsupp.single (Reg.aux q) (c (.gate t pos)) + futureWeights st.next g := by
  dsimp only
  let p := if o then st.pend (.gate k false) else st.pend (.gate k true)
  let q := if o then st.pend (.gate k true) else st.pend (.gate k false)
  let pre : State := ({st with ops := st.ops ++ [Op.add p q k]}.assign q (.gate t pos))
  have hstep : D.step st k = State.serve k p pre (u :: us) := by
    simp [Dag.step, Nat.not_lt.mpr hn, hl, hu, pre, p, q]
  have hnd : (u :: us).Nodup := hu ▸ D.freeUses_nodup k
  have hnext : (D.step st k).next = st.next + us.length := by
    rw [hstep, (State.serve_ops _ _ _ _).2]
    simp [pre]
  have hf : (∑ v ∈ (D.freeUses k).toFinset,
      Finsupp.single (Reg.aux ((D.step st k).pend v)) (c v)) =
      Finsupp.single (Reg.aux p) (c u) +
        ((List.range' st.next us.length).map
          fun s => Finsupp.single (Reg.aux s) (g (Reg.aux s))).sum := by
    rw [List.sum_toFinset _ (D.freeUses_nodup k), hu, hstep]
    have hc' := hc
    rw [hstep] at hc'
    exact internal_served_weights k p u us pre hnd c g hc'
  have hlu : D.linkUse k = some (.gate t pos) := by simp [Dag.linkUse, hl]
  have hnot : Use.gate t pos ∉ D.freeUses k := by
    intro h
    have hb := (D.mem_freeUses.mp h).2
    have ht := (D.linkedB_iff (.gate t pos)).mpr ⟨k, hk, hlu⟩
    rw [hb] at ht
    cases ht
  have hpend : (D.step st k).pend (.gate t pos) = q := by
    rw [hstep, FrameFlow.serve_pend_other k p (.gate t pos) (u :: us) pre
      (by rwa [← hu])]
    simp [pre, State.assign]
  rw [boundaryWeights, D.pendingWeights_succ hv k hk, hlu]
  simp only [Option.toList_some, List.toFinset_cons, List.toFinset_nil,
    Finset.insert_empty, Finset.sum_singleton]
  change (survivorWeights D k (D.step st k) c + _) + _ + _ = _
  rw [survivorWeights_step D hv k hk, hf, hnext, hpend]
  change _ = survivorWeights D k st c + Finsupp.single (Reg.aux p) (c u) +
    Finsupp.single (Reg.aux q) (c (.gate t pos)) + futureWeights st.next g
  calc
    _ = survivorWeights D k st c + Finsupp.single (Reg.aux p) (c u) +
        Finsupp.single (Reg.aux q) (c (.gate t pos)) +
          (((List.range' st.next us.length).map
            fun s => Finsupp.single (Reg.aux s) (g (Reg.aux s))).sum +
            futureWeights (st.next + us.length) g) := by ac_rfl
    _ = _ := by rw [← futureWeights_split]

/-- A linked addition preserves the combined boundary, with the retained-use
coefficient added exactly on the linked operand. -/
theorem boundary_pullOps_step_linked (D : Dag) (hv : D.Valid) (k : Nat)
    (hn : D.v ≤ k) (hk : k < D.N) (o : Bool) (t : Nat) (pos : Bool)
    (hl : D.link k = some (o, t, pos)) (st : State) (hi : D.Inv (fun _ => 0) k st)
    (u : Use) (us : List Use) (hu : D.freeUses k = u :: us)
    (c : Use → ZMod 2) (g : Reg →₀ ZMod 2)
    (hc : ∀ v ∈ us, c v = g (Reg.aux ((D.step st k).pend v)))
    (ha : ∀ side, c (.gate k side) = ((D.freeUses k).map c).sum +
      if side = o then c (.gate t pos) else 0) :
    pullOps ((D.step st k).ops.map D.vop)
      (boundaryWeights D (k + 1) (D.step st k) c g) =
      pullOps (st.ops.map D.vop) (boundaryWeights D k st c g) := by
  let p := if o then st.pend (.gate k false) else st.pend (.gate k true)
  let q := if o then st.pend (.gate k true) else st.pend (.gate k false)
  let w := boundaryWeights D (k + 1) (D.step st k) c g
  let b := ((D.freeUses k).map c).sum
  have hp : p < st.next := by
    dsimp only [p]
    split
    · exact hi.slot_lt _ (D.pending_arg hv hn hk false)
    · exact hi.slot_lt _ (D.pending_arg hv hn hk true)
  have hpq : p ≠ q := by
    have hab : st.pend (.gate k false) ≠ st.pend (.gate k true) := by
      intro he
      have := hi.inj _ _ (D.pending_arg hv hn hk false) (D.pending_arg hv hn hk true) he
      simp at this
    cases o <;> simp [p, q, hab, Ne.symm hab]
  have hsp : survivorWeights D k st c (Reg.aux p) = 0 := by
    dsimp only [p]
    split
    · exact survivorWeights_argument D hv k hn hk st c hi.inj false
    · exact survivorWeights_argument D hv k hn hk st c hi.inj true
  have hshape := boundaryWeights_linked_shape D hv k hn hk o t pos hl st u us hu c g hc
  change w = survivorWeights D k st c + Finsupp.single (Reg.aux p) (c u) +
    Finsupp.single (Reg.aux q) (c (.gate t pos)) + futureWeights st.next g at hshape
  have hwp : w (Reg.aux p) = c u := by
    rw [hshape]
    simp [hsp, hpq, Nat.not_le.mpr hp]
  let pre : State := ({st with ops := st.ops ++ [Op.add p q k]}.assign q (.gate t pos))
  have hstep : D.step st k = State.serve k p pre (u :: us) := by
    simp [Dag.step, Nat.not_lt.mpr hn, hl, hu, pre, p, q]
  have hnd : (u :: us).Nodup := hu ▸ D.freeUses_nodup k
  have hcoef : ∀ v ∈ u :: us, w (Reg.aux ((State.serve k p pre (u :: us)).pend v)) = c v := by
    intro v hv'
    have hf : v ∈ D.freeUses k := by rwa [hu]
    have hpend : D.Pending (k + 1) v :=
      (D.pending_succ_iff hv k v).mpr (Or.inr (Or.inl hf))
    have hi' := D.inv_step hv (fun _ => 0) hk hi
    rw [← hstep]
    change (D.pendingWeights (k + 1) (D.step st k) c +
      futureWeights (D.step st k).next g) (Reg.aux ((D.step st k).pend v)) = c v
    rw [Finsupp.add_apply, D.pendingWeights_at hv _ _ c hi'.inj v hpend]
    simp [Nat.not_le.mpr (hi'.slot_lt v hpend)]
  have hsum : c u + ((List.range' st.next us.length).map fun f => w (Reg.aux f)).sum = b := by
    have hs := served_observation_sum k p u us pre hnd w c hcoef
    rw [hwp] at hs
    simpa only [pre, State.assign_next, hu, b] using hs
  have hlocal := pull_node_boundary p q k st.next hp hpq
    (survivorWeights D k st c) w g (c u) b (c (.gate t pos))
    (List.range' st.next us.length) hsp hshape hsum
  rw [pullOps_step_linked D st k hn o t pos hl hp]
  change pullOps (st.ops.map D.vop) (pullOp (.add p q k)
    (w + Finsupp.single (Reg.aux p)
      (((List.range' st.next ((D.freeUses k).length - 1)).map fun f => w (Reg.aux f)).sum))) = _
  simp only [hu, List.length_cons, Nat.add_sub_cancel]
  rw [hlocal]
  congr 1
  rw [boundaryWeights, pendingWeights_internal D hv k hn hk st c, ha false, ha true]
  cases o <;> simp [p, q, b, add_assoc, add_comm, add_left_comm]

end
end IntegerMultBounds.MathlibTM2.M8.Local.AdjointB
