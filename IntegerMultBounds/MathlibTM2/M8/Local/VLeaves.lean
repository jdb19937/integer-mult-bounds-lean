module

public import IntegerMultBounds.MathlibTM2.M8.Local.Commute
public import IntegerMultBounds.MathlibTM2.M8.Local.Schedule

/-!
# V leaves

In the design-B word a leaf's copies read the leaf's input directly: each copy of a leaf slot
becomes a source gate on the copy's own slot (`vop`). On clean input the V operations `opsB`
compute what the compiled operations compute (`opsB_contents`), so every root's slot holds the
root's value (`opsB_root`).

Every source gate fills a slot that no earlier operation touches (`opsB_fresh`). So the source
gates move to the front (`run_opsB_front`): the operations run as the V gates followed by the
side operations `sideB`, the operations that are not source gates.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Local

open Networks

namespace Dag
variable (D : Dag)

/-- A copy of a leaf slot reads the leaf's input instead. -/
def vop : Op → Op
  | .copy p f n => if n < D.v then .src f n else .copy p f n
  | op => op

/-- The compiled operations with V leaves. -/
def opsB : List Op := D.compile.ops.map D.vop

/-- The side operations of `opsB`: all but the source gates. -/
def sideB : List Op := D.opsB.filter fun op => !op.isSrc

/-- The source gates of `opsB`. -/
def srcB : List Op := D.opsB.filter Op.isSrc

theorem vop_node (op : Op) : (D.vop op).node = op.node := by
  cases op with
  | copy p f n => by_cases h : n < D.v <;> simp [vop, h, Op.node]
  | _ => rfl

theorem vop_slots (op : Op) : ∀ s ∈ (D.vop op).slots, s ∈ op.slots := by
  cases op with
  | copy p f n => by_cases h : n < D.v <;> simp [vop, h, Op.slots]
  | _ => exact fun _ h => h

theorem vop_of_le {op : Op} (h : D.v ≤ op.node) : D.vop op = op := by
  cases op with
  | copy p f n => simp only [Op.node] at h; simp [vop, show ¬ n < D.v by omega]
  | _ => rfl

theorem vop_distinct {op : Op} (h : op.Distinct) : (D.vop op).Distinct := by
  cases op with
  | copy p f n =>
    by_cases hn : n < D.v
    · simp only [vop, hn, ite_true, Op.Distinct]
    · simpa only [vop, hn, ite_false] using h
  | _ => exact h

theorem vop_slotsLt {B : ℕ} {op : Op} (h : op.SlotsLt B) : (D.vop op).SlotsLt B := by
  cases op with
  | copy p f n =>
    by_cases hn : n < D.v
    · simp only [vop, hn, ite_true, Op.SlotsLt]; exact h.2
    · simpa only [vop, hn, ite_false] using h
  | _ => exact h

/-! ### Clean input -/

/-- Copies of slot `s` holding the leaf input `x n` add the input itself. -/
theorem runOps_copies_src (x : ℕ → ZMod 2) {s n : ℕ} (hn : n < D.v) :
    ∀ (fs : List ℕ) (c : ℕ → ZMod 2), c s = x n → s ∉ fs →
      runOps x ((copies s fs n).map D.vop) c = runOps x (copies s fs n) c
  | [], _, _, _ => rfl
  | f :: fs, c, hc, hs => by
    have hf : f ≠ s := fun h => hs (h ▸ List.mem_cons_self)
    simp only [copies, List.map_cons, runOps, List.foldl_cons] at *
    have e : (D.vop (.copy s f n)).run x c = (Op.copy s f n).run x c := by
      simp only [vop, hn, ite_true, Op.run, hc]
    rw [e]
    apply runOps_copies_src x hn fs
    · simp only [Op.run]; rw [Function.update_of_ne (Ne.symm hf)]; exact hc
    · exact fun h => hs (List.mem_cons_of_mem _ h)

theorem map_vop_of_node (k : ℕ) (hk : D.v ≤ k) :
    ∀ new : List Op, (∀ op ∈ new, op.node = k) → new.map D.vop = new
  | [], _ => rfl
  | op :: new, h => by
    rw [List.map_cons, D.vop_of_le (by rw [h op List.mem_cons_self]; exact hk),
      map_vop_of_node k hk new fun o ho => h o (List.mem_cons_of_mem _ ho)]

theorem contents_vop (hv : D.Valid) (x : ℕ → ZMod 2) :
    ∀ k, k ≤ D.N → runOps x ((D.compileTo k).ops.map D.vop) (fun _ => 0) =
      (D.compileTo k).contents x := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have he : D.compileTo (k + 1) = D.step (D.compileTo k) k := by
      simp only [compileTo, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hi := D.inv_compileTo hv x k (by omega)
    set st := D.compileTo k
    rw [he]
    by_cases hleaf : k < D.v
    · -- a leaf: the copies of its source slot read the input
      set st1 : State := { st with next := st.next + 1, ops := st.ops ++ [.src st.next k] }
      have hstep : D.step st k = State.serve k st.next st1 (D.freeUses k) := by
        simp [step, hleaf, st1]
      have hops := (State.serve_ops k st.next (D.freeUses k) st1).1
      rw [hstep, State.contents, hops, List.map_append, runOps_append, runOps_append]
      have h1 : st1.ops.map D.vop = st.ops.map D.vop ++ [.src st.next k] := by
        simp [st1, vop]
      rw [h1, runOps_append, ih (by omega), runOps_singleton]
      have h2 : st1.ops = st.ops ++ [.src st.next k] := rfl
      rw [h2, runOps_append, runOps_singleton]
      apply D.runOps_copies_src x hleaf
      · simp [Op.run, hi.fresh _ le_rfl]
      · intro h
        have := (List.mem_range'_1.mp h).1
        simp [st1] at this
    · -- an addition: its operations are not leaf copies
      obtain ⟨new, hops, hnew⟩ := D.step_ops st k
      rw [State.contents, hops, List.map_append,
        D.map_vop_of_node k (by omega) new fun op h => (hnew op h).1, runOps_append,
        runOps_append, ih (by omega)]
      rfl

/-- **V leaves on clean input** compute the compiled contents. -/
theorem opsB_contents (hv : D.Valid) (x : ℕ → ZMod 2) :
    runOps x D.opsB (fun _ => 0) = D.compile.contents x :=
  D.contents_vop hv x D.N le_rfl

theorem opsB_ok (hv : D.Valid) : ∀ op ∈ D.opsB, op.Distinct ∧ op.SlotsLt D.compile.next := by
  intro op hop
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hop
  exact ⟨D.vop_distinct (D.compile_ops_ok hv o ho).1, D.vop_slotsLt (D.compile_ops_ok hv o ho).2⟩

/-- On the sources alone, every root's slot ends with the root's value. -/
theorem opsB_root (hv : D.Valid) (c : Reg → ZMod 2) {r : ℕ} (hr : r < D.rootCount) :
    Circuit.run (D.opsB.map opGate) (part Reg.isX c) (.aux (D.compile.pend (.root r))) =
      D.val (fun n => c (.x n)) (D.rootNode r) := by
  rw [(run_ops_bridge _ _).1, ← (D.compile_correct hv _ r hr).2]
  have hx : (fun n => part Reg.isX c (.x n)) = fun n => c (.x n) := funext fun n => by
    simp [part, Reg.isX]
  have ha : (fun s => part Reg.isX c (.aux s)) = fun _ => 0 := funext fun s => by
    simp [part, Reg.isX]
  rw [hx, ha, opsB_contents D hv]

/-! ### Source gates fill fresh slots -/

/-- Every source gate fills a slot that no earlier operation touches. -/
def FreshSrc (ops : List Op) : Prop :=
  ops.Pairwise fun o o' => ∀ s n, o' = .src s n → s ∉ o.slots

theorem fresh_vop (hv : D.Valid) :
    ∀ k, k ≤ D.N → FreshSrc ((D.compileTo k).ops.map D.vop) := by
  intro k
  induction k with
  | zero => intro _; simp [FreshSrc, compileTo, start]
  | succ k ih =>
    intro hk
    have he : D.compileTo (k + 1) = D.step (D.compileTo k) k := by
      simp only [compileTo, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hi := D.inv_compileTo hv (fun _ => 0) k (by omega)
    set st := D.compileTo k
    rw [he]
    have hold : ∀ o ∈ st.ops.map D.vop, ∀ s, s ∈ o.slots → s < st.next := by
      intro o ho s hs
      obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
      have h := (hi.ops_ok o' ho').2
      have hs' := D.vop_slots o' s hs
      cases o' <;> simp_all [Op.SlotsLt, Op.slots] <;> omega
    by_cases hleaf : k < D.v
    · set st1 : State := { st with next := st.next + 1, ops := st.ops ++ [.src st.next k] }
      have hstep : D.step st k = State.serve k st.next st1 (D.freeUses k) := by
        simp [step, hleaf, st1]
      have hops := (State.serve_ops k st.next (D.freeUses k) st1).1
      set fs := List.range' st1.next ((D.freeUses k).length - 1)
      have hfs : ∀ f ∈ fs, st.next < f := fun f hf => by
        have := (List.mem_range'_1.mp hf).1; simp [st1] at this; omega
      have hmap : (copies st.next fs k).map D.vop = fs.map fun f => Op.src f k := by
        simp [copies, vop, hleaf]
      rw [hstep, hops]
      change FreshSrc ((st.ops ++ [Op.src st.next k] ++ copies st.next fs k).map D.vop)
      rw [List.map_append, List.map_append, hmap]
      unfold FreshSrc
      rw [List.pairwise_append, List.pairwise_append]
      refine ⟨⟨ih (by omega), by simp, ?_⟩, ?_, ?_⟩
      · intro o ho o' ho' s n he
        have ho'' : o' = Op.src st.next k := by simpa [vop] using ho'
        rw [ho''] at he
        cases he
        intro hs
        exact absurd (hold o ho _ hs) (lt_irrefl _)
      · rw [List.pairwise_map]
        refine List.Pairwise.imp (R := (· ≠ ·)) ?_ List.nodup_range'
        intro f f' hne s n he
        cases he
        simp [Op.slots, Ne.symm hne]
      · intro o ho o' ho' s n he
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ho'
        cases he
        rcases List.mem_append.mp ho with ho | ho
        · intro hs
          have := hold o ho _ hs
          have := hfs _ hf
          omega
        · have ho'' : o = Op.src st.next k := by simpa [vop] using ho
          subst ho''
          simp only [Op.slots, List.mem_singleton]
          exact Nat.ne_of_gt (hfs _ hf)
    · obtain ⟨new, hops, hnew⟩ := D.step_ops st k
      rw [hops, List.map_append, D.map_vop_of_node k (by omega) new fun op h => (hnew op h).1]
      unfold FreshSrc
      rw [List.pairwise_append]
      refine ⟨ih (by omega), ?_, ?_⟩
      · refine List.Pairwise.imp_of_mem ?_
          (List.pairwise_of_forall (R := fun _ _ => True) fun _ _ => trivial)
        intro o o' _ ho' _ s n he
        exact absurd ((hnew o' ho').2 s n he) (by omega)
      · intro o _ o' ho' s n he
        exact absurd ((hnew o' ho').2 s n he) (by omega)

theorem opsB_fresh (hv : D.Valid) : FreshSrc D.opsB := D.fresh_vop hv D.N le_rfl

/-- An XOR gate of a side operation commutes with a source gate on a slot it does not touch. -/
theorem opGate_commute_src {o : Op} (ho : o.isSrc = false) {s n : ℕ} (hs : s ∉ o.slots) :
    GateCommute (opGate o) (opGate (.src s n)) := by
  cases o with
  | src => simp [Op.isSrc] at ho
  | add p q k =>
    refine add_commute (by simp) ?_
    simp only [Op.slots, List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
    simpa using Ne.symm hs.2
  | copy p f k =>
    refine add_commute (by simp) ?_
    simp only [Op.slots, List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
    simpa using Ne.symm hs.1

/-- **The source gates move to the front.** -/
theorem run_opsB_front (hv : D.Valid) :
    Circuit.run (D.opsB.map opGate) = Circuit.run (D.srcB.map opGate ++ D.sideB.map opGate) := by
  rw [run_split opGate Op.isSrc ?_]
  · rfl
  · refine List.Pairwise.imp ?_ (D.opsB_fresh hv)
    intro o o' h ho ho'
    cases o' with
    | src s n => exact opGate_commute_src ho (h s n rfl)
    | _ => simp [Op.isSrc] at ho'

end Dag

end IntegerMultBounds.MathlibTM2.M8.Local
