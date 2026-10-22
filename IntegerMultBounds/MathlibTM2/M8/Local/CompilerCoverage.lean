module

public import IntegerMultBounds.MathlibTM2.M8.Local.SlotAssignment
public import IntegerMultBounds.MathlibTM2.M8.Local.FrameBirth

/-! Compiler-frame coverage is a local property of node arguments and pivot copies. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local.FrameFlow
variable {α : Type}

/-- Each frame used on each physical slot satisfies that slot's coverage predicate. -/
def Covered (label : Op → α) (P : Nat → α → Prop) (ops : List Op) : Prop :=
  ∀ op ∈ ops, ∀ s ∈ op.slots, P s (label op)

theorem covered_append (label : Op → α) (P : Nat → α → Prop) (a b : List Op) :
    Covered label P (a ++ b) ↔ Covered label P a ∧ Covered label P b := by
  constructor
  · intro h
    exact ⟨fun op ho => h op (List.mem_append_left _ ho),
      fun op ho => h op (List.mem_append_right _ ho)⟩
  · rintro ⟨ha, hb⟩ op ho
    exact (List.mem_append.mp ho).elim (ha op) (hb op)

private theorem covered_copies (D : Dag) (node start : Nat → α) (P : Nat → α → Prop)
    (hs : ∀ s, P s (start s)) (n p : Nat) (fs : List Nat)
    (hp : D.v ≤ n → ∀ f ∈ fs, P p (start f)) :
    Covered (opLabel node start) P ((copies p fs n).map D.vop) := by
  intro op ho s hslot
  obtain ⟨copy, hcopy, rfl⟩ := List.mem_map.mp ho
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hcopy
  by_cases hn : n < D.v
  · simp only [Dag.vop, hn, ite_true, Op.slots, List.mem_singleton] at hslot
    subst s
    simpa only [Dag.vop, hn, ite_true, opLabel] using hs _
  · simp only [Dag.vop, hn, ite_false, Op.slots, List.mem_cons, List.not_mem_nil, or_false] at hslot
    rcases hslot with rfl | rfl
    · simpa only [Dag.vop, hn, ite_false, opLabel] using hp (Nat.le_of_not_gt hn) f hf
    · simpa only [Dag.vop, hn, ite_false, opLabel] using hs _

/-- Serving adds only fresh starts, and, for internal nodes, those same starts on the pivot. -/
theorem covered_serve (D : Dag) (node start : Nat → α) (P : Nat → α → Prop)
    (hs : ∀ s, P s (start s)) (n p : Nat) (us : List Use) (st : State)
    (hops : Covered (opLabel node start) P (st.ops.map D.vop))
    (hp : D.v ≤ n → ∀ f ∈ List.range' st.next (us.length - 1), P p (start f)) :
    Covered (opLabel node start) P ((State.serve n p st us).ops.map D.vop) := by
  rw [(State.serve_ops n p us st).1, List.map_append, covered_append]
  exact ⟨hops, covered_copies D node start P hs n p _ hp⟩

private theorem step_pivot_shape (D : Dag) (n : Nat) (hn : D.v ≤ n) (st : State) :
    ∃ o st', (o = st.pend (.gate n false) ∨ o = st.pend (.gate n true)) ∧
      st'.ops = st.ops ++ [Op.add (st.pend (D.pivotUse n)) o n] ∧ st'.next = st.next ∧
      D.step st n = State.serve n (st.pend (D.pivotUse n)) st' (D.freeUses n) := by
  cases hl : D.link n with
  | none =>
    have hp : D.pivotUse n = .gate n false := by simp only [Dag.pivotUse, hl]
    refine ⟨_, { st with ops := st.ops ++ [Op.add (st.pend (.gate n false)) (st.pend (.gate n true)) n] },
      Or.inr rfl, ?_, rfl, ?_⟩
    · rw [hp]
    · simp only [Dag.step, Nat.not_lt.mpr hn, ite_false, hl, hp]
  | some l =>
    obtain ⟨b, t, pos⟩ := l
    cases b
    · have hp : D.pivotUse n = .gate n true := by simp only [Dag.pivotUse, hl, Bool.not_false]
      refine ⟨_, ({ st with ops := st.ops ++ [Op.add (st.pend (.gate n true)) (st.pend (.gate n false)) n] }).assign
        (st.pend (.gate n false)) (.gate t pos), Or.inl rfl, ?_, rfl, ?_⟩
      · rw [hp, State.assign_ops]
      · simp only [Dag.step, Nat.not_lt.mpr hn, ite_false, hl, hp, Bool.false_eq_true]
    · have hp : D.pivotUse n = .gate n false := by simp only [Dag.pivotUse, hl, Bool.not_true]
      refine ⟨_, ({ st with ops := st.ops ++ [Op.add (st.pend (.gate n false)) (st.pend (.gate n true)) n] }).assign
        (st.pend (.gate n true)) (.gate t pos), Or.inr rfl, ?_, rfl, ?_⟩
      · rw [hp, State.assign_ops]
      · simp only [Dag.step, Nat.not_lt.mpr hn, ite_false, hl, hp, ite_true]

/-- A local coverage check at each argument and copy gives coverage of the whole compiler. -/
theorem compileTo_covered (D : Dag) (node start : Nat → α) (P : Nat → α → Prop)
    (hs : ∀ s, P s (start s))
    (hnode : ∀ n, D.v ≤ n → n < D.N → ∀ pos,
      P ((D.compileTo n).pend (.gate n pos)) (node n))
    (hcopy : ∀ n, D.v ≤ n → n < D.N → ∀ f ∈
      List.range' (D.compileTo n).next ((D.freeUses n).length - 1),
        P ((D.compileTo n).pend (D.pivotUse n)) (start f)) :
    ∀ k, k ≤ D.N → Covered (opLabel node start) P ((D.compileTo k).ops.map D.vop) := by
  intro k
  induction k with
  | zero => intro _; simp [Dag.compileTo, Dag.start, Covered]
  | succ k ih =>
    intro hk
    have hkN : k < D.N := by omega
    let st := D.compileTo k
    have he : D.compileTo (k + 1) = D.step st k := by
      simp only [st, Dag.compileTo, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hm := ih (by omega)
    rw [he]
    by_cases hv : k < D.v
    · let st' : State := { st with next := st.next + 1, ops := st.ops ++ [Op.src st.next k] }
      have hstep : D.step st k = State.serve k st.next st' (D.freeUses k) := by
        simp only [Dag.step, hv, ite_true, st']
      rw [hstep]
      apply covered_serve D node start P hs
      · rw [show st'.ops.map D.vop = st.ops.map D.vop ++ [Op.src st.next k] from by simp [st', Dag.vop], covered_append]
        refine ⟨hm, ?_⟩
        intro op ho s hslot
        have he := List.mem_singleton.mp ho
        subst op
        have he : s = st.next := List.mem_singleton.mp hslot
        subst s
        exact hs _
      · intro hn
        omega
    · obtain ⟨o, st', ho, hops, hnext, hstep⟩ := step_pivot_shape D k (Nat.le_of_not_gt hv) st
      rw [hstep]
      apply covered_serve D node start P hs
      · rw [hops, List.map_append, covered_append]
        refine ⟨hm, ?_⟩
        intro op hop s hslot
        have he := List.mem_singleton.mp hop
        subst op
        simp only [Dag.vop, Op.slots, List.mem_cons, List.not_mem_nil, or_false] at hslot
        change P s (node k)
        rcases hslot with rfl | rfl
        · exact hnode k (Nat.le_of_not_gt hv) hkN _
        · rcases ho with rfl | rfl <;> exact hnode k (Nat.le_of_not_gt hv) hkN _
      · intro _ f hf
        rw [hnext] at hf
        exact hcopy k (Nat.le_of_not_gt hv) hkN f hf

/-- A covered operation list covers every frame on each slot's actual trace. -/
theorem covered_framesOf (label : Op → α) (P : Nat → α → Prop) (ops : List Op)
    (h : Covered label P ops) (s : Nat) : ∀ F ∈ framesOf label s ops, P s F := by
  intro F hF
  obtain ⟨op, ho, rfl⟩ := List.mem_map.mp hF
  obtain ⟨ho, hs⟩ := List.mem_filter.mp ho
  exact h op ho s (of_decide_eq_true hs)

end IntegerMultBounds.MathlibTM2.M8.Local.FrameFlow
