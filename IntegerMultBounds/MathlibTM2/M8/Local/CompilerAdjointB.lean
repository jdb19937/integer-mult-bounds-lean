module

public import IntegerMultBounds.MathlibTM2.M8.Local.AdjointB
public import IntegerMultBounds.MathlibTM2.M8.Local.Schedule

/-! Structural adjoints of compiler blocks. Source operations do not change auxiliary
weights; serving fresh copies adds their observation weights to the pivot. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local.AdjointB
noncomputable section
open Classical

/-- Only the auxiliary coordinates matter to the garbage coefficients. -/
def AuxEq (w v : Reg →₀ ZMod 2) : Prop := ∀ s, w (.aux s) = v (.aux s)

theorem auxEq_pullOp (op : Op) {w v : Reg →₀ ZMod 2} (h : AuxEq w v) :
    AuxEq (pullOp op w) (pullOp op v) := by
  intro s
  have hh := h
  unfold AuxEq at hh
  cases op <;> simp [pullOp, pullAdd, Finsupp.add_apply, hh]

theorem auxEq_pullSrc (s n : Nat) (w : Reg →₀ ZMod 2) :
    AuxEq (pullOp (.src s n) w) w := by
  intro i
  simp [pullOp, pullAdd]

theorem auxEq_pullOps (ops : List Op) {w v : Reg →₀ ZMod 2} (h : AuxEq w v) :
    AuxEq (pullOps ops w) (pullOps ops v) := by
  induction ops with
  | nil => exact h
  | cons op ops ih => exact auxEq_pullOp op ih


/-- Erasing sources preserves every initial auxiliary observation weight. -/
theorem auxEq_filter_sources (ops : List Op) (w : Reg →₀ ZMod 2) :
    AuxEq (pullOps (ops.filter fun op => !Op.isSrc op) w) (pullOps ops w) := by
  induction ops with
  | nil => intro s; rfl
  | cons op ops ih =>
    cases op with
    | src s n =>
      simpa only [AuxEq, List.filter_cons, Op.isSrc, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        pullOps, List.foldr_cons] using
        (fun i => (ih i).trans (auxEq_pullSrc s n (pullOps ops w) i).symm)
    | add p o n =>
      simpa only [List.filter_cons, Op.isSrc, Bool.not_false, ↓reduceIte,
        pullOps, List.foldr_cons] using auxEq_pullOp (.add p o n) ih
    | copy p f n =>
      simpa only [List.filter_cons, Op.isSrc, Bool.not_false, ↓reduceIte,
        pullOps, List.foldr_cons] using auxEq_pullOp (.copy p f n) ih

/-- The compiler's full emitted word can be used in the backward recurrence. -/
theorem cov_eq_compiler_pullOps (D : Dag) (targets : Nat → List Nat) (s t : Nat) :
    D.cov targets s t = (pullOps D.opsB (rootWeights D targets t)) (.aux s) := by
  rw [cov_eq_pullOps]
  exact auxEq_filter_sources D.opsB (rootWeights D targets t) s

theorem pullOps_append (a b : List Op) (w : Reg →₀ ZMod 2) :
    pullOps (a ++ b) w = pullOps a (pullOps b w) := by
  simp [pullOps, List.foldr_append]

/-- Fresh copies preserve their own weights and add their sum to the kept slot.
Repeated destinations are allowed; only the pivot must differ from each destination. -/
theorem pullOps_copies (p n : Nat) (fs : List Nat) (w : Reg →₀ ZMod 2)
    (hp : p ∉ fs) :
    pullOps (copies p fs n) w =
      w + Finsupp.single (.aux p) ((fs.map fun f => w (.aux f)).sum) := by
  induction fs with
  | nil => simp [copies, pullOps]
  | cons f fs ih =>
    have hpf : p ≠ f := fun h => hp (List.mem_cons.mpr (Or.inl h))
    have hps : p ∉ fs := fun h => hp (List.mem_cons_of_mem _ h)
    simp only [copies, List.map_cons, pullOps, List.foldr_cons] at ih ⊢
    rw [ih hps]
    simp only [pullOp, pullAdd, Finsupp.add_apply, Finsupp.single_apply,
      show Reg.aux p ≠ Reg.aux f from fun h => hpf (Reg.aux.inj h), ↓reduceIte,
      add_zero, List.sum_cons]
    rw [add_assoc, ← Finsupp.single_add, add_comm ((fs.map fun f => w (.aux f)).sum)]

/-- Leaf copies become source gates, so they contribute no auxiliary weight. -/
theorem auxEq_leaf_copies (D : Dag) (p n : Nat) (hn : n < D.v)
    (fs : List Nat) (w : Reg →₀ ZMod 2) :
    AuxEq (pullOps ((copies p fs n).map D.vop) w) w := by
  induction fs with
  | nil => intro s; rfl
  | cons f fs ih =>
    change AuxEq (pullOp (D.vop (.copy p f n))
      (pullOps ((copies p fs n).map D.vop) w)) w
    rw [Dag.vop, ite_eq_left hn]
    intro s
    exact (auxEq_pullSrc f n _ s).trans (ih s)

/-- Internal copies retain their compiler adjoint exactly. -/
theorem pullOps_internal_copies (D : Dag) (p n : Nat) (hn : D.v ≤ n)
    (fs : List Nat) (w : Reg →₀ ZMod 2) (hp : p ∉ fs) :
    pullOps ((copies p fs n).map D.vop) w =
      w + Finsupp.single (.aux p) ((fs.map fun f => w (.aux f)).sum) := by
  have hm : (copies p fs n).map D.vop = copies p fs n := by
    simp [copies, List.map_map, Dag.vop, Nat.not_lt.mpr hn]
  rw [hm, pullOps_copies p n fs w hp]

/-- Serving a non-leaf adds all freshly allocated observation weights to its pivot. -/
theorem pullOps_serve (D : Dag) (n p : Nat) (hn : D.v ≤ n)
    (us : List Use) (st : State) (hp : p < st.next) (w : Reg →₀ ZMod 2) :
    pullOps ((State.serve n p st us).ops.map D.vop) w =
      pullOps (st.ops.map D.vop)
        (w + Finsupp.single (.aux p)
          (((List.range' st.next (us.length - 1)).map fun f => w (.aux f)).sum)) := by
  rw [(State.serve_ops n p us st).1, List.map_append, pullOps_append,
    pullOps_internal_copies D p n hn]
  intro h
  obtain ⟨i, _, hi⟩ := List.mem_range'.mp h
  simp only [Nat.one_mul] at hi
  omega

/-- Serving a leaf changes only source weights, even through the earlier compiler prefix. -/
theorem auxEq_serve_leaf (D : Dag) (n p : Nat) (hn : n < D.v)
    (us : List Use) (st : State) (w : Reg →₀ ZMod 2) :
    AuxEq (pullOps ((State.serve n p st us).ops.map D.vop) w)
      (pullOps (st.ops.map D.vop) w) := by
  rw [(State.serve_ops n p us st).1, List.map_append, pullOps_append]
  exact auxEq_pullOps _ (auxEq_leaf_copies D p n hn _ w)

/-- A leaf step has no effect on backward auxiliary weights. -/
theorem auxEq_step_leaf (D : Dag) (st : State) (n : Nat) (hn : n < D.v)
    (w : Reg →₀ ZMod 2) :
    AuxEq (pullOps ((D.step st n).ops.map D.vop) w)
      (pullOps (st.ops.map D.vop) w) := by
  rw [Dag.step, ite_eq_left hn]
  have h := auxEq_serve_leaf D n st.next hn (D.freeUses n)
    {st with next := st.next + 1, ops := st.ops ++ [.src st.next n]} w
  rw [List.map_append, pullOps_append] at h
  intro s
  exact (h s).trans (auxEq_pullOps _ (auxEq_pullSrc st.next n w) s)

/-- A non-linked addition pulls the combined served weight through its two operands. -/
theorem pullOps_step_unlinked (D : Dag) (st : State) (n : Nat) (hn : D.v ≤ n)
    (hl : D.link n = none) (hp : st.pend (.gate n false) < st.next)
    (w : Reg →₀ ZMod 2) :
    pullOps ((D.step st n).ops.map D.vop) w =
      pullOps (st.ops.map D.vop)
        (pullOp (.add (st.pend (.gate n false)) (st.pend (.gate n true)) n)
          (w + Finsupp.single (.aux (st.pend (.gate n false)))
            (((List.range' st.next ((D.freeUses n).length - 1)).map
              fun f => w (.aux f)).sum))) := by
  rw [Dag.step, ite_eq_right (Nat.not_lt.mpr hn), hl]
  rw [pullOps_serve D n _ hn]
  · rw [List.map_append, pullOps_append]
    rfl
  · exact hp

/-- A linked addition uses the opposite operand as pivot; assigning the retained
operand to its linked use emits no operation and hence changes no adjoint weight. -/
theorem pullOps_step_linked (D : Dag) (st : State) (n : Nat) (hn : D.v ≤ n)
    (o : Bool) (t : Nat) (pos : Bool) (hl : D.link n = some (o, t, pos))
    (hp : (if o then st.pend (.gate n false) else st.pend (.gate n true)) < st.next)
    (w : Reg →₀ ZMod 2) :
    let p := if o then st.pend (.gate n false) else st.pend (.gate n true)
    let q := if o then st.pend (.gate n true) else st.pend (.gate n false)
    pullOps ((D.step st n).ops.map D.vop) w =
      pullOps (st.ops.map D.vop)
        (pullOp (.add p q n)
          (w + Finsupp.single (.aux p)
            (((List.range' st.next ((D.freeUses n).length - 1)).map
              fun f => w (.aux f)).sum))) := by
  dsimp only
  rw [Dag.step, ite_eq_right (Nat.not_lt.mpr hn), hl]
  rw [pullOps_serve D n _ hn]
  · rw [State.assign_ops, List.map_append, pullOps_append]
    rfl
  · exact hp

end
end IntegerMultBounds.MathlibTM2.M8.Local.AdjointB
