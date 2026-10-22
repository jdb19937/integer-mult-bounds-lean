module

public import IntegerMultBounds.MathlibTM2.M8.Local.FrameCompile
public import IntegerMultBounds.MathlibTM2.M8.Local.SlotCount

/-! Every allocated auxiliary slot first appears at its own start frame.
This supplies the lower boundary for readouts without evaluating compiler data. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local.FrameFlow
variable {α : Type}

theorem framesOf_append (label : Op → α) (s : Nat) (a b : List Op) :
    framesOf label s (a ++ b) = framesOf label s a ++ framesOf label s b := by
  simp only [framesOf, List.filter_append, List.map_append]

theorem last_getLast (label : Op → α) (ops : List Op) (s : Nat) :
    last label ops s = (framesOf label s ops).getLast? := by
  simpa only [last, Option.or_none] using foldl_last label ops (fun _ => none) (s := s)

theorem compileTo_frames_fresh (D : Dag) (hv : D.Valid) (label : Op → α)
    (k : Nat) (hk : k ≤ D.N) (s : Nat) (hs : (D.compileTo k).next ≤ s) :
    framesOf label s ((D.compileTo k).ops.map D.vop) = [] := by
  apply List.getLast?_eq_none_iff.mp
  rw [← last_getLast]
  exact compileTo_frame_fresh D hv label k hk s hs

theorem copies_head (D : Dag) (node start : Nat → α) (p n s : Nat) (hsp : s ≠ p) :
    ∀ fs : List Nat,
      (framesOf (opLabel node start) s ((copies p fs n).map D.vop)).head? =
        if s ∈ fs then some (start s) else none
  | [] => by simp [copies, framesOf]
  | f :: fs => by
    by_cases hn : n < D.v <;> by_cases hsf : s = f
    · subst f
      simp [copies, framesOf, Dag.vop, hn, Op.slots, opLabel]
    · simpa [copies, framesOf, Dag.vop, hn, Op.slots, opLabel, hsf] using
        copies_head D node start p n s hsp fs
    · subst f
      simp [copies, framesOf, Dag.vop, hn, Op.slots, opLabel, hsp]
    · simpa [copies, framesOf, Dag.vop, hn, Op.slots, opLabel, hsf, hsp] using
        copies_head D node start p n s hsp fs

/-- The first frame of an allocated slot is exactly its declared start frame. -/
theorem compileTo_head (D : Dag) (hv : D.Valid) (node start : Nat → α) :
    ∀ k, k ≤ D.N → ∀ s, s < (D.compileTo k).next →
      (framesOf (opLabel node start) s ((D.compileTo k).ops.map D.vop)).head? = some (start s) := by
  intro k
  induction k with
  | zero => intro _ s hs; simp [Dag.compileTo, Dag.start] at hs
  | succ k ih =>
    intro hk s hs
    let st := D.compileTo k
    have hkN : k < D.N := by omega
    have he : D.compileTo (k + 1) = D.step st k := by
      simp [st, Dag.compileTo, List.range_succ, List.foldl_append]
    by_cases hold : s < st.next
    · obtain ⟨new, hops, _⟩ := D.step_ops st k
      rw [he, hops, List.map_append, framesOf_append, List.head?_append,
        ih (by omega) s hold]
      rfl
    · have hf : framesOf (opLabel node start) s (st.ops.map D.vop) = [] :=
        compileTo_frames_fresh D hv (opLabel node start) k (by omega) s (Nat.le_of_not_gt hold)
      have hcount := D.step_next hv st hkN
      rw [he] at hs ⊢
      by_cases hleaf : k < D.v
      · let st' : State := { st with next := st.next + 1, ops := st.ops ++ [Op.src st.next k] }
        have hstep : D.step st k = State.serve k st.next st' (D.freeUses k) := by
          simp only [Dag.step, hleaf, ite_true, st']
        rw [hstep, (State.serve_ops k st.next (D.freeUses k) st').1,
          List.map_append, framesOf_append, List.head?_append]
        have hpre : framesOf (opLabel node start) s (st'.ops.map D.vop) =
            if s = st.next then [start s] else [] := by
          simp only [st', List.map_append, framesOf_append, hf, List.nil_append]
          by_cases heq : s = st.next
          · subst s; simp [framesOf, Dag.vop, Op.slots, opLabel]
          · simp [framesOf, Dag.vop, Op.slots, heq]
        rw [hpre]
        by_cases heq : s = st.next
        · simp [heq]
        · rw [ite_eq_right heq]
          change (framesOf (opLabel node start) s
            ((copies st.next (List.range' (st.next + 1) ((D.freeUses k).length - 1)) k).map D.vop)).head? = _
          rw [copies_head D node start st.next k s heq, ite_eq_left]
          apply List.mem_range'_1.mpr
          rw [hcount] at hs
          simp only [hleaf, ite_true] at hs
          constructor <;> omega
      · have hn : D.v ≤ k := Nat.le_of_not_gt hleaf
        obtain ⟨p, o, st', hp, ho, hops, hnext, hstep⟩ := step_internal_shape D k hn st
        have hi := D.inv_compileTo hv (fun _ => 0) k (by omega)
        have ha : ∀ pos, st.pend (.gate k pos) < st.next :=
          fun pos => hi.slot_lt _ (D.pending_arg hv hn hkN pos)
        have hp' : p < st.next := by rcases hp with rfl | rfl <;> exact ha _
        have ho' : o < st.next := by rcases ho with rfl | rfl <;> exact ha _
        have hsp : s ≠ p := by omega
        have hso : s ≠ o := by omega
        have hpre : framesOf (opLabel node start) s (st'.ops.map D.vop) = [] := by
          rw [hops, List.map_append, framesOf_append, hf]
          simp [framesOf, Dag.vop, Op.slots, hsp, hso]
        rw [hstep, (State.serve_ops k p (D.freeUses k) st').1,
          List.map_append, framesOf_append, hpre, List.nil_append, hnext,
          copies_head D node start p k s hsp, ite_eq_left]
        apply List.mem_range'_1.mpr
        rw [hcount] at hs
        simp only [hleaf, ite_false] at hs
        exact ⟨by omega, hs⟩

theorem pairwise_head_bound (R : α → α → Prop) (xs : List α) (a : α)
    (h : xs.Pairwise R) (hh : xs.head? = some a) (ha : R a a) : ∀ b ∈ xs, R a b := by
  cases xs with
  | nil => simp at hh
  | cons c xs =>
    have he : c = a := Option.some.inj hh
    subst c
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ha
    · exact (List.pairwise_cons.mp h).1 b hb

theorem pairwise_last_bound (R : α → α → Prop) (xs : List α) (a : α)
    (h : xs.Pairwise R) (hh : xs.getLast? = some a) (ha : R a a) : ∀ b ∈ xs, R b a := by
  have he := List.getLast_of_getLast?_eq_some hh
  intro b hb
  have hr := h.rel_getLast_of_rel_getLast_getLast hb (by simpa only [he] using ha)
  simpa only [he] using hr

end IntegerMultBounds.MathlibTM2.M8.Local.FrameFlow
