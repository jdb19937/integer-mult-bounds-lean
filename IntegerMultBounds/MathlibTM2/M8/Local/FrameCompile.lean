module

public import IntegerMultBounds.MathlibTM2.M8.Local.FrameFlowB

/-! Compiler monotonicity with a separate frame at every copied slot.
Only incoming-use edges and each node's copy chain are geometric obligations. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local.FrameFlow

variable {α : Type}

def opLabel (node start : Nat → α) : Op → α
  | .add _ _ n => node n
  | .src s _ | .copy _ s _ => start s

/-- Arbitrary copy frames are compatible with the whole compiler if every
addition follows its actual incoming frames and every copy chain is ordered. -/
theorem compileTo_mono (D : Dag) (hv : D.Valid) (R : α → α → Prop)
    (node start : Nat → α)
    (hsource : ∀ k, D.v ≤ k → k < D.N → ∀ pos a,
      last (opLabel node start) ((D.compileTo k).ops.map D.vop)
        ((D.compileTo k).pend (.gate k pos)) = some a → R a (node k))
    (hcopies : ∀ k, D.v ≤ k → k < D.N →
      List.IsChain R (node k :: (List.range' (D.compileTo k).next
        ((D.freeUses k).length - 1)).map start)) :
    ∀ k, k ≤ D.N → Mono R (opLabel node start) ((D.compileTo k).ops.map D.vop) (fun _ => none) := by
  let label := opLabel node start
  intro k
  induction k with
  | zero => intro _; trivial
  | succ k ih =>
    intro hk
    have hkN : k < D.N := by omega
    let st := D.compileTo k
    have hm := ih (by omega)
    have hnext : D.compileTo (k + 1) = D.step st k := by
      simp [st, Dag.compileTo, List.range_succ, List.foldl_append]
    have hf : ∀ s, st.next ≤ s → last label (st.ops.map D.vop) s = none :=
      fun s hs => compileTo_frame_fresh D hv label k (by omega) s hs
    rw [hnext]
    by_cases hleaf : k < D.v
    · let st' : State := { st with next := st.next + 1, ops := st.ops ++ [Op.src st.next k] }
      have hs : D.step st k = State.serve k st.next st' (D.freeUses k) := by
        simp only [Dag.step, hleaf, ite_true, st']
      have hops : st'.ops.map D.vop = st.ops.map D.vop ++ [Op.src st.next k] := by
        simp [st', Dag.vop]
      rw [hs]
      apply serve_mono_leaf D R label k st.next hleaf (D.freeUses k) st' (fun _ => none)
      · rw [hops, mono_append]
        refine ⟨hm, ?_⟩
        refine ⟨?_, trivial⟩
        intro s hs a ha
        have he : s = st.next := by simpa [Op.slots] using hs
        subst s
        change last label (st.ops.map D.vop) st.next = some a at ha
        rw [hf _ le_rfl] at ha
        cases ha
      · intro s hs
        change last label (st'.ops.map D.vop) s = none
        rw [hops, last_append_single]
        have hne : s ≠ st.next := by change st.next + 1 ≤ s at hs; omega
        simp only [Op.slots, List.mem_singleton, hne, ite_false]
        exact hf s (by change st.next + 1 ≤ s at hs; omega)
    · have hn : D.v ≤ k := Nat.le_of_not_gt hleaf
      obtain ⟨p, o, st', hp, ho, hops, hcount, hs⟩ := step_internal_shape D k hn st
      have hi := D.inv_compileTo hv (fun _ => 0) k (by omega)
      have harg : ∀ pos, st.pend (.gate k pos) < st.next :=
        fun pos => hi.slot_lt _ (D.pending_arg hv hn hkN pos)
      have hplt : p < st.next := by rcases hp with rfl | rfl <;> exact harg _
      have holt : o < st.next := by rcases ho with rfl | rfl <;> exact harg _
      have hopmap : st'.ops.map D.vop = st.ops.map D.vop ++ [Op.add p o k] := by
        simp [hops, Dag.vop]
      have hcur : last label (st'.ops.map D.vop) p = some (node k) := by
        rw [hopmap, last_append_single]
        simp [Op.slots, label, opLabel]
      rw [hs]
      apply serve_mono_internal D R label k p hn (D.freeUses k) st' (fun _ => none)
        (by simpa only [hcount] using hplt)
      · rw [hopmap, mono_append]
        refine ⟨hm, ⟨?_, trivial⟩⟩
        intro s hs a ha
        change last label (st.ops.map D.vop) s = some a at ha
        have hin : s = st.pend (.gate k false) ∨ s = st.pend (.gate k true) := by
          have h : s = p ∨ s = o := by simpa [Op.slots] using hs
          rcases h with rfl | rfl
          · exact hp
          · exact ho
        change R a (node k)
        rcases hin with rfl | rfl
        · exact hsource k hn hkN false a ha
        · exact hsource k hn hkN true a ha
      · intro s hs
        change last label (st'.ops.map D.vop) s = none
        rw [hopmap, last_append_single]
        have hsp : s ≠ p := by rw [hcount] at hs; omega
        have hso : s ≠ o := by rw [hcount] at hs; omega
        simp only [Op.slots, List.mem_cons, hsp, hso]
        exact hf s (by rwa [hcount] at hs)
      · change List.IsChain R ((last label (st'.ops.map D.vop) p).toList ++ _)
        rw [hcur, hcount]
        exact hcopies k hn hkN

end IntegerMultBounds.MathlibTM2.M8.Local.FrameFlow
