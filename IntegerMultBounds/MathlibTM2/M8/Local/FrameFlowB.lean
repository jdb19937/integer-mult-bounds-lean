module

public import IntegerMultBounds.MathlibTM2.M8.Local.FrameFlow
public import IntegerMultBounds.MathlibTM2.M8.Local.VLeaves

/-! Serving with V leaves: internal copies advance the pivot's frame, while
leaf copies become independent sources and leave the kept pivot alone. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local.FrameFlow

variable {α : Type}

theorem foldl_sources (label : Op → α) (node s : Nat) :
    ∀ (fs : List Nat) (cur : Nat → Option α),
      ((fs.map fun f => Op.src f node).foldl (touch label) cur) s =
        if s ∈ fs then some (label (.src s node)) else cur s
  | [], cur => by simp
  | f :: fs, cur => by
    rw [List.map_cons, List.foldl_cons, foldl_sources label node s fs]
    by_cases hs : s ∈ fs
    · simp [hs]
    · by_cases hsf : s = f
      · subst f; simp [hs, touch, Op.slots]
      · simp [hs, hsf, touch, Op.slots]

theorem mono_sources (R : α → α → Prop) (label : Op → α) (node : Nat) :
    ∀ (fs : List Nat) (cur : Nat → Option α),
      (∀ f ∈ fs, cur f = none) → fs.Nodup →
        Mono R label (fs.map fun f => Op.src f node) cur
  | [], _, _, _ => trivial
  | f :: fs, cur, hfresh, hnd => by
    rw [List.nodup_cons] at hnd
    refine ⟨?_, mono_sources R label node fs _ ?_ hnd.2⟩
    · intro s hs a ha
      simp only [Op.slots, List.mem_singleton] at hs
      subst s
      rw [hfresh f (by simp)] at ha
      cases ha
    · intro g hg
      have hgf : g ≠ f := fun h => hnd.1 (h ▸ hg)
      simpa [touch, Op.slots, hgf] using hfresh g (List.mem_cons_of_mem _ hg)

theorem vop_copies_internal (D : Dag) (piv node : Nat) (hn : D.v ≤ node) (fs : List Nat) :
    (copies piv fs node).map D.vop = copies piv fs node := by
  simp [copies, List.map_map, Dag.vop, Nat.not_lt.mpr hn]

theorem vop_copies_leaf (D : Dag) (piv node : Nat) (hn : node < D.v) (fs : List Nat) :
    (copies piv fs node).map D.vop = fs.map fun f => Op.src f node := by
  simp [copies, List.map_map, Dag.vop, hn]

theorem serve_pivot_internal (D : Dag) (label : Op → α) (node piv : Nat)
    (hn : D.v ≤ node) (us : List Use) (st : State) :
    last label ((State.serve node piv st us).ops.map D.vop) piv =
      (((List.range' st.next (us.length - 1)).map fun f => label (.copy piv f node)).getLast?).or
        (last label (st.ops.map D.vop) piv) := by
  rw [(State.serve_ops node piv us st).1, List.map_append, vop_copies_internal D piv node hn]
  simp only [last, List.foldl_append]
  exact foldl_copies_pivot label piv node _ _

theorem serve_pivot_leaf (D : Dag) (label : Op → α) (node piv : Nat)
    (hn : node < D.v) (us : List Use) (st : State) (hpiv : piv < st.next) :
    last label ((State.serve node piv st us).ops.map D.vop) piv =
      last label (st.ops.map D.vop) piv := by
  rw [(State.serve_ops node piv us st).1, List.map_append, vop_copies_leaf D piv node hn]
  simp only [last, List.foldl_append]
  rw [foldl_sources, ite_eq_right]
  intro h
  have := (List.mem_range'_1.mp h).1
  omega

theorem serve_mono_internal (D : Dag) (R : α → α → Prop) (label : Op → α)
    (node piv : Nat) (hn : D.v ≤ node) (us : List Use) (st : State)
    (cur : Nat → Option α) (hpiv : piv < st.next)
    (hmono : Mono R label (st.ops.map D.vop) cur)
    (hfresh : ∀ s, st.next ≤ s → ((st.ops.map D.vop).foldl (touch label) cur) s = none)
    (hchain : List.IsChain R
      ((((st.ops.map D.vop).foldl (touch label) cur) piv).toList ++
        (List.range' st.next (us.length - 1)).map fun f => label (.copy piv f node))) :
    Mono R label ((State.serve node piv st us).ops.map D.vop) cur := by
  rw [(State.serve_ops node piv us st).1, List.map_append, vop_copies_internal D piv node hn,
    mono_append]
  refine ⟨hmono, mono_copies R label piv node _ _ hchain ?_ List.nodup_range' ?_⟩
  · intro f hf
    exact hfresh f (List.mem_range'_1.mp hf).1
  · intro h
    have := (List.mem_range'_1.mp h).1
    omega

theorem serve_mono_leaf (D : Dag) (R : α → α → Prop) (label : Op → α)
    (node piv : Nat) (hn : node < D.v) (us : List Use) (st : State)
    (cur : Nat → Option α) (hmono : Mono R label (st.ops.map D.vop) cur)
    (hfresh : ∀ s, st.next ≤ s → ((st.ops.map D.vop).foldl (touch label) cur) s = none) :
    Mono R label ((State.serve node piv st us).ops.map D.vop) cur := by
  rw [(State.serve_ops node piv us st).1, List.map_append, vop_copies_leaf D piv node hn,
    mono_append]
  refine ⟨hmono, mono_sources R label node _ _ ?_ List.nodup_range'⟩
  intro f hf
  exact hfresh f (List.mem_range'_1.mp hf).1

/-- Newly allocated copies get their own frame, in either branch of `vop`. -/
theorem serve_copy_frame (D : Dag) (label : Op → α) (node piv : Nat) (us : List Use)
    (st : State) (hpiv : piv < st.next) (s : Nat)
    (hs : s ∈ List.range' st.next (us.length - 1)) :
    last label ((State.serve node piv st us).ops.map D.vop) s =
      some (label (D.vop (.copy piv s node))) := by
  have hsp : s ≠ piv := by have := (List.mem_range'_1.mp hs).1; omega
  rw [(State.serve_ops node piv us st).1, List.map_append]
  by_cases hn : node < D.v
  · rw [vop_copies_leaf D piv node hn]
    simp only [last, List.foldl_append, foldl_sources, hs, ite_true, Dag.vop, hn]
  · rw [vop_copies_internal D piv node (Nat.le_of_not_lt hn)]
    simp only [last, List.foldl_append, foldl_copies_other label piv node s hsp, hs, ite_true,
      Dag.vop, hn, ite_false]

theorem serve_untouched (D : Dag) (label : Op → α) (node piv : Nat) (us : List Use)
    (st : State) (s : Nat) (hsp : s ≠ piv)
    (hs : s ∉ List.range' st.next (us.length - 1)) :
    last label ((State.serve node piv st us).ops.map D.vop) s =
      last label (st.ops.map D.vop) s := by
  rw [(State.serve_ops node piv us st).1, List.map_append]
  by_cases hn : node < D.v
  · rw [vop_copies_leaf D piv node hn]
    simp only [last, List.foldl_append, foldl_sources, hs, ite_false]
  · rw [vop_copies_internal D piv node (Nat.le_of_not_lt hn)]
    simp only [last, List.foldl_append, foldl_copies_other label piv node s hsp, hs, ite_false]

theorem serve_old_frame (D : Dag) (label : Op → α) (node piv : Nat) (us : List Use)
    (st : State) (s : Nat) (hs : s < st.next) (hsp : s ≠ piv) :
    last label ((State.serve node piv st us).ops.map D.vop) s =
      last label (st.ops.map D.vop) s := by
  apply serve_untouched D label node piv us st s hsp
  intro h
  have := (List.mem_range'_1.mp h).1
  omega

theorem serve_fresh (D : Dag) (label : Op → α) (node piv : Nat) (us : List Use)
    (st : State) (hpiv : piv < st.next)
    (hfresh : ∀ s, st.next ≤ s → last label (st.ops.map D.vop) s = none)
    (s : Nat) (hs : (State.serve node piv st us).next ≤ s) :
    last label ((State.serve node piv st us).ops.map D.vop) s = none := by
  rw [(State.serve_ops node piv us st).2] at hs
  have hsp : s ≠ piv := by omega
  have hnot : s ∉ List.range' st.next (us.length - 1) := by
    intro h
    have := (List.mem_range'_1.mp h).2
    omega
  rw [serve_untouched D label node piv us st s hsp hnot]
  exact hfresh s (by omega)

/-- Every newly served use either keeps the pivot or has the frame of its own
fresh copy. The latter is true for both internal and leaf nodes. -/
theorem serve_use_frame (D : Dag) (label : Op → α) (node piv : Nat) (us : List Use)
    (st : State) (hnd : us.Nodup) (hpiv : piv < st.next) (u : Use) (hu : u ∈ us) :
    last label ((State.serve node piv st us).ops.map D.vop) ((State.serve node piv st us).pend u) =
      if (State.serve node piv st us).pend u = piv then
        last label ((State.serve node piv st us).ops.map D.vop) piv
      else some (label (D.vop (.copy piv ((State.serve node piv st us).pend u) node))) := by
  by_cases hp : (State.serve node piv st us).pend u = piv
  · rw [ite_eq_left hp, hp]
  · rw [ite_eq_right hp]
    have hspec := State.serve_spec (fun _ => 0) node piv us st hnd hpiv
      (fun s _ => Dag.contents_zero st s)
    have huse := hspec.2.1 u hu
    have hlow := huse.2.2.resolve_left hp
    have hrange : (State.serve node piv st us).pend u ∈ List.range' st.next (us.length - 1) := by
      apply List.mem_range'_1.mpr
      rw [hspec.1] at huse
      exact ⟨hlow, huse.1⟩
    exact serve_copy_frame D label node piv us st hpiv _ hrange

/-- Both internal branches append an addition and then serve its pivot. -/
theorem step_internal_shape (D : Dag) (node : Nat) (hn : D.v ≤ node) (st : State) :
    ∃ (piv oth : Nat) (st' : State),
      (piv = st.pend (.gate node false) ∨ piv = st.pend (.gate node true)) ∧
      st'.ops = st.ops ++ [Op.add piv oth node] ∧ st'.next = st.next ∧
      D.step st node = State.serve node piv st' (D.freeUses node) := by
  cases hl : D.link node with
  | none =>
    refine ⟨_, _, { st with ops := st.ops ++ [Op.add (st.pend (.gate node false))
      (st.pend (.gate node true)) node] }, Or.inl rfl, rfl, rfl, ?_⟩
    simp only [Dag.step, Nat.not_lt.mpr hn, ite_false, hl]
  | some l =>
    obtain ⟨o, t, pos⟩ := l
    cases o
    · refine ⟨_, _, ({ st with ops := st.ops ++ [Op.add (st.pend (.gate node true))
        (st.pend (.gate node false)) node] }.assign (st.pend (.gate node false)) (.gate t pos)),
        Or.inr rfl, rfl, rfl, ?_⟩
      simp only [Dag.step, Nat.not_lt.mpr hn, ite_false, hl, Bool.false_eq_true]
    · refine ⟨_, _, ({ st with ops := st.ops ++ [Op.add (st.pend (.gate node false))
        (st.pend (.gate node true)) node] }.assign (st.pend (.gate node true)) (.gate t pos)),
        Or.inl rfl, rfl, rfl, ?_⟩
      simp only [Dag.step, Nat.not_lt.mpr hn, ite_false, hl, ite_true]

/-- Serving other uses never changes an existing use's slot. -/
theorem serveRest_pend_other (node piv : Nat) (u : Use) :
    ∀ (us : List Use) (st : State), u ∉ us →
      (State.serveRest node piv st us).pend u = st.pend u
  | [], _, _ => rfl
  | v :: us, st, hu => by
    rw [List.mem_cons, not_or] at hu
    rw [State.serveRest, serveRest_pend_other node piv u us _ hu.2]
    simp [State.assign, Function.update_of_ne hu.1]

theorem serve_pend_other (node piv : Nat) (u : Use) (us : List Use) (st : State)
    (hu : u ∉ us) : (State.serve node piv st us).pend u = st.pend u := by
  cases us with
  | nil => rfl
  | cons v us =>
    rw [List.mem_cons, not_or] at hu
    rw [State.serve, serveRest_pend_other node piv u us _ hu.2]
    simp [State.assign, Function.update_of_ne hu.1]

/-- A use's slot is assigned once, at its actual source node. -/
theorem step_pend_after_source (D : Dag) (hv : D.Valid) (st : State)
    (k : Nat) (hk : k < D.N) (u : Use) (hu : D.srcNode u < k) :
    (D.step st k).pend u = st.pend u := by
  have hf : u ∉ D.freeUses k := fun h => by rw [D.srcNode_free h] at hu; omega
  have hl : D.linkUse k ≠ some u := fun h => by
    rw [D.srcNode_linked hv hk h] at hu
    omega
  unfold Dag.step
  split
  · exact serve_pend_other _ _ _ _ _ hf
  · cases he : D.link k with
    | none => exact serve_pend_other _ _ _ _ _ hf
    | some l =>
      obtain ⟨o, t, pos⟩ := l
      have hne : u ≠ .gate t pos := by
        intro h
        apply hl
        exact D.linkUse_eq.mpr ⟨o, t, pos, he, h⟩
      rw [serve_pend_other _ _ _ _ _ hf]
      simp [State.assign, Function.update_of_ne hne]

/-- Once created, a use keeps its assigned slot throughout all later prefixes. -/
theorem compileTo_pend_after_source (D : Dag) (hv : D.Valid) (u : Use)
    (a b : Nat) (ha : D.srcNode u < a) (hab : a ≤ b) (hb : b ≤ D.N) :
    (D.compileTo b).pend u = (D.compileTo a).pend u := by
  induction b with
  | zero =>
    have h : a = 0 := by omega
    subst a
    rfl
  | succ b ih =>
    by_cases h : a = b + 1
    · subst a; rfl
    · have hab' : a ≤ b := by omega
      have hs : D.compileTo (b + 1) = D.step (D.compileTo b) b := by
        simp [Dag.compileTo, List.range_succ, List.foldl_append]
      rw [hs, step_pend_after_source D hv _ b (by omega) u (by omega)]
      exact ih hab' (by omega)

/-- If a suffix consists of one node, a different final node rules out every touch. -/
theorem untouched_of_last_node_ne (k s : Nat) :
    ∀ (ops : List Op) (cur : Nat → Option Nat),
      (∀ op ∈ ops, op.node = k) →
      (ops.foldl touchOp cur) s ≠ some k →
      (∀ op ∈ ops, s ∉ op.slots) ∧ (ops.foldl touchOp cur) s = cur s
  | [], _, _, _ => ⟨by simp, rfl⟩
  | op :: ops, cur, hn, hlast => by
    obtain ⟨htail, heq⟩ := untouched_of_last_node_ne k s ops (touchOp cur op)
      (fun q hq => hn q (List.mem_cons_of_mem _ hq)) hlast
    have hhead : s ∉ op.slots := by
      intro hs
      apply hlast
      change (ops.foldl touchOp (touchOp cur op)) s = some k
      rw [heq]
      simp [touchOp, hs, hn op (by simp)]
    refine ⟨?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hhead
      · exact htail q hq
    · change (ops.foldl touchOp (touchOp cur op)) s = cur s
      rw [heq]
      simp [touchOp, hhead]

theorem last_append_untouched (label : Op → α) (a b : List Op) (s : Nat)
    (hb : ∀ op ∈ b, s ∉ op.slots) : last label (a ++ b) s = last label a s := by
  have h : ∀ (ops : List Op) (cur : Nat → Option α),
      (∀ op ∈ ops, s ∉ op.slots) → (ops.foldl (touch label) cur) s = cur s := by
    intro ops
    induction ops with
    | nil => intros; rfl
    | cons op ops ih =>
      intro cur hu
      rw [List.foldl_cons, ih _ (fun q hq => hu q (List.mem_cons_of_mem _ hq))]
      simp [touch, hu op (by simp)]
  simpa only [last, List.foldl_append] using h b (last label a) hb

/-- The old node invariant also protects arbitrary operation labels through V leaves. -/
theorem last_vop_append_of_node_ne (D : Dag) (label : Op → α)
    (a b : List Op) (k s : Nat) (hb : ∀ op ∈ b, op.node = k)
    (hlast : lastNode (a ++ b) s ≠ some k) :
    last label ((a ++ b).map D.vop) s = last label (a.map D.vop) s := by
  rw [lastNode_append] at hlast
  have hu := (untouched_of_last_node_ne k s b (lastNode a) hb hlast).1
  rw [List.map_append]
  apply last_append_untouched
  intro op hop hs
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hop
  exact hu q hq (D.vop_slots q s hs)

/-- Later steps preserve the frame of any still-pending use born earlier. -/
theorem step_pending_frame (D : Dag) (hv : D.Valid) (label : Op → α)
    (k : Nat) (hk : k < D.N) (u : Use) (hu : D.Pending (k + 1) u)
    (hsrc : D.srcNode u < k) :
    last label ((D.compileTo (k + 1)).ops.map D.vop) ((D.compileTo (k + 1)).pend u) =
      last label ((D.compileTo k).ops.map D.vop) ((D.compileTo k).pend u) := by
  have hs : D.compileTo (k + 1) = D.step (D.compileTo k) k := by
    simp [Dag.compileTo, List.range_succ, List.foldl_append]
  have hp := step_pend_after_source D hv (D.compileTo k) k hk u hsrc
  have hf := D.finv_compileTo_source hv
    (Le := fun _ _ => True) ⟨fun _ => trivial, fun _ _ _ _ => trivial⟩ (k + 1) (by omega)
  have hl := hf.last u hu
  obtain ⟨new, hops, hn⟩ := D.step_ops (D.compileTo k) k
  rw [hs, hops, hp] at hl ⊢
  apply last_vop_append_of_node_ne D label _ new k _ (fun op hop => (hn op hop).1)
  rw [hl]
  intro he
  have : D.srcNode u = k := Option.some.inj he
  omega

/-- A pending use retains exactly the frame it had immediately after its source. -/
theorem pending_birth_frame (D : Dag) (hv : D.Valid) (label : Op → α)
    (k : Nat) (hk : k ≤ D.N) (u : Use) (hu : D.Pending k u)
    (hsrc : D.srcNode u < k) :
    last label ((D.compileTo k).ops.map D.vop) ((D.compileTo k).pend u) =
      last label ((D.compileTo (D.srcNode u + 1)).ops.map D.vop)
        ((D.compileTo (D.srcNode u + 1)).pend u) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases he : D.srcNode u = k
    · rw [he]
    · have hs : D.srcNode u < k := by omega
      have hf : u ∉ D.freeUses k := fun h => by rw [D.srcNode_free h] at hs; omega
      have hl : D.linkUse k ≠ some u := fun h => by
        rw [D.srcNode_linked hv (by omega) h] at hs
        omega
      rw [step_pending_frame D hv label k (by omega) u hu hs]
      exact ih (by omega) (D.pending_old hv hu hf hl).1 hs

end IntegerMultBounds.MathlibTM2.M8.Local.FrameFlow
