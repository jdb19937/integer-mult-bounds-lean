module

public import IntegerMultBounds.MathlibTM2.M8.Local.Compile

/-!
# The node order of the compiled operations

Each compiled operation belongs to a node (`Op.node`) and touches one or two slots
(`Op.slots`). `lastNode ops s` is the node of the last operation of `ops` touching slot `s`.
For a relation `Le` on nodes, `Mono Le ops` says that every operation finds each of its slots
last touched at a node `n` with `Le n` of its own node.

The source of a pending use (`Dag.srcNode`) is its donor if it is linked, and its node otherwise.
Along the compilation, the slot of every pending use was last touched at the use's source, fresh
slots are untouched, and the operations are monotone for every `Le` that contains each argument
below its node and each donor below its linked user (`FrameOrder`). So the compiled operations
are monotone (`compile_mono`), and each root's slot was last touched at the root's node
(`compile_root_last`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Local

open Classical

namespace Op

/-- The slots an operation touches. -/
def slots : Op → List ℕ
  | .src s _ => [s]
  | .add p o _ => [p, o]
  | .copy p f _ => [p, f]

/-- The node of an operation. -/
def node : Op → ℕ
  | .src _ n => n
  | .add _ _ n => n
  | .copy _ _ n => n

end Op

/-- The last node touching each slot, after one more operation. -/
def touchOp (cur : ℕ → Option ℕ) (op : Op) : ℕ → Option ℕ :=
  fun s => if s ∈ op.slots then some op.node else cur s

/-- The node of the last operation touching each slot. -/
def lastNode (ops : List Op) : ℕ → Option ℕ := ops.foldl touchOp fun _ => none

/-- Every operation finds each of its slots last touched at a node below its own. -/
def Mono (Le : ℕ → ℕ → Prop) : List Op → (ℕ → Option ℕ) → Prop
  | [], _ => True
  | op :: rest, cur =>
    (∀ s ∈ op.slots, ∀ n, cur s = some n → Le n op.node) ∧ Mono Le rest (touchOp cur op)

theorem mono_append (Le : ℕ → ℕ → Prop) :
    ∀ (a b : List Op) (cur : ℕ → Option ℕ),
      Mono Le (a ++ b) cur ↔ Mono Le a cur ∧ Mono Le b (a.foldl touchOp cur)
  | [], b, cur => by simp [Mono]
  | op :: a, b, cur => by
    simp only [List.cons_append, Mono, List.foldl_cons, mono_append Le a b]
    tauto

theorem mono_append' (Le : ℕ → ℕ → Prop) (a b : List Op) :
    Mono Le (a ++ b) (fun _ => none) ↔ Mono Le a (fun _ => none) ∧ Mono Le b (lastNode a) :=
  mono_append Le a b _

theorem lastNode_append (a b : List Op) : lastNode (a ++ b) = b.foldl touchOp (lastNode a) := by
  simp [lastNode, List.foldl_append]

/-- The copies of `piv` into the slots `fs`, at node `node`. -/
def copies (piv : ℕ) (fs : List ℕ) (node : ℕ) : List Op := fs.map fun f => .copy piv f node

theorem foldl_copies (piv node : ℕ) :
    ∀ (fs : List ℕ) (cur : ℕ → Option ℕ), cur piv = some node →
      (copies piv fs node).foldl touchOp cur = fun s => if s ∈ fs then some node else cur s
  | [], cur, _ => by funext s; simp [copies]
  | f :: fs, cur, hpiv => by
    have h1 : touchOp cur (.copy piv f node) piv = some node := by simp [touchOp, Op.slots, Op.node]
    show List.foldl touchOp (touchOp cur (.copy piv f node)) (copies piv fs node) = _
    rw [foldl_copies piv node fs _ h1]
    funext s
    simp only [touchOp, Op.slots, Op.node, List.mem_cons, List.not_mem_nil,
      or_false]
    by_cases h1 : s ∈ fs
    · simp [h1]
    · by_cases h2 : s = f
      · simp [h2]
      · by_cases h3 : s = piv
        · subst h3; simp [h2, hpiv]
        · simp [h1, h2, h3]

theorem mono_copies (Le : ℕ → ℕ → Prop) (piv node : ℕ) (hrefl : Le node node) :
    ∀ (fs : List ℕ) (cur : ℕ → Option ℕ), cur piv = some node → (∀ f ∈ fs, cur f = none) →
      fs.Nodup → piv ∉ fs → Mono Le (copies piv fs node) cur
  | [], _, _, _, _, _ => trivial
  | f :: fs, cur, hpiv, hfresh, hnd, hpf => by
    rw [List.nodup_cons] at hnd
    refine ⟨fun s hs n hn => ?_, ?_⟩
    · simp only [Op.slots, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · rw [hpiv] at hn; cases hn; exact hrefl
      · rw [hfresh s (by simp)] at hn; cases hn
    · apply mono_copies Le piv node hrefl fs
      · simp [touchOp, Op.slots, Op.node]
      · intro g hg
        have hgf : g ≠ f := fun h => hnd.1 (h ▸ hg)
        have hgp : g ≠ piv := fun h => hpf (by rw [← h]; exact List.mem_cons_of_mem _ hg)
        simp only [touchOp, Op.slots, List.mem_cons, List.not_mem_nil, or_false,
          hgf, hgp, ite_false]
        exact hfresh g (List.mem_cons_of_mem _ hg)
      · exact hnd.2
      · exact fun h => hpf (List.mem_cons_of_mem _ h)

/-- The nodes of the operations touching slot `s`, in order. -/
def nodesOf (s : ℕ) (ops : List Op) : List ℕ := (ops.filter fun op => s ∈ op.slots).map Op.node

/-- **Monotone operations as chains.** Along each slot, the nodes of the operations touching it
form a chain, after the node that last touched it before. -/
theorem mono_chain (Le : ℕ → ℕ → Prop) :
    ∀ (ops : List Op) (cur : ℕ → Option ℕ), Mono Le ops cur →
      ∀ s, List.IsChain Le ((cur s).toList ++ nodesOf s ops)
  | [], cur, _, s => by
    cases h : cur s <;> simp [nodesOf]
  | op :: rest, cur, hm, s => by
    have ih := mono_chain Le rest (touchOp cur op) hm.2 s
    by_cases hs : s ∈ op.slots
    · have ht : touchOp cur op s = some op.node := by simp [touchOp, hs]
      rw [ht] at ih
      simp only [nodesOf, List.filter_cons, hs, decide_true, ite_true, List.map_cons] at ih ⊢
      cases hc : cur s with
      | none => simpa using ih
      | some n =>
        simp only [Option.toList_some, List.singleton_append] at ih ⊢
        exact List.isChain_cons_cons.mpr ⟨hm.1 s hs n hc, ih⟩
    · have ht : touchOp cur op s = cur s := by simp [touchOp, hs]
      rw [ht] at ih
      simp only [nodesOf, List.filter_cons, hs, decide_false] at ih ⊢
      exact ih

theorem nodesOf_getLast {s : ℕ} : ∀ (ops : List Op) (cur : ℕ → Option ℕ),
    (ops.foldl touchOp cur) s = ((nodesOf s ops).getLast?).or (cur s)
  | [], cur => by simp [nodesOf]
  | op :: rest, cur => by
    rw [List.foldl_cons, nodesOf_getLast rest (touchOp cur op)]
    by_cases hs : s ∈ op.slots
    · simp only [nodesOf, List.filter_cons, hs, decide_true, ite_true, List.map_cons, touchOp]
      cases h : (List.map Op.node (List.filter (fun op => decide (s ∈ op.slots)) rest)).getLast? <;>
        simp [List.getLast?_cons, h]
    · simp [nodesOf, hs, touchOp]

/-! ### The operations of `serve` -/

namespace State

theorem serveRest_ops (node piv : ℕ) : ∀ (us : List Use) (st : State),
    (serveRest node piv st us).ops = st.ops ++ copies piv (List.range' st.next us.length) node ∧
      (serveRest node piv st us).next = st.next + us.length
  | [], st => by simp [serveRest, copies]
  | u :: us, st => by
    obtain ⟨h1, h2⟩ := serveRest_ops node piv us
      { st.assign st.next u with next := st.next + 1, ops := st.ops ++ [.copy piv st.next node] }
    refine ⟨?_, ?_⟩
    · rw [serveRest, h1]
      simp [copies, List.range'_succ, List.map_cons]
    · rw [serveRest, h2]
      simp only [List.length_cons]
      omega

theorem serve_ops (node piv : ℕ) (us : List Use) (st : State) :
    (serve node piv st us).ops = st.ops ++ copies piv (List.range' st.next (us.length - 1)) node ∧
      (serve node piv st us).next = st.next + (us.length - 1) := by
  cases us with
  | nil => simp [serve, copies]
  | cons u us =>
    obtain ⟨h1, h2⟩ := serveRest_ops node piv us (st.assign piv u)
    simp only [serve]
    exact ⟨by rw [h1]; simp, by rw [h2]; simp⟩

end State

/-! ### Sources of uses -/

namespace Dag
variable (D : Dag)

/-- The donor of a linked use. -/
noncomputable def donor (u : Use) : Option ℕ :=
  if h : ∃ n, n < D.N ∧ D.linkUse n = some u then some (Nat.find h) else none

/-- The source of a use: its donor if it is linked, its node otherwise. -/
noncomputable def srcNode (u : Use) : ℕ := (D.donor u).getD (D.useNode u)

theorem srcNode_linked (hv : D.Valid) {n : ℕ} {u : Use} (hn : n < D.N) (h : D.linkUse n = some u) :
    D.srcNode u = n := by
  have hex : ∃ n, n < D.N ∧ D.linkUse n = some u := ⟨n, hn, h⟩
  simp only [srcNode, donor, dite_eq_left hex, Option.getD_some]
  obtain ⟨-, hm⟩ := Nat.find_spec hex
  obtain ⟨o, t, pos, hl, rfl⟩ := D.linkUse_eq.mp h
  obtain ⟨o', t', pos', hl', he⟩ := D.linkUse_eq.mp hm
  cases he
  exact hv.link_inj _ _ _ _ _ _ hl' hl

theorem srcNode_free {y : ℕ} {u : Use} (h : u ∈ D.freeUses y) : D.srcNode u = y := by
  have hnl : ¬ ∃ n, n < D.N ∧ D.linkUse n = some u := by
    rintro ⟨n, hn, hl⟩
    have := (D.mem_freeUses.mp h).2
    rw [(D.linkedB_iff u).mpr ⟨n, hn, hl⟩] at this
    cases this
  simp only [srcNode, donor, dite_eq_right hnl, Option.getD_none]
  exact D.useNode_of_mem_uses (D.mem_freeUses.mp h).1

/-- What a node order must contain. -/
structure FrameOrder (Le : ℕ → ℕ → Prop) : Prop where
  refl : ∀ n, Le n n
  arg : ∀ k, D.v ≤ k → k < D.N → ∀ pos, Le (D.arg k pos) k
  link : ∀ n o t pos, D.link n = some (o, t, pos) → Le n t

/-- The source of an argument use lies below its node. -/
theorem srcNode_arg_le (hv : D.Valid) {Le : ℕ → ℕ → Prop} (hLe : D.FrameOrder Le) {k : ℕ}
    (hk : D.v ≤ k) (hkN : k < D.N) (pos : Bool) : Le (D.srcNode (.gate k pos)) k := by
  rcases hl : D.linkedB (.gate k pos) with _ | _
  · rw [D.srcNode_free (y := D.arg k pos)
      (D.mem_freeUses.mpr ⟨(D.mem_uses_gate _ k pos).mpr ⟨hkN, hk, rfl⟩, hl⟩)]
    exact hLe.arg k hk hkN pos
  · obtain ⟨n, hn, hlu⟩ := (D.linkedB_iff _).mp hl
    rw [D.srcNode_linked hv hn hlu]
    obtain ⟨o, t, p, hlink, he⟩ := D.linkUse_eq.mp hlu
    cases he
    exact hLe.link n o k pos hlink

/-! ### The frame invariant -/

/-- After the nodes below `k`: pending slots were last touched at their sources, fresh slots
are untouched, and the operations are monotone. -/
structure FInv (Le : ℕ → ℕ → Prop) (k : ℕ) (st : State) : Prop where
  last : ∀ u, D.Pending k u → lastNode st.ops (st.pend u) = some (D.srcNode u)
  fresh : ∀ s, st.next ≤ s → lastNode st.ops s = none
  mono : Mono Le st.ops fun _ => none

theorem finv_start (Le : ℕ → ℕ → Prop) : D.FInv Le 0 start where
  last := fun _ h => by obtain ⟨_, ⟨_, h, _⟩ | ⟨_, h, _⟩⟩ := h <;> omega
  fresh := fun _ _ => rfl
  mono := trivial

theorem runOps_zero : ∀ (ops : List Op) (c : ℕ → ZMod 2), c = (fun _ => 0) →
    runOps (fun _ => 0) ops c = fun _ => 0
  | [], _, hc => hc
  | op :: ops, c, hc => by
    rw [runOps, List.foldl_cons]
    apply runOps_zero ops
    subst hc
    funext s
    cases op <;> simp [Op.run, Function.update_apply]

theorem contents_zero (st : State) (s : ℕ) : st.contents (fun _ => 0) s = 0 := by
  simp [State.contents, runOps_zero st.ops _ rfl]

/-- The serve step keeps the frame invariant, given the state before it. -/
theorem finv_serve (_hv : D.Valid) {Le : ℕ → ℕ → Prop} (hLe : D.FrameOrder Le) {k piv : ℕ}
    {st : State} (hpiv : piv < st.next)
    (hcur : lastNode st.ops piv = some k)
    (hlast : ∀ u, D.Pending (k + 1) u → u ∉ D.freeUses k →
      st.pend u < st.next ∧ st.pend u ≠ piv ∧ lastNode st.ops (st.pend u) = some (D.srcNode u))
    (hfresh : ∀ s, st.next ≤ s → lastNode st.ops s = none)
    (hmono : Mono Le st.ops fun _ => none) :
    D.FInv Le (k + 1) (State.serve k piv st (D.freeUses k)) := by
  obtain ⟨hops, hnext⟩ := State.serve_ops k piv (D.freeUses k) st
  obtain ⟨-, hnew, -, hold, -⟩ := State.serve_spec (fun _ => 0) k piv (D.freeUses k) st
    (D.freeUses_nodup k) hpiv fun s _ => contents_zero st s
  set fs := List.range' st.next ((D.freeUses k).length - 1)
  have hlastF : ∀ s, lastNode (State.serve k piv st (D.freeUses k)).ops s =
      if s ∈ fs then some k else lastNode st.ops s := by
    intro s
    rw [hops, lastNode_append, foldl_copies piv k fs _ hcur]
  refine ⟨fun u hu => ?_, fun s hs => ?_, ?_⟩
  · rw [hlastF]
    by_cases hf : u ∈ D.freeUses k
    · rw [D.srcNode_free hf]
      obtain ⟨hlt, -, hpv⟩ := hnew u hf
      rcases hpv with hpv | hpv
      · rw [hpv]
        split_ifs
        · rfl
        · exact hcur
      · rw [ite_eq_left]
        rw [List.mem_range'_1]
        rw [hnext] at hlt
        exact ⟨by omega, by omega⟩
    · obtain ⟨hlt, -, hl⟩ := hlast u hu hf
      rw [hold u hf, ite_eq_right]
      · exact hl
      · rw [List.mem_range'_1]; omega
  · rw [hlastF, ite_eq_right]
    · exact hfresh s (by rw [hnext] at hs; omega)
    · rw [List.mem_range'_1]; rw [hnext] at hs; omega
  · rw [hops, mono_append']
    refine ⟨hmono, mono_copies Le piv k (hLe.refl k) fs _ hcur (fun f hf => ?_) ?_ ?_⟩
    · exact hfresh f (List.mem_range'_1.mp hf).1
    · exact List.nodup_range'
    · intro h; have := (List.mem_range'_1.mp h).1; omega

/-- **One compiler step** keeps the frame invariant. -/
theorem finv_step (hv : D.Valid) {Le : ℕ → ℕ → Prop} (hLe : D.FrameOrder Le) {k : ℕ}
    (hk : k < D.N) {st : State} (hi : D.Inv (fun _ => 0) k st) (hf : D.FInv Le k st) :
    D.FInv Le (k + 1) (D.step st k) := by
  unfold step
  split_ifs with hleaf
  · -- a leaf
    set st1 : State := { st with next := st.next + 1, ops := st.ops ++ [.src st.next k] } with hst1
    have hl1 : lastNode st1.ops = touchOp (lastNode st.ops) (.src st.next k) := by
      simp [hst1, lastNode_append]
    have hold : ∀ u, D.Pending (k + 1) u → u ∉ D.freeUses k → D.Pending k u := fun u hu hf =>
      (D.pending_old hv hu hf (by rw [D.linkUse_none_of_lt hv hleaf]; simp)).1
    refine D.finv_serve (st := st1) (piv := st.next) hv hLe (by simp [hst1]) ?_ ?_ ?_ ?_
    · rw [hl1]; simp [touchOp, Op.slots, Op.node]
    · intro u hu hfr
      have hp := hold u hu hfr
      have hlt := hi.slot_lt u hp
      refine ⟨by simp [hst1]; omega, by simp [hst1]; omega, ?_⟩
      simp only [hst1]
      rw [hl1]
      simp only [touchOp, Op.slots, List.mem_singleton, Nat.ne_of_lt hlt, ite_false]
      exact hf.last u hp
    · intro s hs
      rw [hl1]
      simp only [hst1] at hs
      simp only [touchOp, Op.slots, List.mem_singleton, show s ≠ st.next by omega, ite_false]
      exact hf.fresh s (by omega)
    · simp only [hst1]
      rw [mono_append']
      refine ⟨hf.mono, fun s hs n hn => ?_, trivial⟩
      simp only [Op.slots, List.mem_singleton] at hs
      subst hs
      rw [hf.fresh _ le_rfl] at hn
      cases hn
  · -- an addition
    have hvk : D.v ≤ k := Nat.le_of_not_lt hleaf
    have hpa := D.pending_arg hv hvk hk false
    have hpb := D.pending_arg hv hvk hk true
    have hab : st.pend (.gate k false) ≠ st.pend (.gate k true) := fun h =>
      absurd (hi.inj _ _ hpa hpb h) (by simp)
    have hne : ∀ u, D.Pending k u → (∀ pos, u ≠ .gate k pos) →
        st.pend u ≠ st.pend (.gate k false) ∧ st.pend u ≠ st.pend (.gate k true) := by
      intro u hu hn
      exact ⟨fun h => hn false (hi.inj _ _ hu hpa h), fun h => hn true (hi.inj _ _ hu hpb h)⟩
    have hla := hf.last _ hpa
    have hlb := hf.last _ hpb
    have hsa := D.srcNode_arg_le hv hLe hvk hk false
    have hsb := D.srcNode_arg_le hv hLe hvk hk true
    have hlta := hi.slot_lt _ hpa
    have hltb := hi.slot_lt _ hpb
    -- the addition of two slots holding the arguments
    have hmono_add : ∀ p o, (p = st.pend (.gate k false) ∧ o = st.pend (.gate k true)) ∨
        (p = st.pend (.gate k true) ∧ o = st.pend (.gate k false)) →
        Mono Le (st.ops ++ [.add p o k]) fun _ => none := by
      intro p o hpo
      rw [mono_append']
      refine ⟨hf.mono, fun s hs n hn => ?_, trivial⟩
      simp only [Op.slots, List.mem_cons, List.not_mem_nil, or_false] at hs
      simp only [Op.node]
      rcases hpo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hs with rfl | rfl
      · rw [hla] at hn; cases hn; exact hsa
      · rw [hlb] at hn; cases hn; exact hsb
      · rw [hlb] at hn; cases hn; exact hsb
      · rw [hla] at hn; cases hn; exact hsa
    cases hl : D.link k with
    | none =>
      set sa := st.pend (.gate k false)
      set sb := st.pend (.gate k true)
      set st1 : State := { st with ops := st.ops ++ [.add sa sb k] } with hst1
      have hl1 : lastNode st1.ops = touchOp (lastNode st.ops) (.add sa sb k) := by
        simp [hst1, lastNode_append]
      have hnl : D.linkUse k = none := by simp [linkUse, hl]
      have hold : ∀ u, D.Pending (k + 1) u → u ∉ D.freeUses k →
          D.Pending k u ∧ ∀ pos, u ≠ .gate k pos := fun u hu hf =>
        D.pending_old hv hu hf (by rw [hnl]; simp)
      refine D.finv_serve (st := st1) (piv := sa) hv hLe hlta ?_ ?_ ?_ ?_
      · rw [hl1]; simp [touchOp, Op.slots, Op.node]
      · intro u hu hfr
        obtain ⟨hp, hnk⟩ := hold u hu hfr
        obtain ⟨h1, h2⟩ := hne u hp hnk
        change st.pend u < st.next ∧ st.pend u ≠ sa ∧ lastNode st1.ops (st.pend u) = _
        refine ⟨hi.slot_lt u hp, h1, ?_⟩
        rw [hl1]
        simp only [touchOp, Op.slots, List.mem_cons, List.not_mem_nil, 
          h1, h2, or_self, ite_false]
        exact hf.last u hp
      · intro s hs
        change st.next ≤ s at hs
        rw [hl1]
        simp only [touchOp, Op.slots, List.mem_cons, List.not_mem_nil, 
          show s ≠ sa by omega, show s ≠ sb by omega, or_self, ite_false]
        exact hf.fresh s hs
      · exact hmono_add sa sb (Or.inl ⟨rfl, rfl⟩)
    | some l =>
      obtain ⟨o, t, pos⟩ := l
      have hlu : D.linkUse k = some (.gate t pos) := by simp [linkUse, hl]
      set sa := st.pend (.gate k false)
      set sb := st.pend (.gate k true)
      set piv := if o then sa else sb
      set oth := if o then sb else sa
      have hpo : (piv = sa ∧ oth = sb) ∨ (piv = sb ∧ oth = sa) := by
        simp only [piv, oth]; split_ifs <;> simp
      set st1 : State := { st with ops := st.ops ++ [.add piv oth k] } with hst1
      set st2 := st1.assign oth (.gate t pos) with hst2
      have hl2 : lastNode st2.ops = touchOp (lastNode st.ops) (.add piv oth k) := by
        simp [hst2, hst1, lastNode_append]
      have hlinked : Use.gate t pos ∉ D.freeUses k := by
        intro h
        have := (D.mem_freeUses.mp h).2
        rw [show D.linkedB (.gate t pos) = true from
          (D.linkedB_iff _).mpr ⟨k, hk, hlu⟩] at this
        cases this
      have hold : ∀ u, D.Pending (k + 1) u → u ∉ D.freeUses k → u ≠ .gate t pos →
          D.Pending k u ∧ ∀ pos, u ≠ .gate k pos := fun u hu hf hne' =>
        D.pending_old hv hu hf (by rw [hlu]; exact fun h => hne' (Option.some.inj h).symm)
      have hpend2 : ∀ u, st2.pend u = if u = .gate t pos then oth else st.pend u := by
        intro u; simp only [hst2, State.assign_pend]
        by_cases h : u = .gate t pos
        · subst h; simp
        · simp [h, hst1]
      have hpivlt : piv < st.next := by rcases hpo with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> assumption
      have hothlt : oth < st.next := by rcases hpo with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> assumption
      have hpivoth : piv ≠ oth := by
        rcases hpo with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
        · exact hab
        · exact Ne.symm hab
      refine D.finv_serve (st := st2) (piv := piv) hv hLe
        (by simp only [hst2, State.assign_next, hst1]; exact hpivlt) ?_ ?_ ?_ ?_
      · rw [hl2]; simp [touchOp, Op.slots, Op.node]
      · intro u hu hfr
        simp only [hst2, State.assign_next, hst1]
        rw [hpend2, hl2]
        split_ifs with h
        · subst h
          refine ⟨hothlt, Ne.symm hpivoth, ?_⟩
          rw [D.srcNode_linked hv hk hlu]
          simp [touchOp, Op.slots, Op.node]
        · obtain ⟨hp, hnk⟩ := hold u hu hfr h
          obtain ⟨h1, h2⟩ := hne u hp hnk
          have hp1 : st.pend u ≠ piv := by rcases hpo with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] <;> assumption
          have hp2 : st.pend u ≠ oth := by rcases hpo with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e] <;> assumption
          refine ⟨hi.slot_lt u hp, hp1, ?_⟩
          simp only [touchOp, Op.slots, List.mem_cons, List.not_mem_nil,
            hp1, hp2, or_self, ite_false]
          exact hf.last u hp
      · intro s hs
        simp only [hst2, State.assign_next, hst1] at hs
        rw [hl2]
        simp only [touchOp, Op.slots, List.mem_cons, List.not_mem_nil, 
          show s ≠ piv by omega, show s ≠ oth by omega, or_self, ite_false]
        exact hf.fresh s hs
      · simp only [hst2, State.assign_ops, hst1]
        exact hmono_add piv oth hpo

theorem finv_compileTo (hv : D.Valid) {Le : ℕ → ℕ → Prop} (hLe : D.FrameOrder Le) :
    ∀ k, k ≤ D.N → D.FInv Le k (D.compileTo k) := by
  intro k
  induction k with
  | zero => intro _; exact D.finv_start Le
  | succ k ih =>
    intro hk
    have h := D.finv_step hv hLe (by omega) (D.inv_compileTo hv _ k (by omega)) (ih (by omega))
    simpa only [compileTo, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      using h

/-- A step appends operations of its own node; sources only at leaves. -/
theorem step_ops (st : State) (k : ℕ) :
    ∃ new, (D.step st k).ops = st.ops ++ new ∧
      ∀ op ∈ new, op.node = k ∧ ∀ s n, op = .src s n → k < D.v := by
  have hcop : ∀ (piv : ℕ) (fs : List ℕ), ∀ op ∈ copies piv fs k,
      op.node = k ∧ ∀ s n, op = .src s n → k < D.v := by
    intro piv fs op hop
    simp only [copies, List.mem_map] at hop
    obtain ⟨f, -, rfl⟩ := hop
    exact ⟨rfl, fun _ _ h => by cases h⟩
  unfold step
  split_ifs with hleaf
  · refine ⟨[.src st.next k] ++
      copies st.next (List.range' (st.next + 1) ((D.freeUses k).length - 1)) k, ?_, ?_⟩
    · rw [(State.serve_ops _ _ _ _).1]; simp
    · intro op hop
      rcases List.mem_append.mp hop with h | h
      · rw [List.mem_singleton] at h; subst h; exact ⟨rfl, fun _ _ _ => hleaf⟩
      · exact hcop _ _ op h
  · cases hl : D.link k with
    | none =>
      refine ⟨[.add (st.pend (.gate k false)) (st.pend (.gate k true)) k] ++
        copies (st.pend (.gate k false)) (List.range' st.next ((D.freeUses k).length - 1)) k, ?_, ?_⟩
      · dsimp only
        rw [(State.serve_ops _ _ _ _).1]; simp
      · intro op hop
        rcases List.mem_append.mp hop with h | h
        · rw [List.mem_singleton] at h; subst h; exact ⟨rfl, fun _ _ h => by cases h⟩
        · exact hcop _ _ op h
    | some l =>
      obtain ⟨o, t, pos⟩ := l
      refine ⟨[.add (if o then st.pend (.gate k false) else st.pend (.gate k true))
        (if o then st.pend (.gate k true) else st.pend (.gate k false)) k] ++
        copies (if o then st.pend (.gate k false) else st.pend (.gate k true))
          (List.range' st.next ((D.freeUses k).length - 1)) k, ?_, ?_⟩
      · dsimp only
        rw [(State.serve_ops _ _ _ _).1]; simp
      · intro op hop
        rcases List.mem_append.mp hop with h | h
        · rw [List.mem_singleton] at h; subst h; exact ⟨rfl, fun _ _ h => by cases h⟩
        · exact hcop _ _ op h

theorem compileTo_ops_node : ∀ k, ∀ op ∈ (D.compileTo k).ops,
    op.node < k ∧ ∀ s n, op = .src s n → n < D.v := by
  intro k
  induction k with
  | zero => intro op h; simp [compileTo, start] at h
  | succ k ih =>
    intro op hop
    have he : D.compileTo (k + 1) = D.step (D.compileTo k) k := by
      simp only [compileTo, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [he] at hop
    obtain ⟨new, hops, hnew⟩ := D.step_ops (D.compileTo k) k
    rw [hops] at hop
    rcases List.mem_append.mp hop with h | h
    · exact ⟨by have := (ih op h).1; omega, (ih op h).2⟩
    · obtain ⟨hn, hs⟩ := hnew op h
      refine ⟨by omega, fun s n e => ?_⟩
      have := hs s n e
      subst e
      simp only [Op.node] at hn
      omega

/-- The compiled operations belong to nodes, sources to leaves. -/
theorem compile_ops_node : ∀ op ∈ D.compile.ops,
    op.node < D.N ∧ ∀ s n, op = .src s n → n < D.v :=
  D.compileTo_ops_node D.N

theorem inv_compile (hv : D.Valid) (x : ℕ → ZMod 2) : D.Inv x D.N D.compile :=
  D.inv_compileTo hv x D.N le_rfl

theorem root_pending (hv : D.Valid) {r : ℕ} (hr : r < D.rootCount) : D.Pending D.N (.root r) :=
  ⟨trivial, Or.inl ⟨D.rootNode r, hv.root_lt r hr,
    D.mem_freeUses.mpr ⟨(D.mem_uses_root _ r).mpr ⟨hr, rfl⟩, D.root_not_linked r⟩⟩⟩

/-- Distinct roots read distinct slots. -/
theorem root_slot_inj (hv : D.Valid) {r r' : ℕ} (hr : r < D.rootCount) (hr' : r' < D.rootCount)
    (h : D.compile.pend (.root r) = D.compile.pend (.root r')) : r = r' := by
  have := (D.inv_compile hv fun _ => 0).inj _ _ (D.root_pending hv hr) (D.root_pending hv hr') h
  injection this

theorem root_slot_lt (hv : D.Valid) {r : ℕ} (hr : r < D.rootCount) :
    D.compile.pend (.root r) < D.compile.next :=
  (D.inv_compile hv fun _ => 0).slot_lt _ (D.root_pending hv hr)

/-- **The compiled operations are monotone.** -/
theorem compile_mono (hv : D.Valid) {Le : ℕ → ℕ → Prop} (hLe : D.FrameOrder Le) :
    Mono Le D.compile.ops fun _ => none :=
  (D.finv_compileTo hv hLe D.N le_rfl).mono

/-- Every root's slot was last touched at the root's node. -/
theorem compile_root_last (hv : D.Valid) {Le : ℕ → ℕ → Prop} (hLe : D.FrameOrder Le) {r : ℕ}
    (hr : r < D.rootCount) :
    lastNode D.compile.ops (D.compile.pend (.root r)) = some (D.rootNode r) := by
  have hu : Use.root r ∈ D.freeUses (D.rootNode r) :=
    D.mem_freeUses.mpr ⟨(D.mem_uses_root _ r).mpr ⟨hr, rfl⟩, D.root_not_linked r⟩
  have hp : D.Pending D.N (.root r) := ⟨trivial, Or.inl ⟨D.rootNode r, hv.root_lt r hr, hu⟩⟩
  have h := (D.finv_compileTo hv hLe D.N le_rfl).last _ hp
  rw [D.srcNode_free hu] at h
  exact h

/-- Along each slot, the nodes of the compiled operations form a chain. -/
theorem compile_chain (hv : D.Valid) {Le : ℕ → ℕ → Prop} (hLe : D.FrameOrder Le) (s : ℕ) :
    (nodesOf s D.compile.ops).IsChain Le := by
  have h := mono_chain Le _ _ (D.compile_mono hv hLe) s
  simpa using h

/-- The last node along a root's slot is the root's node. -/
theorem compile_root_nodes (hv : D.Valid) {Le : ℕ → ℕ → Prop} (hLe : D.FrameOrder Le) {r : ℕ}
    (hr : r < D.rootCount) :
    (nodesOf (D.compile.pend (.root r)) D.compile.ops).getLast? = some (D.rootNode r) := by
  have h := D.compile_root_last hv hLe hr
  rw [lastNode, nodesOf_getLast, Option.or_none] at h
  exact h

end Dag

end IntegerMultBounds.MathlibTM2.M8.Local
