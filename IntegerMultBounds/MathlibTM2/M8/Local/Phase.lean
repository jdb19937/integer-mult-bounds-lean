module

public import IntegerMultBounds.MathlibTM2.M8.Local.VLeaves

/-!
# The first phase of the design-B word

The design-B word runs the side operations in two phases. An addition of node `n` belongs to
the first phase when `Φ n`, a copy of `n` when `Ψ n` (`phase`). The phase hypotheses (`PhaseHyp`)
are local: `Ψ` implies `Φ`; an addition in the first phase has its arguments' copies there and
its linked donor's addition; the retained centres (`cen`) end in the first phase. Every deferred
use (`dset`) is a fresh slot of its node: a copy outside the first phase, or a V slot whose
consumer is outside it.

The compiler invariant `PInv` then gives, for the compiled operations:
* no side operation outside the first phase shares a slot with a later one inside it
  (`Sorted`);
* no side operation outside the first phase touches a centre's slot (`phase_centre`);
* no side operation inside the first phase touches the slot of a deferred use
  (`phase_deferred`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Local

open Networks

namespace Dag
variable (D : Dag) (Φ Ψ cen : ℕ → Bool) (dset : Use → Prop)

/-- The phase of an operation: an addition by `Φ` of its node, a copy by `Ψ`. -/
def phase : Op → Bool
  | .add _ _ n => Φ n
  | .copy _ _ n => Ψ n
  | .src _ _ => false

/-- A side operation of the V word. -/
def side (op : Op) : Bool := !(D.vop op).isSrc

/-- Slot `s` is touched by a side operation of phase `b`. -/
def Hit (b : Bool) (ops : List Op) (s : ℕ) : Prop :=
  ∃ op ∈ ops, D.side op = true ∧ phase Φ Ψ op = b ∧ s ∈ op.slots

/-- No side operation outside the first phase shares a slot with a later one inside it. -/
def Sorted (ops : List Op) : Prop :=
  ops.Pairwise fun o o' => D.side o = true → phase Φ Ψ o = false → D.side o' = true →
    phase Φ Ψ o' = true → ∀ s ∈ o'.slots, s ∉ o.slots

/-- What a use needs: an addition's use its phase, a root use whether it is a centre. -/
def need : Use → Bool
  | .gate t _ => Φ t
  | .root j => cen j

/-- The local phase hypotheses. -/
structure PhaseHyp : Prop where
  psi : ∀ n, Ψ n = true → Φ n = true
  arg : ∀ t, D.v ≤ t → t < D.N → Φ t = true → ∀ pos, D.v ≤ D.arg t pos → Ψ (D.arg t pos) = true
  link : ∀ n o t pos, D.link n = some (o, t, pos) → Φ t = true → Φ n = true
  centre : ∀ j, j < D.rootCount → cen j = true → Ψ (D.rootNode j) = true
  dfr : ∀ u, dset u → u ∈ D.freeUses (D.useNode u) ∧ D.useNode u < D.N ∧
    if D.v ≤ D.useNode u then Ψ (D.useNode u) = false ∧ (D.freeUses (D.useNode u)).head? ≠ some u
    else need Φ cen u = false

/-- The phase invariant after the nodes below `k`. -/
structure PInv (k : ℕ) (st : State) : Prop where
  sorted : D.Sorted Φ Ψ st.ops
  low : ∀ u, D.Pending k u → D.Hit Φ Ψ false st.ops (st.pend u) → need Φ cen u = false
  dfr : ∀ u, dset u → D.useNode u < k →
    ¬ D.Hit Φ Ψ true st.ops (st.pend u) ∧ (D.Hit Φ Ψ false st.ops (st.pend u) ∨
      (D.useNode u < D.v ∧ D.Pending k u ∧ ∀ b, ¬ D.Hit Φ Ψ b st.ops (st.pend u)))

variable {D Φ Ψ cen dset}

theorem hit_append {b : Bool} {a new : List Op} {s : ℕ} :
    D.Hit Φ Ψ b (a ++ new) s ↔ D.Hit Φ Ψ b a s ∨ D.Hit Φ Ψ b new s := by
  simp only [Hit, List.mem_append]
  constructor
  · rintro ⟨op, h | h, h2⟩
    · exact Or.inl ⟨op, h, h2⟩
    · exact Or.inr ⟨op, h, h2⟩
  · rintro (⟨op, h, h2⟩ | ⟨op, h, h2⟩)
    · exact ⟨op, Or.inl h, h2⟩
    · exact ⟨op, Or.inr h, h2⟩

theorem sorted_append {a new : List Op} (ha : D.Sorted Φ Ψ a) (hn : D.Sorted Φ Ψ new)
    (hx : ∀ o' ∈ new, D.side o' = true → phase Φ Ψ o' = true → ∀ s ∈ o'.slots,
      ¬ D.Hit Φ Ψ false a s) : D.Sorted Φ Ψ (a ++ new) := by
  unfold Sorted
  rw [List.pairwise_append]
  refine ⟨ha, hn, fun o ho o' ho' h1 h2 h3 h4 s hs hso => hx o' ho' h3 h4 s hs ⟨o, ho, h1, h2, hso⟩⟩

/-- The first use of `serve` keeps the slot `piv`. -/
theorem serve_head (node piv : ℕ) (st : State) (w : Use) (ws : List Use) (hnd : (w :: ws).Nodup)
    (hpiv : piv < st.next) : (State.serve node piv st (w :: ws)).pend w = piv := by
  have := (State.serveRest_spec (fun _ => 0) node piv ws (st.assign piv w)
    (List.nodup_cons.mp hnd).2 hpiv (fun s _ => contents_zero _ s)).2.2.2.1 w
    (List.nodup_cons.mp hnd).1
  simp only [State.serve]
  rw [this]
  simp

theorem side_of_le {op : Op} (h : D.v ≤ op.node) (hs : op.isSrc = false) : D.side op = true := by
  simp [side, D.vop_of_le h, hs]

theorem not_hit_of_ge {b : Bool} {ops : List Op} {B s : ℕ} (hops : ∀ op ∈ ops, op.SlotsLt B)
    (hs : B ≤ s) : ¬ D.Hit Φ Ψ b ops s := by
  rintro ⟨op, hop, -, -, hso⟩
  have h := hops op hop
  cases op <;> simp_all [Op.SlotsLt, Op.slots] <;> omega

theorem not_hit_nil {b : Bool} {new : List Op} {s : ℕ} (h : ∀ op ∈ new, D.side op = false) :
    ¬ D.Hit Φ Ψ b new s := by
  rintro ⟨op, hop, hs, -⟩
  rw [h op hop] at hs
  cases hs

theorem pinv_start : D.PInv Φ Ψ cen dset 0 start where
  sorted := List.Pairwise.nil
  low := fun _ h => by obtain ⟨_, ⟨_, h, _⟩ | ⟨_, h, _⟩⟩ := h <;> omega
  dfr := fun _ _ h => by omega

theorem useNode_lt_of_pending {k : ℕ} {u : Use} (hv : D.Valid) (h : D.Pending k u)
    (hf : ∃ y, u ∈ D.freeUses y) : D.useNode u < k := by
  obtain ⟨y, hy⟩ := hf
  obtain ⟨-, ⟨y', hy', hu⟩ | ⟨n, hn, hl⟩⟩ := h
  · rw [D.useNode_of_mem_uses (D.mem_freeUses.mp hu).1]; exact hy'
  · exfalso
    have := (D.mem_freeUses.mp hy).2
    rw [(D.linkedB_iff u).mpr ⟨n, by
      obtain ⟨o, t, pos, hl', -⟩ := D.linkUse_eq.mp hl
      exact (hv.link_donor n o t pos hl').2, hl⟩] at this
    cases this

/-- A use that is free is no linked use. -/
theorem free_not_linked {n : ℕ} {u : Use} (hf : u ∈ D.freeUses (D.useNode u)) (hn : n < D.N) :
    D.linkUse n ≠ some u := fun h => by
  have := (D.mem_freeUses.mp hf).2
  rw [(D.linkedB_iff u).mpr ⟨n, hn, h⟩] at this
  cases this

/-- **One compiler step** keeps the phase invariant. -/
theorem pinv_step (hv : D.Valid) (hp : D.PhaseHyp Φ Ψ cen dset) {k : ℕ} (hk : k < D.N)
    {st : State} (hi : D.Inv (fun _ => 0) k st) (hq : D.PInv Φ Ψ cen dset k st) :
    D.PInv Φ Ψ cen dset (k + 1) (D.step st k) := by
  have hlt : ∀ op ∈ st.ops, op.SlotsLt st.next := fun op h => (hi.ops_ok op h).2
  by_cases hleaf : k < D.v
  · -- a leaf: no side operations
    set st1 : State := { st with next := st.next + 1, ops := st.ops ++ [.src st.next k] }
    have hstep : D.step st k = State.serve k st.next st1 (D.freeUses k) := by
      simp [step, hleaf, st1]
    obtain ⟨hops, hnext⟩ := State.serve_ops k st.next (D.freeUses k) st1
    obtain ⟨-, hnew, -, hold, -⟩ := State.serve_spec (fun _ => 0) k st.next (D.freeUses k) st1
      (D.freeUses_nodup k) (by simp [st1]) fun s _ => contents_zero st1 s
    rw [hstep]
    set new := [Op.src st.next k] ++ copies st.next
      (List.range' st1.next ((D.freeUses k).length - 1)) k
    have hops' : (State.serve k st.next st1 (D.freeUses k)).ops = st.ops ++ new := by
      rw [hops]; simp [st1, new]
    have hside : ∀ op ∈ new, D.side op = false := by
      intro op hop
      simp only [new, List.mem_append, List.mem_singleton, copies, List.mem_map] at hop
      rcases hop with rfl | ⟨f, -, rfl⟩
      · rfl
      · simp [side, vop, hleaf, Op.isSrc]
    have hhit : ∀ b s, D.Hit Φ Ψ b (State.serve k st.next st1 (D.freeUses k)).ops s ↔
        D.Hit Φ Ψ b st.ops s := fun b s => by
      rw [hops', hit_append]
      exact ⟨fun h => h.resolve_right (not_hit_nil hside), Or.inl⟩
    have hpold : ∀ u, D.Pending (k + 1) u → u ∉ D.freeUses k → D.Pending k u := fun u hu hf =>
      (D.pending_old hv hu hf (by rw [D.linkUse_none_of_lt hv hleaf]; simp)).1
    have hpend : ∀ u, u ∉ D.freeUses k →
        (State.serve k st.next st1 (D.freeUses k)).pend u = st.pend u := fun u hf => by
      rw [hold u hf]
    refine ⟨?_, ?_, ?_⟩
    · rw [hops']
      refine sorted_append hq.sorted ?_ fun o' ho' h => by rw [hside o' ho'] at h; cases h
      exact List.Pairwise.imp_of_mem (fun _ hb _ _ _ h => by rw [hside _ hb] at h; cases h)
        (List.pairwise_of_forall (R := fun _ _ => True) fun _ _ => trivial)
    · intro u hu h
      rw [hhit] at h
      by_cases hf : u ∈ D.freeUses k
      · exfalso
        rcases (hnew u hf).2.2 with he | he
        · rw [he] at h; exact not_hit_of_ge hlt le_rfl h
        · exact not_hit_of_ge hlt (Nat.le_of_succ_le he) h
      · rw [hpend u hf] at h
        exact hq.low u (hpold u hu hf) h
    · intro u hd hlt'
      obtain ⟨hfu, -, hcase⟩ := hp.dfr u hd
      rw [hhit, hhit]
      by_cases hy : D.useNode u = k
      · rw [hy] at hfu
        have hfresh : st.next ≤ (State.serve k st.next st1 (D.freeUses k)).pend u := by
          rcases (hnew u hfu).2.2 with he | he
          · rw [he]
          · exact Nat.le_of_succ_le he
        have hno : ∀ b, ¬ D.Hit Φ Ψ b st.ops ((State.serve k st.next st1 (D.freeUses k)).pend u) :=
          fun b => not_hit_of_ge hlt hfresh
        refine ⟨hno true, Or.inr ⟨by omega, ⟨?_, Or.inl ⟨k, by omega, hfu⟩⟩, fun b => by
          rw [hhit]; exact hno b⟩⟩
        cases u with
        | gate t pos =>
          have := ((D.mem_uses_gate _ t pos).mp (D.mem_freeUses.mp hfu).1).2.1
          show k + 1 ≤ t
          omega
        | root r => trivial
      · have hf : u ∉ D.freeUses k := fun h =>
          hy (D.useNode_of_mem_uses (D.mem_freeUses.mp h).1)
        rw [hpend u hf]
        obtain ⟨h1, h2⟩ := hq.dfr u hd (by omega)
        refine ⟨h1, h2.imp_right fun ⟨hl, hpk, hn⟩ => ⟨hl, ?_, fun b => by rw [hhit]; exact hn b⟩⟩
        refine ⟨?_, hpk.2.imp (fun ⟨y, hy, hu⟩ => ⟨y, by omega, hu⟩)
          fun ⟨n, hn, hu⟩ => ⟨n, by omega, hu⟩⟩
        cases u with
        | gate t pos =>
          have := ((D.mem_uses_gate _ t pos).mp (D.mem_freeUses.mp hfu).1).2.1
          show k + 1 ≤ t
          have := hpk.1
          simp only [Live] at this
          omega
        | root r => trivial
  · -- an addition
    have hvk : D.v ≤ k := Nat.le_of_not_lt hleaf
    have hpa := D.pending_arg hv hvk hk false
    have hpb := D.pending_arg hv hvk hk true
    have hab : st.pend (.gate k false) ≠ st.pend (.gate k true) := fun h =>
      absurd (hi.inj _ _ hpa hpb h) (by simp)
    have hlta := hi.slot_lt _ hpa
    have hltb := hi.slot_lt _ hpb
    have hne : ∀ u, D.Pending k u → (∀ pos, u ≠ .gate k pos) →
        st.pend u ≠ st.pend (.gate k false) ∧ st.pend u ≠ st.pend (.gate k true) := fun u hu hn =>
      ⟨fun h => hn false (hi.inj _ _ hu hpa h), fun h => hn true (hi.inj _ _ hu hpb h)⟩
    -- the arguments' slots are not hit outside the first phase when `k` is in it
    have harg : ∀ pos, Φ k = true → ¬ D.Hit Φ Ψ false st.ops (st.pend (.gate k pos)) :=
      fun pos hk' h => by
        have := hq.low _ (D.pending_arg hv hvk hk pos) h
        simp only [need] at this
        rw [hk'] at this; cases this
    -- the step: an addition `add piv oth k`, the uses served from `piv`
    obtain ⟨piv, oth, st2, hpo, hst2ops, hst2next, hst2pend, hstep, hlinkcase⟩ :
        ∃ (piv oth : ℕ) (st2 : State),
          ((piv = st.pend (.gate k false) ∧ oth = st.pend (.gate k true)) ∨
            (piv = st.pend (.gate k true) ∧ oth = st.pend (.gate k false))) ∧
          st2.ops = st.ops ++ [Op.add piv oth k] ∧ st2.next = st.next ∧
          (∀ u, (∀ t pos, D.linkUse k = some (.gate t pos) → u ≠ .gate t pos) →
            st2.pend u = st.pend u) ∧
          D.step st k = State.serve k piv st2 (D.freeUses k) ∧
          (∀ t pos, D.linkUse k = some (.gate t pos) → st2.pend (.gate t pos) = oth) := by
      cases hl : D.link k with
      | none =>
        refine ⟨_, _, { st with ops := st.ops ++ [Op.add (st.pend (.gate k false))
          (st.pend (.gate k true)) k] }, Or.inl ⟨rfl, rfl⟩, rfl, rfl, fun _ _ => rfl, ?_, ?_⟩
        · simp [step, hleaf, hl]
        · intro t pos h; simp [linkUse, hl] at h
      | some l =>
        obtain ⟨o, t, pos⟩ := l
        refine ⟨if o then st.pend (.gate k false) else st.pend (.gate k true),
          if o then st.pend (.gate k true) else st.pend (.gate k false),
          ({ st with ops := st.ops ++ [Op.add (if o then st.pend (.gate k false) else
            st.pend (.gate k true)) (if o then st.pend (.gate k true) else
            st.pend (.gate k false)) k] }).assign
            (if o then st.pend (.gate k true) else st.pend (.gate k false)) (.gate t pos),
          by cases o <;> simp, rfl, rfl, ?_, ?_, ?_⟩
        · intro u hu
          have hne' : u ≠ .gate t pos := hu t pos (by simp [linkUse, hl])
          simp [State.assign, Function.update_of_ne hne']
        · simp [step, hleaf, hl]
        · intro t' pos' h
          simp only [linkUse, hl, Option.map_some, Option.some.injEq, Use.gate.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp [State.assign]
    have hpivlt : piv < st.next := by rcases hpo with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> assumption
    have hothlt : oth < st.next := by rcases hpo with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> assumption
    have hpivoth : piv ≠ oth := by
      rcases hpo with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
      · exact hab
      · exact Ne.symm hab
    have hpivarg : ∃ pos, piv = st.pend (.gate k pos) := by
      rcases hpo with ⟨h, -⟩ | ⟨h, -⟩ <;> exact ⟨_, h⟩
    have hotharg : ∃ pos, oth = st.pend (.gate k pos) := by
      rcases hpo with ⟨-, h⟩ | ⟨-, h⟩ <;> exact ⟨_, h⟩
    obtain ⟨hops, hnext⟩ := State.serve_ops k piv (D.freeUses k) st2
    obtain ⟨-, hnew, hinj, hold, -⟩ := State.serve_spec (fun _ => 0) k piv (D.freeUses k) st2
      (D.freeUses_nodup k) (by rw [hst2next]; exact hpivlt) fun s _ => contents_zero st2 s
    rw [hstep]
    set st' := State.serve k piv st2 (D.freeUses k)
    set fs := List.range' st.next ((D.freeUses k).length - 1)
    set new := [Op.add piv oth k] ++ copies piv fs k
    have hops' : st'.ops = st.ops ++ new := by
      rw [hops, hst2ops, hst2next]; simp [new, fs]
    have hfs : ∀ f ∈ fs, st.next ≤ f := fun f hf => (List.mem_range'_1.mp hf).1
    have hnewside : ∀ op ∈ new, D.side op = true := by
      intro op hop
      simp only [new, List.mem_append, List.mem_singleton, copies, List.mem_map] at hop
      rcases hop with rfl | ⟨f, -, rfl⟩ <;> exact side_of_le (by simpa [Op.node] using hvk) rfl
    -- what the new operations hit
    have hnewhit : ∀ b s, D.Hit Φ Ψ b new s ↔
        ((s = piv ∨ s = oth) ∧ Φ k = b) ∨ ((s = piv ∨ s ∈ fs) ∧ fs ≠ [] ∧ Ψ k = b) := by
      intro b s
      constructor
      · rintro ⟨op, hop, -, hph, hs⟩
        simp only [new, List.singleton_append, List.mem_cons, copies, List.mem_map] at hop
        rcases hop with rfl | ⟨f, hf, rfl⟩
        · left
          simp only [Op.slots, List.mem_cons, List.not_mem_nil, or_false] at hs
          exact ⟨hs, hph⟩
        · right
          simp only [Op.slots, List.mem_cons, List.not_mem_nil, or_false] at hs
          refine ⟨?_, List.ne_nil_of_mem hf, hph⟩
          rcases hs with hs | hs
          · exact Or.inl hs
          · exact Or.inr (hs ▸ hf)
      · have hmem : ∀ g ∈ fs, Op.copy piv g k ∈ new := fun g hg => by
          simp only [new, copies, List.mem_append, List.mem_map]
          exact Or.inr ⟨g, hg, rfl⟩
        rintro (⟨hs, hph⟩ | ⟨hs, hne', hph⟩)
        · refine ⟨Op.add piv oth k, by simp [new], hnewside _ (by simp [new]), hph, ?_⟩
          simp only [Op.slots, List.mem_cons, List.not_mem_nil, or_false]
          exact hs
        · obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil fs hne'
          rcases hs with rfl | hs
          · exact ⟨_, hmem f hf, hnewside _ (hmem f hf), hph, by simp [Op.slots]⟩
          · exact ⟨_, hmem s hs, hnewside _ (hmem s hs), hph, by simp [Op.slots]⟩
    -- the first-phase operations of the step hit no slot hit outside it before
    have hcross : ∀ o' ∈ new, D.side o' = true → phase Φ Ψ o' = true → ∀ s ∈ o'.slots,
        ¬ D.Hit Φ Ψ false st.ops s := by
      intro o' ho' _ hph s hs
      simp only [new, List.mem_append, List.mem_singleton, copies, List.mem_map] at ho'
      have hpk : Φ k = true := by
        rcases ho' with rfl | ⟨f, -, rfl⟩
        · exact hph
        · exact hp.psi k hph
      rcases ho' with rfl | ⟨f, hf, rfl⟩
      · simp only [Op.slots, List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · obtain ⟨pos, hpos⟩ := hpivarg; rw [hpos]; exact harg pos hpk
        · obtain ⟨pos, hpos⟩ := hotharg; rw [hpos]; exact harg pos hpk
      · simp only [Op.slots, List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · obtain ⟨pos, hpos⟩ := hpivarg; rw [hpos]; exact harg pos hpk
        · exact not_hit_of_ge hlt (hfs _ hf)
    have hsorted_new : D.Sorted Φ Ψ new := by
      unfold Sorted
      simp only [new, List.singleton_append, List.pairwise_cons]
      refine ⟨?_, ?_⟩
      · intro o' ho' _ h2 _ h4
        simp only [copies, List.mem_map] at ho'
        obtain ⟨f, -, rfl⟩ := ho'
        exact absurd (hp.psi k h4) (by simp_all [phase])
      · refine List.Pairwise.imp_of_mem ?_
          (List.pairwise_of_forall (R := fun _ _ => True) fun _ _ => trivial)
        intro o o' ho ho' _ _ h2 _ h4
        simp only [copies, List.mem_map] at ho ho'
        obtain ⟨f, -, rfl⟩ := ho
        obtain ⟨f', -, rfl⟩ := ho'
        simp only [phase] at h2 h4
        rw [h2] at h4; cases h4
    -- pending uses and their slots
    have hlinkfree : ∀ t pos, D.linkUse k = some (.gate t pos) → Use.gate t pos ∉ D.freeUses k :=
      fun t pos h hf => free_not_linked
        (by rw [D.useNode_of_mem_uses (D.mem_freeUses.mp hf).1]; exact hf) hk h
    have hpend_old : ∀ u, u ∉ D.freeUses k →
        (∀ t pos, D.linkUse k = some (.gate t pos) → u ≠ .gate t pos) → st'.pend u = st.pend u :=
      fun u hf hl => by rw [hold u hf, hst2pend u hl]
    have hpend_link : ∀ t pos, D.linkUse k = some (.gate t pos) → st'.pend (.gate t pos) = oth :=
      fun t pos h => by rw [hold _ (hlinkfree t pos h), hlinkcase t pos h]
    -- a slot hit by the step outside the first phase forces `Ψ k = false`
    have hpsi_of_hit : ∀ s, (s = piv ∨ s ∈ fs) → D.Hit Φ Ψ false st'.ops s → Ψ k = false := by
      intro s hs h
      rw [hops', hit_append, hnewhit] at h
      rcases h with h | (⟨-, h⟩ | ⟨-, -, h⟩)
      · rcases hs with rfl | hs
        · obtain ⟨pos, hpos⟩ := hpivarg
          rw [hpos] at h
          have := hq.low _ (D.pending_arg hv hvk hk pos) h
          simp only [need] at this
          cases hΨ : Ψ k
          · rfl
          · rw [hp.psi k hΨ] at this; cases this
        · exact absurd h (not_hit_of_ge hlt (hfs s hs))
      · cases hΨ : Ψ k
        · rfl
        · rw [hp.psi k hΨ] at h; cases h
      · exact h
    have hfresh_of_free : ∀ u ∈ D.freeUses k, st'.pend u = piv ∨ st'.pend u ∈ fs := by
      intro u hu
      obtain ⟨hl1, -, hl3⟩ := hnew u hu
      rcases hl3 with h | h
      · exact Or.inl h
      · right
        rw [hnext, hst2next] at hl1
        rw [hst2next] at h
        exact List.mem_range'_1.mpr ⟨h, by omega⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hops']; exact sorted_append hq.sorted hsorted_new hcross
    · intro u hu h
      by_cases hf : u ∈ D.freeUses k
      · have hΨk := hpsi_of_hit _ (hfresh_of_free u hf) h
        cases u with
        | gate t pos =>
          obtain ⟨htN, hvt, harg'⟩ := (D.mem_uses_gate _ t pos).mp (D.mem_freeUses.mp hf).1
          simp only [need]
          cases hΦ : Φ t
          · rfl
          · have := hp.arg t hvt htN hΦ pos (by rw [harg']; exact hvk)
            rw [harg', hΨk] at this; cases this
        | root r =>
          obtain ⟨hr, hrk⟩ := (D.mem_uses_root _ r).mp (D.mem_freeUses.mp hf).1
          simp only [need]
          cases hc : cen r
          · rfl
          · have := hp.centre r hr hc
            rw [hrk, hΨk] at this; cases this
      · by_cases hl : ∃ t pos, D.linkUse k = some (.gate t pos) ∧ u = .gate t pos
        · obtain ⟨t, pos, hlk, rfl⟩ := hl
          rw [hpend_link t pos hlk, hops', hit_append, hnewhit] at h
          obtain ⟨o, hlink, -⟩ : ∃ o, D.link k = some (o, t, pos) ∧ True := by
            obtain ⟨o, t', pos', hl', he⟩ := D.linkUse_eq.mp hlk
            cases he
            exact ⟨o, hl', trivial⟩
          have hΦk : Φ k = false := by
            rcases h with h | (⟨-, h⟩ | ⟨hs, -, h⟩)
            · obtain ⟨pos', hpos⟩ := hotharg
              rw [hpos] at h
              have := hq.low _ (D.pending_arg hv hvk hk pos') h
              simpa [need] using this
            · exact h
            · rcases hs with hs | hs
              · exact absurd hs.symm hpivoth
              · exact absurd (hfs _ hs) (by omega)
          simp only [need]
          cases hΦ : Φ t
          · rfl
          · rw [hp.link k o t pos hlink hΦ] at hΦk; cases hΦk
        · have hl' : ∀ t pos, D.linkUse k = some (.gate t pos) → u ≠ .gate t pos :=
            fun t pos h1 h2 => hl ⟨t, pos, h1, h2⟩
          obtain ⟨hpk, hnk⟩ := D.pending_old hv hu hf (by
            intro h
            obtain ⟨o, t, pos, -, he⟩ := D.linkUse_eq.mp h
            exact hl' t pos (by rw [h, he]) he)
          obtain ⟨h1, h2⟩ := hne u hpk hnk
          have hpne : st.pend u ≠ piv ∧ st.pend u ≠ oth := by
            rcases hpo with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> exact ⟨by assumption, by assumption⟩
          rw [hpend_old u hf hl', hops', hit_append, hnewhit] at h
          rcases h with h | (⟨hs, -⟩ | ⟨hs, -⟩)
          · exact hq.low u hpk h
          · rcases hs with hs | hs
            · exact absurd hs hpne.1
            · exact absurd hs hpne.2
          · rcases hs with hs | hs
            · exact absurd hs hpne.1
            · exact absurd (hfs _ hs) (by have := hi.slot_lt u hpk; omega)
    · intro u hd hlt'
      obtain ⟨hfu, -, hcase⟩ := hp.dfr u hd
      by_cases hy : D.useNode u = k
      · -- a deferred copy of `k`: a fresh slot, copied outside the first phase
        rw [hy] at hfu hcase
        rw [ite_eq_left hvk] at hcase
        obtain ⟨hΨk, hhead⟩ := hcase
        have hfs_u : st'.pend u ∈ fs := by
          rcases hfresh_of_free u hfu with h | h
          · exfalso
            obtain ⟨w, ws, hw⟩ : ∃ w ws, D.freeUses k = w :: ws := by
              cases h' : D.freeUses k with
              | nil => rw [h'] at hfu; simp at hfu
              | cons w ws => exact ⟨w, ws, rfl⟩
            have hwpiv : st'.pend w = piv := by
              show (State.serve k piv st2 (D.freeUses k)).pend w = piv
              rw [hw]
              exact serve_head k piv st2 w ws (by rw [← hw]; exact D.freeUses_nodup k)
                (by rw [hst2next]; exact hpivlt)
            have : u = w := hinj u hfu w (by rw [hw]; exact List.mem_cons_self) (h.trans hwpiv.symm)
            rw [hw, this] at hhead
            exact hhead rfl
          · exact h
        have hcopy : D.Hit Φ Ψ false st'.ops (st'.pend u) := by
          rw [hops', hit_append, hnewhit]
          exact Or.inr (Or.inr ⟨Or.inr hfs_u, List.ne_nil_of_mem hfs_u, hΨk⟩)
        refine ⟨fun h => ?_, Or.inl hcopy⟩
        rw [hops', hit_append, hnewhit] at h
        rcases h with h | (⟨hs, -⟩ | ⟨-, -, h⟩)
        · exact not_hit_of_ge hlt (hfs _ hfs_u) h
        · rcases hs with hs | hs
          · exact absurd hs (by have := hfs _ hfs_u; omega)
          · exact absurd hs (by have := hfs _ hfs_u; omega)
        · rw [hΨk] at h; cases h
      · -- an older deferred use
        have hf : u ∉ D.freeUses k := fun h =>
          hy (D.useNode_of_mem_uses (D.mem_freeUses.mp h).1)
        have hl' : ∀ t pos, D.linkUse k = some (.gate t pos) → u ≠ .gate t pos :=
          fun t pos h he => free_not_linked hfu hk (he ▸ h)
        rw [hpend_old u hf hl']
        obtain ⟨h1, h2⟩ := hq.dfr u hd (by omega)
        rcases h2 with h2 | ⟨hleaf', hpk, hno⟩
        · -- already hit outside the first phase: the step's first-phase operations avoid it
          refine ⟨fun h => ?_, Or.inl (by rw [hops', hit_append]; exact Or.inl h2)⟩
          rw [hops', hit_append] at h
          rcases h with h | ⟨o', ho', hs', hph, hso⟩
          · exact h1 h
          · exact hcross o' ho' hs' hph _ hso h2
        · by_cases hc : ∃ pos, u = .gate k pos
          · -- consumed now, outside the first phase
            obtain ⟨pos, rfl⟩ := hc
            rw [ite_eq_right (by omega)] at hcase
            simp only [need] at hcase
            have hΨk : Ψ k = false := by
              cases hΨ : Ψ k
              · rfl
              · rw [hp.psi k hΨ] at hcase; cases hcase
            have hslot : st.pend (.gate k pos) = piv ∨ st.pend (.gate k pos) = oth := by
              rcases hpo with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> cases pos <;> simp_all
            refine ⟨fun h => ?_, Or.inl ?_⟩
            · rw [hops', hit_append, hnewhit] at h
              rcases h with h | (⟨-, h⟩ | ⟨-, -, h⟩)
              · exact hno true h
              · rw [hcase] at h; cases h
              · rw [hΨk] at h; cases h
            · rw [hops', hit_append, hnewhit]
              exact Or.inr (Or.inl ⟨hslot, hcase⟩)
          · -- still pending and untouched
            have hnk : ∀ pos, u ≠ .gate k pos := fun pos h => hc ⟨pos, h⟩
            obtain ⟨e1, e2⟩ := hne u hpk hnk
            have hpne : st.pend u ≠ piv ∧ st.pend u ≠ oth := by
              rcases hpo with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;> rw [f1, f2] <;> exact ⟨by assumption, by assumption⟩
            have hnot : ∀ b, ¬ D.Hit Φ Ψ b st'.ops (st.pend u) := by
              intro b h
              rw [hops', hit_append, hnewhit] at h
              rcases h with h | (⟨hs, -⟩ | ⟨hs, -⟩)
              · exact hno b h
              · rcases hs with hs | hs
                · exact hpne.1 hs
                · exact hpne.2 hs
              · rcases hs with hs | hs
                · exact hpne.1 hs
                · exact absurd (hfs _ hs) (by have := hi.slot_lt u hpk; omega)
            refine ⟨hnot true, Or.inr ⟨hleaf', ⟨?_, ?_⟩, hnot⟩⟩
            · cases u with
              | gate t pos =>
                have := hpk.1
                simp only [Live] at this ⊢
                have : t ≠ k := fun h => hnk pos (h ▸ rfl)
                omega
              | root r => trivial
            · exact hpk.2.imp (fun ⟨y, hy, hu⟩ => ⟨y, by omega, hu⟩)
                fun ⟨n, hn, hu⟩ => ⟨n, by omega, hu⟩

theorem pinv_compileTo (hv : D.Valid) (hp : D.PhaseHyp Φ Ψ cen dset) :
    ∀ k, k ≤ D.N → D.PInv Φ Ψ cen dset k (D.compileTo k) := by
  intro k
  induction k with
  | zero => intro _; exact pinv_start
  | succ k ih =>
    intro hk
    have h := pinv_step hv hp (by omega) (D.inv_compileTo hv _ k (by omega)) (ih (by omega))
    simpa only [compileTo, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      using h

/-! ### What the invariant gives -/

theorem phase_sorted (hv : D.Valid) (hp : D.PhaseHyp Φ Ψ cen dset) :
    D.Sorted Φ Ψ D.compile.ops :=
  (pinv_compileTo hv hp D.N le_rfl).sorted

/-- No side operation outside the first phase touches a centre's slot. -/
theorem phase_centre (hv : D.Valid) (hp : D.PhaseHyp Φ Ψ cen dset) {j : ℕ}
    (hj : j < D.rootCount) (hc : cen j = true) :
    ¬ D.Hit Φ Ψ false D.compile.ops (D.compile.pend (.root j)) := fun h => by
  have := (pinv_compileTo hv hp D.N le_rfl).low _ (D.root_pending hv hj) h
  simp [need, hc] at this

/-- No side operation inside the first phase touches the slot of a deferred use. -/
theorem phase_deferred (hv : D.Valid) (hp : D.PhaseHyp Φ Ψ cen dset) {u : Use} (hu : dset u) :
    ¬ D.Hit Φ Ψ true D.compile.ops (D.compile.pend u) :=
  ((pinv_compileTo hv hp D.N le_rfl).dfr u hu (hp.dfr u hu).2.1).1

end Dag

end IntegerMultBounds.MathlibTM2.M8.Local
