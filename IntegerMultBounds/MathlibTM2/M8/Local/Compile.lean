module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.List.Range
public import Mathlib.Order.Basic

/-!
# The linked slot compiler

An addition DAG on nodes `0, …, N-1` (leaves `0, …, v-1`) is compiled to XOR operations on
numbered slots, in node order:
* a leaf gets a fresh slot, which receives its input (`Op.src`);
* an addition adds the slot of one operand use into the slot of the other (`Op.add piv oth`): the
  first slot now holds the node's value, the second still holds the operand's value;
* a donor node (`Dag.link`) hands that second slot to one later use of the same operand, its
  *linked use*, so that use needs no slot of its own;
* the node's value then serves its *free uses* (all uses except linked ones): the first in the
  slot itself, each other in a fresh slot by a copy (`Op.copy`).

`compile_correct` proves, for a valid DAG (`Dag.Valid`): after the operations, every root's read
slot holds the root's value, on clean input (all slots zero, sources placed by `Op.src`). Slots
are never reused, so the slot count is `v` plus the copies (`compile_next`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Local

/-- A use of a node: argument `pos` of node `t`, or root `r`. -/
inductive Use where
  | gate (t : ℕ) (pos : Bool)
  | root (r : ℕ)
  deriving DecidableEq

/-- An addition DAG with linked operands. -/
structure Dag where
  /-- The number of nodes. -/
  N : ℕ
  /-- The number of leaves, nodes `0, …, v-1`. -/
  v : ℕ
  /-- The two arguments of an addition node. -/
  arg : ℕ → Bool → ℕ
  /-- The number of roots. -/
  rootCount : ℕ
  /-- The node of each root. -/
  rootNode : ℕ → ℕ
  /-- A donor's link: its operand `o` serves argument `pos` of the later node `t`. -/
  link : ℕ → Option (Bool × ℕ × Bool)
  /-- The order in which a node serves its uses: by rank, stably. The first free use keeps the
  node's slot; the others get copies. -/
  rank : ℕ → Use → ℕ := fun _ _ => 0

namespace Dag
variable (D : Dag)

/-- The node a use consumes. -/
def useNode : Use → ℕ
  | .gate t pos => D.arg t pos
  | .root r => D.rootNode r

/-- The use that donor `n` links, if any. -/
def linkUse (n : ℕ) : Option Use := (D.link n).map fun l => .gate l.2.1 l.2.2

/-- Use `u` is the linked use of some donor. -/
def linkedB (u : Use) : Bool := (List.range D.N).any fun n => D.linkUse n == some u

/-- The gate uses of `y`, by user and argument position. -/
def gateUses (y : ℕ) : List Use :=
  (List.range D.N).flatMap fun t =>
    if D.v ≤ t then (([false, true].filter fun pos => D.arg t pos = y)).map (Use.gate t) else []

/-- The root uses of `y`. -/
def rootUses (y : ℕ) : List Use :=
  ((List.range D.rootCount).filter fun r => D.rootNode r = y).map Use.root

/-- All uses of `y`, in serving order. -/
def uses (y : ℕ) : List Use :=
  (D.gateUses y ++ D.rootUses y).mergeSort fun a b => decide (D.rank y a ≤ D.rank y b)

/-- The free uses of `y`: those that no donor links. -/
def freeUses (y : ℕ) : List Use := (D.uses y).filter fun u => !D.linkedB u

/-- The values of the nodes on leaf inputs `x`, over `𝔽₂`. -/
def val (x : ℕ → ZMod 2) : ℕ → ZMod 2
  | n => if _h : n < D.v then x n
    else if h' : D.arg n false < n ∧ D.arg n true < n then
      have := h'.1; have := h'.2
      val x (D.arg n false) + val x (D.arg n true)
    else 0
termination_by n => n

/-- Validity: arguments precede their node; a link names a later user of the same operand and
targets an argument of that user; distinct donors target distinct uses; every node has a free
use; roots are nodes. -/
structure Valid : Prop where
  arg_lt : ∀ n, D.v ≤ n → n < D.N → ∀ pos, D.arg n pos < n
  link_donor : ∀ n o t pos, D.link n = some (o, t, pos) → D.v ≤ n ∧ n < D.N
  link_user : ∀ n o t pos, D.link n = some (o, t, pos) → n < t ∧ t < D.N ∧ D.arg t pos = D.arg n o
  link_inj : ∀ n n' o o' t pos, D.link n = some (o, t, pos) → D.link n' = some (o', t, pos) → n = n'
  free_ne : ∀ y, y < D.N → D.freeUses y ≠ []
  root_lt : ∀ r, r < D.rootCount → D.rootNode r < D.N
  v_le : D.v ≤ D.N

end Dag

/-- A slot operation. -/
inductive Op where
  /-- Slot `s` receives the input of leaf `n`. -/
  | src (s n : ℕ)
  /-- Slot `piv` receives slot `oth`; the node is kept for frame bookkeeping. -/
  | add (piv oth node : ℕ)
  /-- Slot `dst` receives slot `piv`. -/
  | copy (piv dst node : ℕ)
  deriving DecidableEq

namespace Op

/-- One operation on slot contents, with leaf inputs `x`. -/
def run (x : ℕ → ZMod 2) : Op → (ℕ → ZMod 2) → (ℕ → ZMod 2)
  | .src s n, c => Function.update c s (c s + x n)
  | .add p o _, c => Function.update c p (c p + c o)
  | .copy p f _, c => Function.update c f (c f + c p)

/-- The slot an operation writes. -/
def target : Op → ℕ
  | .src s _ => s
  | .add p _ _ => p
  | .copy _ f _ => f

/-- The two slots of an addition or a copy differ. -/
def Distinct : Op → Prop
  | .src _ _ => True
  | .add p o _ => p ≠ o
  | .copy p f _ => p ≠ f

/-- Every slot of the operation is below `B`. -/
def SlotsLt (B : ℕ) : Op → Prop
  | .src s _ => s < B
  | .add p o _ => p < B ∧ o < B
  | .copy p f _ => p < B ∧ f < B

theorem SlotsLt.mono {B B' : ℕ} (h : B ≤ B') : ∀ {op : Op}, op.SlotsLt B → op.SlotsLt B'
  | .src _ _, hs => lt_of_lt_of_le hs h
  | .add _ _ _, hs => ⟨lt_of_lt_of_le hs.1 h, lt_of_lt_of_le hs.2 h⟩
  | .copy _ _ _, hs => ⟨lt_of_lt_of_le hs.1 h, lt_of_lt_of_le hs.2 h⟩

end Op

/-- Run a list of operations. -/
def runOps (x : ℕ → ZMod 2) (ops : List Op) (c : ℕ → ZMod 2) : ℕ → ZMod 2 :=
  ops.foldl (fun c op => op.run x c) c

/-- The compiler state. -/
structure State where
  /-- The next fresh slot. -/
  next : ℕ
  /-- The slot serving each pending use. -/
  pend : Use → ℕ
  /-- The emitted operations, in order. -/
  ops : List Op
  /-- The read slot of each root, in order of assignment. -/
  reads : List (ℕ × ℕ)

namespace State

/-- Slot `s` serves use `u`; a root use is recorded as a read. -/
def assign (st : State) (s : ℕ) (u : Use) : State :=
  { st with
    pend := Function.update st.pend u s
    reads := match u with
      | .root r => st.reads ++ [(s, r)]
      | .gate _ _ => st.reads }

/-- Every use after the first gets a fresh slot, which copies `piv`. -/
def serveRest (node piv : ℕ) : State → List Use → State
  | st, [] => st
  | st, u :: us =>
    serveRest node piv
      ({ st.assign st.next u with next := st.next + 1, ops := st.ops ++ [.copy piv st.next node] })
      us

/-- Slot `piv` serves the first use, fresh copies the others. -/
def serve (node piv : ℕ) (st : State) : List Use → State
  | [] => st
  | u :: us => serveRest node piv (st.assign piv u) us

end State

namespace Dag
variable (D : Dag)

/-- Compile node `n`. -/
def step (st : State) (n : ℕ) : State :=
  if n < D.v then
    State.serve n st.next { st with next := st.next + 1, ops := st.ops ++ [Op.src st.next n] }
      (D.freeUses n)
  else
    let sa := st.pend (.gate n false)
    let sb := st.pend (.gate n true)
    match D.link n with
    | some (o, t, pos) =>
      let piv := if o then sa else sb
      let oth := if o then sb else sa
      State.serve n piv ({ st with ops := st.ops ++ [Op.add piv oth n] }.assign oth (.gate t pos))
        (D.freeUses n)
    | none => State.serve n sa { st with ops := st.ops ++ [Op.add sa sb n] } (D.freeUses n)

/-- The empty state. -/
def start : State := ⟨0, fun _ => 0, [], []⟩

/-- Compile nodes `0, …, k-1`. -/
def compileTo (k : ℕ) : State := (List.range k).foldl D.step start

/-- The compiled DAG. -/
def compile : State := D.compileTo D.N

end Dag

/-! ### Running operations -/

theorem runOps_append (x : ℕ → ZMod 2) (a b : List Op) (c : ℕ → ZMod 2) :
    runOps x (a ++ b) c = runOps x b (runOps x a c) := by
  simp [runOps, List.foldl_append]

theorem runOps_singleton (x : ℕ → ZMod 2) (op : Op) (c : ℕ → ZMod 2) :
    runOps x [op] c = op.run x c := rfl

namespace State

/-- The slot contents after the emitted operations, from zero contents. -/
def contents (x : ℕ → ZMod 2) (st : State) : ℕ → ZMod 2 := runOps x st.ops fun _ => 0

@[simp] theorem assign_next (st : State) (s : ℕ) (u : Use) : (st.assign s u).next = st.next := rfl
@[simp] theorem assign_ops (st : State) (s : ℕ) (u : Use) : (st.assign s u).ops = st.ops := rfl
@[simp] theorem assign_pend (st : State) (s : ℕ) (u : Use) :
    (st.assign s u).pend = Function.update st.pend u s := rfl

theorem contents_assign (x : ℕ → ZMod 2) (st : State) (s : ℕ) (u : Use) :
    (st.assign s u).contents x = st.contents x := rfl

theorem reads_assign_sub (st : State) (s : ℕ) (u : Use) : ∀ p ∈ st.reads, p ∈ (st.assign s u).reads := by
  intro p hp
  cases u <;> simp [assign, hp]

theorem reads_assign_root (st : State) (s r : ℕ) : (s, r) ∈ (st.assign s (.root r)).reads := by
  simp [assign]

/-- The fresh slots of `serveRest`: one per use, from `st.next` on, each a copy of `piv`. -/
theorem serveRest_spec (x : ℕ → ZMod 2) (node piv : ℕ) :
    ∀ (us : List Use) (st : State), us.Nodup → piv < st.next →
      (∀ s, st.next ≤ s → st.contents x s = 0) →
      let st' := serveRest node piv st us
      st'.next = st.next + us.length ∧
      (∀ u ∈ us, st.next ≤ st'.pend u ∧ st'.pend u < st'.next ∧
        st'.contents x (st'.pend u) = st.contents x piv) ∧
      (∀ u ∈ us, ∀ u' ∈ us, st'.pend u = st'.pend u' → u = u') ∧
      (∀ u, u ∉ us → st'.pend u = st.pend u) ∧
      (∀ s, s < st.next → st'.contents x s = st.contents x s) ∧
      (∀ s, st'.next ≤ s → st'.contents x s = 0) ∧
      (∀ p ∈ st.reads, p ∈ st'.reads) ∧
      (∀ r, Use.root r ∈ us → (st'.pend (.root r), r) ∈ st'.reads) ∧
      (∀ op ∈ st'.ops, op ∈ st.ops ∨ ∃ f, st.next ≤ f ∧ f < st'.next ∧ op = .copy piv f node) := by
  intro us
  induction us with
  | nil =>
    intro st _ _ hz
    exact ⟨by simp [serveRest], by simp, by simp, fun _ _ => rfl, fun _ _ => rfl, hz,
      fun _ h => h, by simp, fun _ h => Or.inl h⟩
  | cons u us ih =>
    intro st hnd hpiv hz
    rw [List.nodup_cons] at hnd
    set st1 : State :=
      { st.assign st.next u with next := st.next + 1, ops := st.ops ++ [.copy piv st.next node] }
      with hst1
    have hc1 : st1.contents x = Function.update (st.contents x) st.next
        (st.contents x st.next + st.contents x piv) := by
      simp only [contents, hst1, runOps_append, runOps_singleton, Op.run]
    have hz1 : ∀ s, st1.next ≤ s → st1.contents x s = 0 := by
      intro s hs
      rw [hc1, Function.update_of_ne (by simp [hst1] at hs; omega)]
      exact hz s (by simp [hst1] at hs; omega)
    have hpiv1 : piv < st1.next := by simp [hst1]; omega
    obtain ⟨hn, hfresh, hinj, hold, hlow, hzero, hreads, hroot, hops⟩ := ih st1 hnd.2 hpiv1 hz1
    set st' := serveRest node piv st1 us with hst'
    have hserve : serveRest node piv st (u :: us) = st' := rfl
    rw [hserve]
    have hnext1 : st1.next = st.next + 1 := rfl
    have hpend1 : st1.pend = Function.update st.pend u st.next := rfl
    -- the first use keeps slot `st.next`
    have hu' : st'.pend u = st.next := by
      rw [hold u hnd.1, hpend1, Function.update_self]
    have hcu : st'.contents x st.next = st.contents x piv := by
      rw [hlow st.next (by omega), hc1, Function.update_self, hz st.next le_rfl, zero_add]
    refine ⟨by rw [hn, hnext1, List.length_cons]; omega, ?_, ?_, ?_, ?_, hzero, ?_, ?_, ?_⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact ⟨by rw [hu'], by rw [hu', hn, hnext1]; omega, by rw [hu', hcu]⟩
      · obtain ⟨h1, h2, h3⟩ := hfresh w hw
        refine ⟨by omega, h2, ?_⟩
        rw [h3, hc1, Function.update_of_ne (by omega)]
    · intro w hw w' hw' heq
      rcases List.mem_cons.mp hw with rfl | hw1 <;> rcases List.mem_cons.mp hw' with rfl | hw1'
      · rfl
      · exfalso; have := (hfresh w' hw1').1; rw [hu'] at heq; omega
      · exfalso; have := (hfresh w hw1).1; rw [hu'] at heq; omega
      · exact hinj w hw1 w' hw1' heq
    · intro w hw
      have hw1 : w ≠ u := fun h => hw (h ▸ List.mem_cons_self)
      have hw2 : w ∉ us := fun h => hw (List.mem_cons_of_mem _ h)
      rw [hold w hw2, hpend1, Function.update_of_ne hw1]
    · intro s hs
      rw [hlow s (by omega), hc1, Function.update_of_ne (by omega)]
    · intro p hp
      exact hreads p (reads_assign_sub st st.next u p hp)
    · intro r hr
      rcases List.mem_cons.mp hr with h | hr
      · subst h
        rw [hu']
        exact hreads _ (reads_assign_root st st.next r)
      · exact hroot r hr
    · intro op hop
      rcases hops op hop with h | ⟨f, hf1, hf2, rfl⟩
      · have h' : op ∈ st.ops ++ [.copy piv st.next node] := h
        rcases List.mem_append.mp h' with h | h
        · exact Or.inl h
        · rw [List.mem_singleton] at h
          exact Or.inr ⟨st.next, le_rfl, by rw [hn, hnext1]; omega, h⟩
      · exact Or.inr ⟨f, by rw [hnext1] at hf1; omega, hf2, rfl⟩

/-- `serve`: the first use in slot `piv`, the others in fresh copies of it. -/
theorem serve_spec (x : ℕ → ZMod 2) (node piv : ℕ) (us : List Use) (st : State)
    (hnd : us.Nodup) (hpiv : piv < st.next) (hz : ∀ s, st.next ≤ s → st.contents x s = 0) :
    let st' := serve node piv st us
    st'.next = st.next + (us.length - 1) ∧
    (∀ u ∈ us, st'.pend u < st'.next ∧ st'.contents x (st'.pend u) = st.contents x piv ∧
      (st'.pend u = piv ∨ st.next ≤ st'.pend u)) ∧
    (∀ u ∈ us, ∀ u' ∈ us, st'.pend u = st'.pend u' → u = u') ∧
    (∀ u, u ∉ us → st'.pend u = st.pend u) ∧
    (∀ s, s < st.next → s ≠ piv → st'.contents x s = st.contents x s) ∧
    st'.contents x piv = st.contents x piv ∧
    (∀ s, st'.next ≤ s → st'.contents x s = 0) ∧
    (∀ p ∈ st.reads, p ∈ st'.reads) ∧
    (∀ r, Use.root r ∈ us → (st'.pend (.root r), r) ∈ st'.reads) ∧
    (∀ op ∈ st'.ops, op ∈ st.ops ∨ ∃ f, st.next ≤ f ∧ f < st'.next ∧ op = .copy piv f node) := by
  cases us with
  | nil =>
    exact ⟨by simp [serve], by simp, by simp, fun _ _ => rfl, fun _ _ _ => rfl, rfl, hz,
      fun _ h => h, by simp, fun _ h => Or.inl h⟩
  | cons u us =>
    rw [List.nodup_cons] at hnd
    set st1 := st.assign piv u with hst1
    have hz1 : ∀ s, st1.next ≤ s → st1.contents x s = 0 := hz
    obtain ⟨hn, hfresh, hinj, hold, hlow, hzero, hreads, hroot, hops⟩ :=
      serveRest_spec x node piv us st1 hnd.2 hpiv hz1
    set st' := serveRest node piv st1 us with hst'
    have hserve : serve node piv st (u :: us) = st' := rfl
    rw [hserve]
    have hu' : st'.pend u = piv := by
      rw [hold u hnd.1]; simp [hst1]
    refine ⟨by rw [hn, List.length_cons]; simp [hst1], ?_, ?_, ?_, ?_, ?_, hzero, ?_, ?_, ?_⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · refine ⟨by rw [hu', hn]; simp [hst1]; omega, ?_, Or.inl hu'⟩
        rw [hu', hlow piv hpiv]; rfl
      · obtain ⟨h1, h2, h3⟩ := hfresh w hw
        exact ⟨h2, by rw [h3]; rfl, Or.inr h1⟩
    · intro w hw w' hw' heq
      rcases List.mem_cons.mp hw with rfl | hw1 <;> rcases List.mem_cons.mp hw' with rfl | hw1'
      · rfl
      · exfalso; have := (hfresh w' hw1').1; rw [hu'] at heq; simp [hst1] at this; omega
      · exfalso; have := (hfresh w hw1).1; rw [hu'] at heq; simp [hst1] at this; omega
      · exact hinj w hw1 w' hw1' heq
    · intro w hw
      have hw1 : w ≠ u := fun h => hw (h ▸ List.mem_cons_self)
      have hw2 : w ∉ us := fun h => hw (List.mem_cons_of_mem _ h)
      rw [hold w hw2]; simp [hst1, Function.update_of_ne hw1]
    · intro s hs _
      rw [hlow s hs]; rfl
    · rw [hlow piv hpiv]; rfl
    · intro p hp
      exact hreads p (reads_assign_sub st piv u p hp)
    · intro r hr
      rcases List.mem_cons.mp hr with h | hr
      · subst h
        rw [hu']
        exact hreads _ (reads_assign_root st piv r)
      · exact hroot r hr
    · intro op hop
      rcases hops op hop with h | ⟨f, hf1, hf2, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨f, by simpa [hst1] using hf1, hf2, rfl⟩

end State

/-! ### Uses -/

namespace Dag
variable (D : Dag)

theorem mem_gateUses (y t : ℕ) (pos : Bool) :
    Use.gate t pos ∈ D.gateUses y ↔ t < D.N ∧ D.v ≤ t ∧ D.arg t pos = y := by
  simp only [gateUses, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨t', ht', hm⟩
    split_ifs at hm with hv
    · obtain ⟨p, hp, he⟩ := List.mem_map.mp hm
      cases he
      simp only [List.mem_filter, decide_eq_true_eq] at hp
      exact ⟨ht', hv, hp.2⟩
    · simp at hm
  · rintro ⟨ht, hv, ha⟩
    refine ⟨t, ht, ?_⟩
    rw [ite_eq_left hv]
    exact List.mem_map.mpr ⟨pos, by cases pos <;> simp [ha], rfl⟩

theorem root_not_mem_gateUses (y r : ℕ) : Use.root r ∉ D.gateUses y := by
  simp only [gateUses, List.mem_flatMap, not_exists, not_and]
  intro t _ hm
  split_ifs at hm
  · obtain ⟨p, _, he⟩ := List.mem_map.mp hm
    cases he
  · simp at hm

theorem mem_rootUses (y r : ℕ) : Use.root r ∈ D.rootUses y ↔ r < D.rootCount ∧ D.rootNode r = y := by
  simp [rootUses]

theorem gate_not_mem_rootUses (y t : ℕ) (pos : Bool) : Use.gate t pos ∉ D.rootUses y := by
  simp [rootUses]

theorem mem_uses_gate (y t : ℕ) (pos : Bool) :
    Use.gate t pos ∈ D.uses y ↔ t < D.N ∧ D.v ≤ t ∧ D.arg t pos = y := by
  rw [uses, List.mem_mergeSort, List.mem_append, mem_gateUses]
  simp [gate_not_mem_rootUses]

theorem mem_uses_root (y r : ℕ) : Use.root r ∈ D.uses y ↔ r < D.rootCount ∧ D.rootNode r = y := by
  rw [uses, List.mem_mergeSort, List.mem_append, mem_rootUses]
  simp [root_not_mem_gateUses]

theorem useNode_of_mem_uses {y : ℕ} {u : Use} (h : u ∈ D.uses y) : D.useNode u = y := by
  cases u with
  | gate t pos => exact ((D.mem_uses_gate y t pos).mp h).2.2
  | root r => exact ((D.mem_uses_root y r).mp h).2

theorem gateUses_nodup (y : ℕ) : (D.gateUses y).Nodup := by
  unfold gateUses
  apply List.nodup_flatMap.mpr
  refine ⟨fun t _ => ?_, ?_⟩
  · split_ifs
    · apply List.Nodup.map (fun _ _ h => by cases h; rfl)
      exact List.Nodup.filter _ (by decide)
    · exact List.nodup_nil
  · apply List.nodup_range.pairwise_of_forall_ne
    intro t _ t' _ hne
    simp only [Function.onFun]
    rw [List.disjoint_iff_ne]
    intro a ha b hb heq
    subst heq
    split_ifs at ha hb
    · obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨p', _, he⟩ := List.mem_map.mp hb
      cases he
      exact hne rfl
    all_goals simp_all

theorem rootUses_nodup (y : ℕ) : (D.rootUses y).Nodup :=
  List.Nodup.map (fun _ _ h => by cases h; rfl) (List.Nodup.filter _ List.nodup_range)

theorem uses_nodup (y : ℕ) : (D.uses y).Nodup := by
  rw [uses, (List.mergeSort_perm _ _).nodup_iff, List.nodup_append]
  refine ⟨D.gateUses_nodup y, D.rootUses_nodup y, ?_⟩
  intro a ha b hb heq
  subst heq
  cases a with
  | gate t pos => exact D.gate_not_mem_rootUses y t pos hb
  | root r => exact D.root_not_mem_gateUses y r ha

theorem freeUses_nodup (y : ℕ) : (D.freeUses y).Nodup := (D.uses_nodup y).filter _

theorem mem_freeUses {y : ℕ} {u : Use} : u ∈ D.freeUses y ↔ u ∈ D.uses y ∧ D.linkedB u = false := by
  simp [freeUses]

theorem linkedB_iff (u : Use) : D.linkedB u = true ↔ ∃ n < D.N, D.linkUse n = some u := by
  simp [linkedB]

theorem linkUse_eq {n : ℕ} {u : Use} :
    D.linkUse n = some u ↔ ∃ o t pos, D.link n = some (o, t, pos) ∧ u = .gate t pos := by
  unfold linkUse
  cases h : D.link n with
  | none => simp
  | some l =>
    obtain ⟨o, t, pos⟩ := l
    simp only [Option.map_some, Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨o, t, pos, rfl, rfl⟩
    · rintro ⟨o', t', pos', he, rfl⟩
      obtain ⟨rfl, rfl, rfl⟩ : o = o' ∧ t = t' ∧ pos = pos' := by simpa using he
      rfl

theorem root_not_linked (D : Dag) (r : ℕ) : D.linkedB (.root r) = false := by
  rcases hb : D.linkedB (.root r) with _ | _
  · rfl
  · obtain ⟨n, _, hn⟩ := (D.linkedB_iff _).mp hb
    obtain ⟨_, _, _, _, he⟩ := D.linkUse_eq.mp hn
    cases he

theorem val_leaf (x : ℕ → ZMod 2) {n : ℕ} (h : n < D.v) : D.val x n = x n := by
  rw [val, dite_eq_left h]

theorem val_add (x : ℕ → ZMod 2) {n : ℕ} (h : D.v ≤ n) (ha : D.arg n false < n)
    (hb : D.arg n true < n) : D.val x n = D.val x (D.arg n false) + D.val x (D.arg n true) := by
  rw [val, dite_eq_right (by omega), dite_eq_left ⟨ha, hb⟩]

/-! ### The compiler invariant -/

/-- A use is live after nodes below `k` if no node below `k` consumes it. -/
def Live (k : ℕ) : Use → Prop
  | .gate t _ => k ≤ t
  | .root _ => True

/-- The pending uses after compiling the nodes below `k`: live free uses of compiled nodes and
live linked uses of compiled donors. -/
def Pending (k : ℕ) (u : Use) : Prop :=
  Live k u ∧ ((∃ y < k, u ∈ D.freeUses y) ∨ (∃ n < k, D.linkUse n = some u))

/-- The compiler invariant after the nodes below `k`, on leaf inputs `x`. -/
structure Inv (x : ℕ → ZMod 2) (k : ℕ) (st : State) : Prop where
  slot_lt : ∀ u, D.Pending k u → st.pend u < st.next
  value : ∀ u, D.Pending k u → st.contents x (st.pend u) = D.val x (D.useNode u)
  inj : ∀ u u', D.Pending k u → D.Pending k u' → st.pend u = st.pend u' → u = u'
  fresh : ∀ s, st.next ≤ s → st.contents x s = 0
  reads : ∀ r, D.Pending k (.root r) → (st.pend (.root r), r) ∈ st.reads
  ops_ok : ∀ op ∈ st.ops, op.Distinct ∧ op.SlotsLt st.next

theorem inv_start (x : ℕ → ZMod 2) : D.Inv x 0 start where
  slot_lt := fun _ h => by obtain ⟨_, ⟨_, h, _⟩ | ⟨_, h, _⟩⟩ := h <;> omega
  value := fun _ h => by obtain ⟨_, ⟨_, h, _⟩ | ⟨_, h, _⟩⟩ := h <;> omega
  inj := fun _ _ h => by obtain ⟨_, ⟨_, h, _⟩ | ⟨_, h, _⟩⟩ := h <;> omega
  fresh := fun _ _ => rfl
  reads := fun _ h => by obtain ⟨_, ⟨_, h, _⟩ | ⟨_, h, _⟩⟩ := h <;> omega
  ops_ok := fun _ h => by simp [start] at h

theorem live_succ {k : ℕ} {u : Use} (h : Live (k + 1) u) : Live k u := by
  cases u with
  | gate t pos => exact Nat.le_of_succ_le h
  | root r => trivial

/-- The arguments of an addition node `k` are pending when it is compiled. -/
theorem pending_arg (hv : D.Valid) {k : ℕ} (hk : D.v ≤ k) (hkN : k < D.N) (pos : Bool) :
    D.Pending k (.gate k pos) := by
  refine ⟨le_rfl, ?_⟩
  rcases hl : D.linkedB (.gate k pos) with _ | _
  · exact Or.inl ⟨D.arg k pos, hv.arg_lt k hk hkN pos,
      D.mem_freeUses.mpr ⟨(D.mem_uses_gate _ k pos).mpr ⟨hkN, hk, rfl⟩, hl⟩⟩
  · obtain ⟨n, _, hn⟩ := (D.linkedB_iff _).mp hl
    obtain ⟨o, t, p, hlink, he⟩ := D.linkUse_eq.mp hn
    cases he
    exact Or.inr ⟨n, (hv.link_user n o k pos hlink).1, hn⟩

/-- A pending use after node `k` that is neither a free use of `k` nor `k`'s linked use was
pending before node `k`, and is not an argument of `k`. -/
theorem pending_old (_hv : D.Valid) {k : ℕ} {u : Use} (h : D.Pending (k + 1) u)
    (hfree : u ∉ D.freeUses k) (hlink : D.linkUse k ≠ some u) :
    D.Pending k u ∧ ∀ pos, u ≠ .gate k pos := by
  obtain ⟨hl, hy | hn⟩ := h
  · obtain ⟨y, hy, hu⟩ := hy
    have hyk : y ≠ k := fun h => hfree (h ▸ hu)
    refine ⟨⟨live_succ hl, Or.inl ⟨y, by omega, hu⟩⟩, ?_⟩
    rintro pos rfl
    exact absurd hl (by simp [Live])
  · obtain ⟨n, hn, hu⟩ := hn
    have hnk : n ≠ k := fun h => hlink (h ▸ hu)
    refine ⟨⟨live_succ hl, Or.inr ⟨n, by omega, hu⟩⟩, ?_⟩
    rintro pos rfl
    exact absurd hl (by simp [Live])

/-- The state just before node `k` serves its free uses from slot `piv`. -/
structure Pre (x : ℕ → ZMod 2) (k piv : ℕ) (st : State) : Prop where
  piv_lt : piv < st.next
  piv_val : st.contents x piv = D.val x k
  slot_lt : ∀ u, D.Pending (k + 1) u → u ∉ D.freeUses k → st.pend u < st.next
  slot_ne : ∀ u, D.Pending (k + 1) u → u ∉ D.freeUses k → st.pend u ≠ piv
  value : ∀ u, D.Pending (k + 1) u → u ∉ D.freeUses k →
    st.contents x (st.pend u) = D.val x (D.useNode u)
  inj : ∀ u u', D.Pending (k + 1) u → u ∉ D.freeUses k → D.Pending (k + 1) u' →
    u' ∉ D.freeUses k → st.pend u = st.pend u' → u = u'
  fresh : ∀ s, st.next ≤ s → st.contents x s = 0
  reads : ∀ r, D.Pending (k + 1) (.root r) → Use.root r ∉ D.freeUses k →
    (st.pend (.root r), r) ∈ st.reads
  ops_ok : ∀ op ∈ st.ops, op.Distinct ∧ op.SlotsLt st.next

theorem inv_of_pre (x : ℕ → ZMod 2) {k piv : ℕ} {st : State} (hp : D.Pre x k piv st) :
    D.Inv x (k + 1) (State.serve k piv st (D.freeUses k)) := by
  obtain ⟨hn, hnew, hinj, hold, hlow, hpivv, hzero, hreads, hroot, hops⟩ :=
    State.serve_spec x k piv (D.freeUses k) st (D.freeUses_nodup k) hp.piv_lt hp.fresh
  have hnext : st.next ≤ (State.serve k piv st (D.freeUses k)).next := by rw [hn]; omega
  have huse : ∀ u ∈ D.freeUses k, D.useNode u = k := fun u hu =>
    D.useNode_of_mem_uses (D.mem_freeUses.mp hu).1
  refine ⟨?_, ?_, ?_, hzero, ?_, ?_⟩
  · intro u hu
    by_cases hf : u ∈ D.freeUses k
    · exact (hnew u hf).1
    · rw [hold u hf]; exact lt_of_lt_of_le (hp.slot_lt u hu hf) hnext
  · intro u hu
    by_cases hf : u ∈ D.freeUses k
    · rw [(hnew u hf).2.1, hp.piv_val, huse u hf]
    · rw [hold u hf, hlow _ (hp.slot_lt u hu hf) (hp.slot_ne u hu hf), hp.value u hu hf]
  · intro u u' hu hu' heq
    by_cases hf : u ∈ D.freeUses k <;> by_cases hf' : u' ∈ D.freeUses k
    · exact hinj u hf u' hf' heq
    · exfalso
      rw [hold u' hf'] at heq
      rcases (hnew u hf).2.2 with h | h
      · exact hp.slot_ne u' hu' hf' (heq.symm.trans h)
      · have := hp.slot_lt u' hu' hf'; omega
    · exfalso
      rw [hold u hf] at heq
      rcases (hnew u' hf').2.2 with h | h
      · exact hp.slot_ne u hu hf (heq.trans h)
      · have := hp.slot_lt u hu hf; omega
    · rw [hold u hf, hold u' hf'] at heq
      exact hp.inj u u' hu hf hu' hf' heq
  · intro r hr
    by_cases hf : Use.root r ∈ D.freeUses k
    · exact hroot r hf
    · rw [hold _ hf]; exact hreads _ (hp.reads r hr hf)
  · intro op hop
    rcases hops op hop with h | ⟨f, hf1, hf2, rfl⟩
    · exact ⟨(hp.ops_ok op h).1, Op.SlotsLt.mono hnext (hp.ops_ok op h).2⟩
    · exact ⟨fun h => by have := hp.piv_lt; omega, ⟨lt_of_lt_of_le hp.piv_lt hnext, hf2⟩⟩

theorem linkUse_none_of_lt (hv : D.Valid) {k : ℕ} (hk : k < D.v) : D.linkUse k = none := by
  unfold linkUse
  cases h : D.link k with
  | none => rfl
  | some l =>
    obtain ⟨o, t, pos⟩ := l
    exact absurd (hv.link_donor k o t pos h).1 (by omega)

/-- **One compiler step** preserves the invariant. -/
theorem inv_step (hv : D.Valid) (x : ℕ → ZMod 2) {k : ℕ} (hk : k < D.N) {st : State}
    (hi : D.Inv x k st) : D.Inv x (k + 1) (D.step st k) := by
  unfold step
  split_ifs with hleaf
  · -- a leaf: a fresh slot receives the input
    apply D.inv_of_pre
    set st1 : State := { st with next := st.next + 1, ops := st.ops ++ [.src st.next k] } with hst1
    have hc1 : st1.contents x = Function.update (st.contents x) st.next
        (st.contents x st.next + x k) := by
      simp only [State.contents, hst1, runOps_append, runOps_singleton, Op.run]
    have hold : ∀ u, D.Pending (k + 1) u → u ∉ D.freeUses k → D.Pending k u := fun u hu hf =>
      (D.pending_old hv hu hf (by rw [D.linkUse_none_of_lt hv hleaf]; simp)).1
    refine ⟨by simp [hst1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hc1, Function.update_self, hi.fresh _ le_rfl, zero_add, D.val_leaf x hleaf]
    · intro u hu hf
      have := hi.slot_lt u (hold u hu hf); simp [hst1]; omega
    · intro u hu hf
      exact Nat.ne_of_lt (hi.slot_lt u (hold u hu hf))
    · intro u hu hf
      rw [hc1, Function.update_of_ne (Nat.ne_of_lt (hi.slot_lt u (hold u hu hf))),
        hi.value u (hold u hu hf)]
    · intro u u' hu hf hu' hf' heq
      exact hi.inj u u' (hold u hu hf) (hold u' hu' hf') heq
    · intro s hs
      simp only [hst1] at hs
      rw [hc1, Function.update_of_ne (by omega)]
      exact hi.fresh s (by omega)
    · intro r hr hf
      exact hi.reads r (hold _ hr hf)
    · intro op hop
      simp only [hst1, List.mem_append, List.mem_singleton] at hop
      rcases hop with h | rfl
      · exact ⟨(hi.ops_ok op h).1, Op.SlotsLt.mono (Nat.le_succ st.next) (hi.ops_ok op h).2⟩
      · exact ⟨trivial, Nat.lt_succ_self st.next⟩
  · -- an addition
    have hvk : D.v ≤ k := Nat.le_of_not_lt hleaf
    have hpa := D.pending_arg hv hvk hk false
    have hpb := D.pending_arg hv hvk hk true
    have hab : st.pend (.gate k false) ≠ st.pend (.gate k true) := fun h =>
      absurd (hi.inj _ _ hpa hpb h) (by simp)
    have hva := hi.value _ hpa
    have hvb := hi.value _ hpb
    simp only [useNode] at hva hvb
    have hsum : D.val x k = D.val x (D.arg k false) + D.val x (D.arg k true) :=
      D.val_add x hvk (hv.arg_lt k hvk hk false) (hv.arg_lt k hvk hk true)
    -- an old pending use is not an argument of `k`, so its slot is neither argument slot
    have hne : ∀ u, D.Pending k u → (∀ pos, u ≠ .gate k pos) →
        st.pend u ≠ st.pend (.gate k false) ∧ st.pend u ≠ st.pend (.gate k true) := by
      intro u hu hn
      exact ⟨fun h => hn false (hi.inj _ _ hu hpa h), fun h => hn true (hi.inj _ _ hu hpb h)⟩
    cases hl : D.link k with
    | none =>
      apply D.inv_of_pre
      set sa := st.pend (.gate k false)
      set sb := st.pend (.gate k true)
      set st1 : State := { st with ops := st.ops ++ [.add sa sb k] } with hst1
      have hc1 : st1.contents x = Function.update (st.contents x) sa
          (st.contents x sa + st.contents x sb) := by
        simp only [State.contents, hst1, runOps_append, runOps_singleton, Op.run]
      have hnl : D.linkUse k = none := by simp [linkUse, hl]
      have hold : ∀ u, D.Pending (k + 1) u → u ∉ D.freeUses k →
          D.Pending k u ∧ ∀ pos, u ≠ .gate k pos := fun u hu hf =>
        D.pending_old hv hu hf (by rw [hnl]; simp)
      refine ⟨hi.slot_lt _ hpa, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hc1, Function.update_self, hva, hvb, hsum]
      · intro u hu hf
        exact hi.slot_lt u (hold u hu hf).1
      · intro u hu hf
        exact (hne u (hold u hu hf).1 (hold u hu hf).2).1
      · intro u hu hf
        rw [hc1, Function.update_of_ne (hne u (hold u hu hf).1 (hold u hu hf).2).1,
          hi.value u (hold u hu hf).1]
      · intro u u' hu hf hu' hf' heq
        exact hi.inj u u' (hold u hu hf).1 (hold u' hu' hf').1 heq
      · intro s hs
        have hs' : st.next ≤ s := hs
        rw [hc1, Function.update_of_ne (by have := hi.slot_lt _ hpa; omega)]
        exact hi.fresh s hs'
      · intro r hr hf
        exact hi.reads r (hold _ hr hf).1
      · intro op hop
        simp only [hst1, List.mem_append, List.mem_singleton] at hop
        rcases hop with h | rfl
        · exact hi.ops_ok op h
        · exact ⟨hab, hi.slot_lt _ hpa, hi.slot_lt _ hpb⟩
    | some l =>
      obtain ⟨o, t, pos⟩ := l
      have hlu : D.linkUse k = some (.gate t pos) := by simp [linkUse, hl]
      obtain ⟨hkt, htN, hsame⟩ := hv.link_user k o t pos hl
      apply D.inv_of_pre
      set sa := st.pend (.gate k false)
      set sb := st.pend (.gate k true)
      set piv := if o then sa else sb
      set oth := if o then sb else sa
      have hpo : piv ≠ oth := by
        simp only [piv, oth]; split_ifs
        · exact hab
        · exact Ne.symm hab
      have hoth : st.contents x oth = D.val x (D.arg k o) := by
        simp only [oth]; split_ifs with ho
        · rw [hvb, ho]
        · rw [hva, Bool.eq_false_iff.mpr ho]
      set st1 : State := { st with ops := st.ops ++ [.add piv oth k] } with hst1
      set st2 := st1.assign oth (.gate t pos) with hst2
      have hc2 : st2.contents x = Function.update (st.contents x) piv
          (st.contents x piv + st.contents x oth) := by
        simp only [State.contents, hst2, State.assign_ops, hst1, runOps_append, runOps_singleton,
          Op.run]
      have hlinked : Use.gate t pos ∉ D.freeUses k := by
        intro h
        have := (D.mem_freeUses.mp h).2
        rw [show D.linkedB (.gate t pos) = true from
          (D.linkedB_iff _).mpr ⟨k, hk, hlu⟩] at this
        cases this
      -- the pending uses other than the free uses of `k`
      have hold : ∀ u, D.Pending (k + 1) u → u ∉ D.freeUses k → u ≠ .gate t pos →
          D.Pending k u ∧ ∀ pos, u ≠ .gate k pos := fun u hu hf hne' =>
        D.pending_old hv hu hf (by rw [hlu]; exact fun h => hne' (Option.some.inj h).symm)
      have hpend2 : ∀ u, st2.pend u = if u = .gate t pos then oth else st.pend u := by
        intro u; simp only [hst2, State.assign_pend]
        by_cases h : u = .gate t pos
        · subst h; simp
        · simp [h, hst1]
      have hpivsa : piv = sa ∨ piv = sb := by simp only [piv]; split_ifs <;> simp
      have hothsa : oth = sa ∨ oth = sb := by simp only [oth]; split_ifs <;> simp
      have hpivval : st.contents x piv + st.contents x oth = D.val x k := by
        rw [hsum]; simp only [piv, oth]; split_ifs
        · rw [hva, hvb]
        · rw [hvb, hva, add_comm]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [hst2, State.assign_next, hst1]
        rcases hpivsa with h | h <;> rw [h]
        · exact hi.slot_lt _ hpa
        · exact hi.slot_lt _ hpb
      · rw [hc2, Function.update_self, hpivval]
      · intro u hu hf
        rw [hpend2]
        simp only [hst2, State.assign_next, hst1]
        split_ifs with h
        · rcases hothsa with h' | h' <;> rw [h']
          · exact hi.slot_lt _ hpa
          · exact hi.slot_lt _ hpb
        · exact hi.slot_lt u (hold u hu hf h).1
      · intro u hu hf
        rw [hpend2]
        split_ifs with h
        · exact Ne.symm hpo
        · have := hne u (hold u hu hf h).1 (hold u hu hf h).2
          rcases hpivsa with h' | h' <;> rw [h']
          · exact this.1
          · exact this.2
      · intro u hu hf
        rw [hpend2]
        split_ifs with h
        · rw [hc2, Function.update_of_ne (Ne.symm hpo), hoth, h]
          simp only [useNode]
          exact congrArg (D.val x) hsame.symm
        · have hn := hne u (hold u hu hf h).1 (hold u hu hf h).2
          have hp' : st.pend u ≠ piv := by rcases hpivsa with h' | h' <;> rw [h'] <;> simp [hn]
          rw [hc2, Function.update_of_ne hp', hi.value u (hold u hu hf h).1]
      · intro u u' hu hf hu' hf' heq
        rw [hpend2, hpend2] at heq
        by_cases h : u = .gate t pos <;> by_cases h' : u' = .gate t pos
        · rw [h, h']
        · exfalso
          rw [ite_eq_left h, ite_eq_right h'] at heq
          have hn := hne u' (hold u' hu' hf' h').1 (hold u' hu' hf' h').2
          rcases hothsa with h'' | h'' <;> rw [h''] at heq
          · exact hn.1 heq.symm
          · exact hn.2 heq.symm
        · exfalso
          rw [ite_eq_right h, ite_eq_left h'] at heq
          have hn := hne u (hold u hu hf h).1 (hold u hu hf h).2
          rcases hothsa with h'' | h'' <;> rw [h''] at heq
          · exact hn.1 heq
          · exact hn.2 heq
        · rw [ite_eq_right h, ite_eq_right h'] at heq
          exact hi.inj u u' (hold u hu hf h).1 (hold u' hu' hf' h').1 heq
      · intro s hs
        simp only [hst2, State.assign_next, hst1] at hs
        have hp' : s ≠ piv := by
          rcases hpivsa with h | h <;> rw [h]
          · exact Nat.ne_of_gt (lt_of_lt_of_le (hi.slot_lt _ hpa) hs)
          · exact Nat.ne_of_gt (lt_of_lt_of_le (hi.slot_lt _ hpb) hs)
        rw [hc2, Function.update_of_ne hp']
        exact hi.fresh s hs
      · intro r hr hf
        have hrt : Use.root r ≠ .gate t pos := by simp
        have := hi.reads r (hold _ hr hf hrt).1
        rw [hpend2, ite_eq_right hrt]
        exact State.reads_assign_sub st1 oth _ _ this
      · intro op hop
        simp only [hst2, State.assign_ops, hst1, List.mem_append, List.mem_singleton] at hop
        rcases hop with h | rfl
        · exact hi.ops_ok op h
        · refine ⟨hpo, ?_, ?_⟩
          · rcases hpivsa with h | h <;> rw [h]
            · exact hi.slot_lt _ hpa
            · exact hi.slot_lt _ hpb
          · rcases hothsa with h | h <;> rw [h]
            · exact hi.slot_lt _ hpa
            · exact hi.slot_lt _ hpb

/-- The invariant after compiling the nodes below `k`. -/
theorem inv_compileTo (hv : D.Valid) (x : ℕ → ZMod 2) :
    ∀ k, k ≤ D.N → D.Inv x k (D.compileTo k) := by
  intro k
  induction k with
  | zero => intro _; exact D.inv_start x
  | succ k ih =>
    intro hk
    have h := D.inv_step hv x (by omega) (ih (by omega))
    simpa only [compileTo, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      using h

/-- **Compiler correctness.** On clean input, every root's read slot holds the root's value. -/
theorem compile_correct (hv : D.Valid) (x : ℕ → ZMod 2) (r : ℕ) (hr : r < D.rootCount) :
    (D.compile.pend (.root r), r) ∈ D.compile.reads ∧
      D.compile.contents x (D.compile.pend (.root r)) = D.val x (D.rootNode r) := by
  have hi := D.inv_compileTo hv x D.N le_rfl
  have hp : D.Pending D.N (.root r) := by
    refine ⟨trivial, Or.inl ⟨D.rootNode r, hv.root_lt r hr, ?_⟩⟩
    exact D.mem_freeUses.mpr ⟨(D.mem_uses_root _ r).mpr ⟨hr, rfl⟩, D.root_not_linked r⟩
  exact ⟨hi.reads r hp, hi.value _ hp⟩

end Dag

end IntegerMultBounds.MathlibTM2.M8.Local
