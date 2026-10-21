module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.LeafRoutines
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphExists
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Guard

/-!
# The reversed family on the common bank

A frame (`Frame`) is a call on a view `v` of `n` atoms of `b` digits, with its node stack, scalar
stack, payload work tapes and call stacks, and the return address whose code tops the PC stack.
Its role streams are free, up to a shape `Good` that every block keeps.

The preparation (`Prepare.atoms`, `Prepare.divide`), the test (`Guard`), the leaves and the
finish are concrete blocks. A leaf computes its offsets, saves the headers on the node stack,
installs the headers of `sub (r-1) 1`, runs the leaf core, restores the headers and counts one
leaf fewer (`leaf_runs`). The leaf core is a hypothesis (`LeafCore`): on any one-atom view it
runs from good role streams to good role streams within `coreCost`. The node's blocks (split,
pieces, merge) are an interface (`NodeHalf`): shapes for the node's banks and runs between them.

`inv` assembles `GraphExists.Inv`, so `GraphExists.contract` gives the family's contract.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.Family

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)
open GraphContract (Runs Tests Pops)
open CommonBank (bank Target word K)
open Routines (hdr)
open Blocks (seqB seq_runs runs_mono Leading)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedBankStageInput (raw)

variable {T : ℕ}

abbrev count (T : ℕ) := CommonBank.count T

/-- The PC stack. -/
def pcSlot : Fin (count T) := Shared50RecursiveBank.returnSlot 1

theorem pcSlot_pos : 0 < count T := Nat.zero_lt_of_lt (pcSlot (T := T)).isLt

/-- The counters during the leaf loop, with `r` leaves remaining. -/
def leafC (b m n r : ℕ) : Fin K → Option ℕ :=
  Function.update (Function.update (Function.update (Prepare.rest b m) 9 (some n)) 5 (some (n / m))) 11
    (some r)

/-! ### The concrete blocks -/

def prepare : Graph.Block (count T) prime := seqB Prepare.atoms Prepare.divide

def test : Graph.Block (count T) prime :=
  SharedBankFamily.ofProgram (s := 0)
    (Guard.program (a := prime) (Fin.castAdd 0 (CommonBank.auxSlot (t := T) 11))
      (Fin.castAdd 0 (CommonBank.auxSlot (t := T) 5)))

def leaf (core : Graph.Block (count T) prime) : Graph.Block (count T) prime :=
  seqB LeafRoutines.offsets (seqB Blocks.push (seqB LeafRoutines.view (seqB core
    (seqB Blocks.restore LeafRoutines.advance))))

/-- The leaf core runs on any one-atom view from good role streams to good role streams. -/
def LeafCore (core : Graph.Block (count T) prime) (Good : Descriptor → Tapes T prime → Prop)
    (coreCost : ℕ → ℕ → ℕ) : Prop :=
  Leading core ∧ ∀ (v u : Descriptor) (b : ℕ), RecursiveDimensionBank.Headers u (hdr u) →
    u.width = b → volume prime u = volume prime v → ∀ (hs : Fin 6 → List Bool), hs = hdr u →
    ∀ roles f p node scalar c st, Good v roles → ∃ roles', Good v roles' ∧
      Runs core (bank roles hs f p node scalar c st) (bank roles' hs f p node scalar c st) (coreCost (volume prime v) b)

/-! ### The runs of the concrete blocks -/

variable {roles : Tapes T prime} {f : ℤ → Fin (prime+4)} {p : ℤ} {node scalar : Tapes 1 prime}
  {st : Tapes 2 prime}

theorem hdr_width (v : Descriptor) : Counter.value (hdr v 3) = v.width :=
  FlatCoordinateSchedule.bits_value _

/-- The preparation's cost. -/
def prepCost (b m n : ℕ) : ℕ :=
  (BinaryDescriptorDivMod.linearConstant (bits b) * (n * b + 1) + 2 * b + 6) +
    BinaryDescriptorDivMod.linearConstant (bits m) * (n + 1) + 1

/-- **The preparation**: `n` atoms, `⌊n/m⌋` per coordinate, `n mod m` leaves remaining. -/
theorem prepare_runs {v : Descriptor} {b m n : ℕ} (hb : 0 < b) (hm : 0 < m) (hw : v.width = n * b) :
    Runs prepare (bank roles (hdr v) f p node scalar (Prepare.rest b m) st)
      (bank roles (hdr v) f p node scalar (leafC b m n (n % m)) st) (prepCost b m n) := by
  obtain ⟨B₁, hB₁, h₁⟩ := Prepare.atoms_runs (roles := roles) (f := f) (p := p) (node := node)
    (scalar := scalar) (st := st) (c := Prepare.rest b m) (hs := hdr v) hb (hdr_width v)
    (FlatCoordinateSchedule.bits_canonical _) rfl rfl
  rw [hw, Nat.mul_div_cancel _ hb] at h₁
  obtain ⟨B₂, hB₂, h₂⟩ := Prepare.divide_runs (roles := roles) (f := f) (p := p) (node := node)
    (scalar := scalar) (st := st) (hs := hdr v) (c := Function.update (Prepare.rest b m) 9 (some n)) (n := n) (m := m)
    hm (by simp) (by simp [Prepare.rest]) (by simp [Prepare.rest]) (by simp [Prepare.rest])
  rw [hw] at hB₁
  exact runs_mono (seq_runs (fun _ => rfl) (fun _ => rfl) h₁ h₂)
    (by unfold prepCost; omega)

/-- The test on a bank of the leaf loop. -/
theorem test_runs {b m n r : ℕ} (hm : 0 < m) (hs : Fin 6 → List Bool) :
    ∃ st' : Fin (test (T := T)).states,
      Guard.exit st' = (if r ≠ 0 then .leaf else if m ≤ n then .node else .done) ∧
      run (test (T := T)).program 1 ((raw (bank roles hs f p node scalar (leafC b m n r) st)
        (test (T := T)).tapes).start (test (T := T)).program) =
        some (SharedBankFamilyExact.atState (raw (bank roles hs f p node scalar (leafC b m n r) st)
          (test (T := T)).tapes) st') ∧
      step (test (T := T)).program (SharedBankFamilyExact.atState (raw (bank roles hs f p node scalar
        (leafC b m n r) st) (test (T := T)).tapes) st') = none := by
  set x := raw (bank roles hs f p node scalar (leafC b m n r) st) (count T + 0)
  obtain ⟨hr, hh⟩ := Guard.run_exact (Fin.castAdd 0 (CommonBank.auxSlot (t := T) 11))
    (Fin.castAdd 0 (CommonBank.auxSlot (t := T) 5)) x
  refine ⟨_, ?_, hr, hh⟩
  have r11 := CommonBank.bank_aux roles hs f p node scalar (leafC b m n r) st 11
  have r5 := CommonBank.bank_aux roles hs f p node scalar (leafC b m n r) st 5
  have l11 := Embed.raw_left (p := 0) (bank roles hs f p node scalar (leafC b m n r) st) (CommonBank.auxSlot 11)
  have l5 := Embed.raw_left (p := 0) (bank roles hs f p node scalar (leafC b m n r) st) (CommonBank.auxSlot 5)
  have c11 : leafC b m n r 11 = some r := by simp [leafC]
  have c5 : leafC b m n r 5 = some (n / m) := by simp [leafC]
  rw [c11] at r11; rw [c5] at r5
  have b11 := Blocks.counter_blank r
  have b5 := Blocks.counter_blank (n / m)
  have hdiv : n / m ≠ 0 ↔ m ≤ n := by
    rw [ne_eq, Nat.div_eq_zero_iff]; omega
  unfold Guard.result
  simp only [x, l11.1, l11.2, l5.1, l5.2, r11.1, r11.2, r5.1, r5.2, word, Option.map_some]
  by_cases h1 : r ≠ 0
  · rw [ite_eq_left (b11.mpr h1), ite_eq_left h1]; rfl
  · rw [ite_eq_right (fun h => h1 (b11.mp h)), ite_eq_right h1]
    by_cases h2 : m ≤ n
    · rw [ite_eq_left (b5.mpr (hdiv.mpr h2)), ite_eq_left h2]; rfl
    · rw [ite_eq_right (fun h => h2 (hdiv.mp (b5.mp h))), ite_eq_right h2]; rfl

theorem sub_positive {v : Descriptor} {b n s c : ℕ} (hpos : v.Positive) :
    (RevMachine.sub prime b n s c v).Positive := by
  have hq0 : 0 < prime := Networks.Shared50ModularControl.prime_prime.pos
  obtain ⟨hA, hR, hB, hC, hE⟩ := hpos
  exact ⟨hA, hR, Nat.mul_pos hB (pow_pos hq0 _),
    Nat.mul_pos (Nat.mul_pos (pow_pos hq0 _) hC) (pow_pos hq0 _), Nat.mul_pos (pow_pos hq0 _) hE⟩

/-- A node stack with free cells from its head on. -/
def NodeFree (node : Tapes 1 prime) : Prop := ∀ z, node.head 0 ≤ z → node.tape 0 z = blank

theorem nodeFree_free {node : Tapes 1 prime} (h : NodeFree node) (hs : Fin 6 → List Bool) :
    RecursiveViewFrame.Free hs node := fun z hz _ => h z hz

/-- The header length bound of a view. -/
def hlen (v : Descriptor) : ℕ := Nat.log2 (volume prime v) + 1

/-- A leaf's cost. -/
def leafCost (coreCost : ℕ → ℕ → ℕ) (v : Descriptor) (b n : ℕ) : ℕ :=
  (30 * n + 130) + (12 * hlen v + 48) + 1500 * volume prime v + coreCost (volume prime v) b +
    (24 * hlen v + 79) + (20 * n + 40) + 5

/-- **A leaf**: from `r ≥ 1` remaining leaves to `r - 1`, with the role streams run by the core. -/
theorem leaf_runs {core : Graph.Block (count T) prime} {Good : Descriptor → Tapes T prime → Prop}
    {coreCost : ℕ → ℕ → ℕ} (hcore : LeafCore core Good coreCost) {v : Descriptor} {b m n r : ℕ}
    (hpos : v.Positive) (hb : 0 < b) (hw : v.width = n * b) (hr : 1 ≤ r) (hrn : r ≤ n)
    (hfree : NodeFree node) (hg : Good v roles) :
    ∃ roles', Good v roles' ∧ Runs (leaf core) (bank roles (hdr v) f p node scalar (leafC b m n r) st)
      (bank roles' (hdr v) f p node scalar (leafC b m n (r - 1)) st) (leafCost coreCost v b n) := by
  set c₁ := Function.update (Function.update (Function.update (leafC b m n r) 12 (some (r - 1)))
    13 (some 1)) 14 (some (n - (r - 1) - 1))
  obtain ⟨B₁, hB₁, h₁⟩ := LeafRoutines.offsets_runs (roles := roles) (hs := hdr v) (f := f) (p := p)
    (node := node) (scalar := scalar) (st := st) (c := leafC b m n r) hr hrn
    (by simp [leafC]) (by simp [leafC]) (by simp [leafC, Prepare.rest]) (by simp [leafC, Prepare.rest])
    (by simp [leafC, Prepare.rest]) (by simp [leafC, Prepare.rest])
  have h₂ := Blocks.push_runs roles (hdr v) f p node scalar c₁ st
  have h₃ := LeafRoutines.view_runs (roles := roles) (f := f) (p := p)
    (node := RecursiveViewFrame.savedStack (hdr v) node) (scalar := scalar) (st := st) (c := c₁)
    (Routines.hdr_headers v) hpos hb hw (s := r - 1) (cc := 1) (by omega) rfl
    (by simp [c₁, leafC, Prepare.rest]) (by simp [c₁]) (by simp [c₁]) (by simp [c₁])
  set u := RevMachine.sub prime b n (r - 1) 1 v
  have hu : Headers.childHeaders (q := prime) v (hdr v) b (r - 1) 1 (n - (r - 1) - 1) = hdr u :=
    Routines.hdr_eq (Headers.child_headers (Routines.hdr_headers v) rfl)
  have hvol : volume prime u = volume prime v := RevMachine.sub_volume prime b n (r - 1) 1 v hw (by omega)
  obtain ⟨roles', hg', h₄⟩ := hcore.2 v u b (hu ▸ Headers.child_headers (Routines.hdr_headers v) rfl)
    (by simp [u, RevMachine.sub]) hvol _ hu roles f p (RecursiveViewFrame.savedStack (hdr v) node) scalar c₁ st hg
  have h₅ := Blocks.restore_runs roles' (Headers.childHeaders (q := prime) v (hdr v) b (r - 1) 1 (n - (r - 1) - 1))
    f p node scalar c₁ st (hdr v) (nodeFree_free hfree _)
  obtain ⟨B₆, hB₆, h₆⟩ := LeafRoutines.advance_runs (roles := roles') (hs := hdr v) (f := f) (p := p)
    (node := node) (scalar := scalar) (st := st) (c := c₁) (n := n) (r := r) (s := r - 1) (cc := 1)
    (e := n - (r - 1) - 1) hrn (by omega) (by omega) (by omega)
    (by simp [c₁, leafC]) (by simp [c₁]) (by simp [c₁]) (by simp [c₁])
  have hc : Function.update (Function.update (Function.update (Function.update c₁ 11 (some (r - 1))) 12 none)
      13 none) 14 none = leafC b m n (r - 1) := by
    funext j; fin_cases j <;> rfl
  rw [hc] at h₆
  refine ⟨roles', hg', ?_⟩
  have hp := RecursiveViewFrame.pushCost_le (hdr v) (hlen v)
    (fun z => RecursiveAffinePrepare.header_log Networks.Shared50ModularControl.prime_prime.two_le v hpos _
      (Routines.hdr_headers v) z)
  have hq := RecursiveViewFrame.restoreCost_le (hdr v)
    (Headers.childHeaders (q := prime) v (hdr v) b (r - 1) 1 (n - (r - 1) - 1)) (hlen v)
    (fun z => RecursiveAffinePrepare.header_log Networks.Shared50ModularControl.prime_prime.two_le v hpos _
      (Routines.hdr_headers v) z)
    (fun z => by
      rw [hu]
      have := RecursiveAffinePrepare.header_log Networks.Shared50ModularControl.prime_prime.two_le u
        (sub_positive hpos) _ (Routines.hdr_headers u) z
      rwa [hvol] at this)
  have L5 := seq_runs (fun _ => rfl) (fun _ => rfl) h₅ h₆
  have L4 := seq_runs hcore.1 (fun _ => rfl) h₄ L5
  have L3 := seq_runs (fun _ => rfl) (fun _ => rfl) h₃ L4
  have L2 := seq_runs (fun _ => rfl) (fun _ => rfl) h₂ L3
  have L1 := seq_runs (fun _ => rfl) (fun _ => rfl) h₁ L2
  exact runs_mono L1 (by unfold leafCost; omega)

/-! ### The PC stack -/

/-- The PC stack after popping a code that sat on `g` at `q`. -/
def popped (st : Tapes 2 prime) (g : ℤ → Fin (prime+4)) (q : ℤ) : Tapes 2 prime :=
  SharedPlacementAlphabet.setTape st 1 g q

theorem bank_pc (hs : Fin 6 → List Bool) (c : Fin K → Option ℕ) :
    (bank roles hs f p node scalar c st).head pcSlot = st.head 1 ∧
      (bank roles hs f p node scalar c st).tape pcSlot = st.tape 1 := by
  simp [bank, Shared50RecursiveBank.bank, RecursiveCallBank.bank, RecursiveShiftRoleBank.common,
    pcSlot, Shared50RecursiveBank.returnSlot, Tapes.append]

theorem bank_pop (hs : Fin 6 → List Bool) (c : Fin K → Option ℕ) (g : ℤ → Fin (prime+4)) (q : ℤ) :
    SharedPlacementAlphabet.setTape (bank roles hs f p node scalar c st) pcSlot g q =
      bank roles hs f p node scalar c (popped st g q) := by
  simp only [bank, Shared50RecursiveBank.bank, RecursiveCallBank.bank, RecursiveShiftRoleBank.common, pcSlot,
    Shared50RecursiveBank.returnSlot, SharedPlacementAlphabet.setTape_append_right, popped]

/-- The PC stack holds `code` on `g` at `q`, with free cells above. -/
def Coded {k : ℕ} (st : Tapes 2 prime) (code : FiniteReturnStack.Code k) (g : ℤ → Fin (prime+4)) (q : ℤ) : Prop :=
  st.tape 1 = FiniteReturnStack.wordPart g q code k le_rfl ∧ st.head 1 = q + k ∧ ∀ j < k, g (q + j) = blank

/-! ### Frames -/

section Frames

variable {Seg Call : Type} (pieces : List (Graph.Piece Seg Call)) {k : ℕ}
  (capacity : Fintype.card (Graph.PC pieces.length) ≤ 2^k)

/-- **A frame**: a call on a view of `n` atoms of `b` digits. -/
structure Frame where
  v : Descriptor
  n : ℕ
  b : ℕ
  hpos : v.Positive
  hb : 0 < b
  hw : v.width = n * b
  f : ℤ → Fin (prime+4)
  p : ℤ
  node : Tapes 1 prime
  scalar : Tapes 1 prime
  st : Tapes 2 prime
  hfree : NodeFree node
  ret : Graph.PC pieces.length
  g : ℤ → Fin (prime+4)
  q : ℤ
  hcode : Coded st (FiniteReturnStack.address capacity (Graph.encoding pieces ret)) g q

variable {pieces capacity}

/-- A bank of the frame. -/
def Frame.at (σ : Frame pieces capacity) (roles : Tapes T prime) (c : Fin K → Option ℕ) :
    Tapes (count T) prime :=
  bank roles (hdr σ.v) σ.f σ.p σ.node σ.scalar c σ.st

/-- The frame's bank at its return. -/
def Frame.exitAt (σ : Frame pieces capacity) (roles : Tapes T prime) (m : ℕ) : Tapes (count T) prime :=
  bank roles (hdr σ.v) σ.f σ.p σ.node σ.scalar (Prepare.rest σ.b m) (popped σ.st σ.g σ.q)

end Frames

/-! ### The implementation and the invariants -/

section Assembly

variable {Seg Call : Type} (pieces : List (Graph.Piece Seg Call)) {k : ℕ}
  (capacity : Fintype.card (Graph.PC pieces.length) ≤ 2^k)

/-- The node's blocks. -/
structure NodeBlocks (T k : ℕ) (Seg Call : Type) where
  split : Graph.Block (count T) prime
  merge : Graph.Block (count T) prime
  segment : Seg → Graph.Block (count T) prime
  enter : Call → FiniteReturnStack.Code k → Graph.Block (count T) prime
  recover : Call → Graph.Block (count T) prime

/-- **The implementation**: concrete preparation, test, leaves and finish; the node's blocks. -/
def impl (core : Graph.Block (count T) prime) (N : NodeBlocks T k Seg Call) :
    Graph.Implementation (count T) prime k Seg Call where
  prepare := prepare
  test := test
  exit := Guard.exit
  leaf := leaf core
  split := N.split
  merge := N.merge
  finish := Prepare.finish
  segment := N.segment
  enter := N.enter
  recover := N.recover

variable {pieces capacity}

/-- **The node half**: shapes of the node's banks and the node's block runs between them. -/
structure NodeHalf (N : NodeBlocks T k Seg Call) (m W : ℕ) (rank : Call → ℕ)
    (Good : Descriptor → Tapes T prime → Prop) where
  /-- The frames the family serves. -/
  Ok : Frame pieces capacity → Prop
  Node : Frame pieces capacity → ℕ → Tapes (count T) prime → Prop
  cSplit : Frame pieces capacity → ℕ
  cMerge : Frame pieces capacity → ℕ
  cSeg : Frame pieces capacity → Seg → ℕ
  cCall : Frame pieces capacity → Call → ℕ
  split : ∀ σ roles, Ok σ → m ≤ σ.n → Good σ.v roles →
    ∃ y, Node σ 0 y ∧ Runs N.split (σ.at roles (leafC σ.b m σ.n 0)) y (cSplit σ)
  seg : ∀ σ y, Ok σ → m ≤ σ.n → ∀ (i : Graph.Site pieces) (s : Seg), pieces[i] = .seg s → Node σ i.val y →
    ∃ y', Node σ (i.val+1) y' ∧ Runs (N.segment s) y y' (cSeg σ s)
  call : ∀ σ y, Ok σ → m ≤ σ.n → ∀ (i : Graph.Site pieces) (c : Call), pieces[i] = .call c → Node σ i.val y →
    ∃ τ : Frame pieces capacity, Ok τ ∧ τ.n = rank c * (σ.n / m) ∧
      (volume prime τ.v : ℝ) = volume prime σ.v / W ∧ τ.ret = .recover i ∧ τ.b = σ.b ∧
      ∃ roles, Good τ.v roles ∧ ∃ E R, E + R ≤ cCall σ c ∧
        Runs (N.enter c (Graph.returnCode pieces capacity i)) y (τ.at roles (Prepare.rest τ.b m)) E ∧
        ∀ roles', Good τ.v roles' → ∃ y', Node σ (i.val+1) y' ∧ Runs (N.recover c) (τ.exitAt roles' m) y' R
  merge : ∀ σ y, Ok σ → m ≤ σ.n → Node σ pieces.length y →
    ∃ roles, Good σ.v roles ∧ Runs N.merge y (σ.at roles (leafC σ.b m σ.n 0)) (cMerge σ)

end Assembly

section Inv

variable {Seg Call : Type} {pieces : List (Graph.Piece Seg Call)} {k : ℕ}
  {capacity : Fintype.card (Graph.PC pieces.length) ≤ 2^k}

/-- The finish's cost. -/
def finishCost (m n : ℕ) : ℕ :=
  (2*(bits (n / m)).length+4) + (2*(bits n).length+4) + 1 + (2*(bits 0).length+4) + 1

theorem finish_counters (b m n : ℕ) :
    Function.update (Function.update (Function.update (leafC b m n 0) 5 none) 9 none) 11 none = Prepare.rest b m := by
  funext j; fin_cases j <;> rfl

/-- **The invariants of the family.** -/
def inv {core : Graph.Block (count T) prime} {Good : Descriptor → Tapes T prime → Prop}
    {coreCost : ℕ → ℕ → ℕ} (hcore : LeafCore core Good coreCost) {N : NodeBlocks T k Seg Call}
    {m W : ℕ} (hm : 0 < m) {rank : Call → ℕ} (H : NodeHalf (pieces := pieces) (capacity := capacity) N m W rank Good) :
    GraphExists.Inv pieces capacity pcSlot (impl core N) m W rank where
  Shape := Frame pieces capacity
  size σ := σ.n
  vol σ := volume prime σ.v
  ret σ := σ.ret
  leaves σ := σ.n % m
  Entry σ x₀ := H.Ok σ ∧ ∃ roles, Good σ.v roles ∧ x₀ = σ.at roles (Prepare.rest σ.b m)
  Leaf σ _ i y := ∃ roles, Good σ.v roles ∧ y = σ.at roles (leafC σ.b m σ.n (σ.n % m - i))
  Node σ _ i y := H.Node σ i y
  Done σ _ y := ∃ roles, Good σ.v roles ∧ y = σ.at roles (leafC σ.b m σ.n 0)
  Finished σ _ y := ∃ roles, Good σ.v roles ∧ y = σ.at roles (Prepare.rest σ.b m)
  Exit σ _ z := ∃ roles, Good σ.v roles ∧ z = σ.exitAt roles m
  cPrepare σ := prepCost σ.b m σ.n
  cTest _ := 1
  cLeaf σ := leafCost coreCost σ.v σ.b σ.n
  cSplit := H.cSplit
  cMerge := H.cMerge
  cFinish σ := finishCost m σ.n
  cSeg := H.cSeg
  cCall := H.cCall
  prepare σ x₀ := by
    rintro ⟨-, roles, hg, rfl⟩
    exact ⟨_, ⟨roles, hg, by rw [Nat.sub_zero]; rfl⟩, prepare_runs σ.hb hm σ.hw⟩
  test_leaf σ x₀ i y _ hi := by
    rintro ⟨roles, hg, rfl⟩
    obtain ⟨st', he, hr, hh⟩ := test_runs (roles := roles) (f := σ.f) (p := σ.p) (node := σ.node)
      (scalar := σ.scalar) (st := σ.st) (b := σ.b) (m := m) (n := σ.n) (r := σ.n % m - i) hm (hdr σ.v)
    refine ⟨1, le_rfl, st', he.trans ?_, hr, hh⟩
    rw [ite_eq_left (by omega)]
  test_end σ x₀ y _ := by
    rintro ⟨roles, hg, rfl⟩
    obtain ⟨st', he, hr, hh⟩ := test_runs (roles := roles) (f := σ.f) (p := σ.p) (node := σ.node)
      (scalar := σ.scalar) (st := σ.st) (b := σ.b) (m := m) (n := σ.n) (r := σ.n % m - σ.n % m) hm (hdr σ.v)
    refine ⟨1, le_rfl, st', he.trans ?_, hr, hh⟩
    rw [ite_eq_right (by omega)]
  leaf σ x₀ i y _ hi := by
    rintro ⟨roles, hg, rfl⟩
    obtain ⟨roles', hg', h⟩ := leaf_runs (f := σ.f) (p := σ.p) (scalar := σ.scalar) (st := σ.st) (m := m)
      hcore σ.hpos σ.hb σ.hw (r := σ.n % m - i) (by omega)
      (le_trans (Nat.sub_le _ _) (Nat.mod_le _ _)) σ.hfree hg
    rw [show σ.n % m - i - 1 = σ.n % m - (i + 1) by omega] at h
    exact ⟨_, ⟨roles', hg', rfl⟩, h⟩
  split σ x₀ y hx hm' := by
    rintro ⟨roles, hg, rfl⟩
    rw [Nat.sub_self]
    exact H.split σ roles hx.1 hm' hg
  seg σ x₀ y hx hm' i s hi hy := H.seg σ y hx.1 hm' i s hi hy
  call σ x₀ y hx hm' i c hi hy := by
    obtain ⟨τ, hok, hn, hv, hr, -, roles, hg, E, R, hER, he, hrec⟩ := H.call σ y hx.1 hm' i c hi hy
    exact ⟨τ, _, hn, hv, hr, ⟨hok, roles, hg, rfl⟩, E, R, hER, he, fun z ⟨roles', hg', hz⟩ => hz ▸ hrec roles' hg'⟩
  merge σ x₀ y hx hm' hy := by
    obtain ⟨roles, hg, h⟩ := H.merge σ y hx.1 hm' hy
    exact ⟨_, ⟨roles, hg, rfl⟩, h⟩
  done_leaf σ x₀ y _ _ := by
    rintro ⟨roles, hg, rfl⟩
    exact ⟨roles, hg, by rw [Nat.sub_self]⟩
  finish σ x₀ y _ := by
    rintro ⟨roles, hg, rfl⟩
    have h := Prepare.finish_runs (roles := roles) (hs := hdr σ.v) (f := σ.f) (p := σ.p) (node := σ.node)
      (scalar := σ.scalar) (st := σ.st) (c := leafC σ.b m σ.n 0) (f' := σ.n / m) (n := σ.n) (r := 0)
      (by simp [leafC]) (by simp [leafC]) (by simp [leafC])
    rw [finish_counters] at h
    exact ⟨_, ⟨roles, hg, rfl⟩, h⟩
  pop σ x₀ y _ := by
    rintro ⟨roles, hg, rfl⟩
    obtain ⟨hc, hh, hf⟩ := σ.hcode
    refine ⟨_, ⟨roles, hg, rfl⟩, σ.g, σ.q, ?_, ?_, hf, ?_⟩
    · simp only [Frame.at]; rw [(bank_pc _ _).2]; exact hc
    · simp only [Frame.at]; rw [(bank_pc _ _).1]; exact hh
    · simp only [Frame.at, Frame.exitAt]; exact bank_pop _ _ _ _

end Inv

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.Family
