module

public import IntegerMultBounds.Machine.FiniteFlow
public import IntegerMultBounds.Machine.FiniteReturnStackAt
public import IntegerMultBounds.Machine.FiniteReturnDispatch
public import IntegerMultBounds.Machine.SharedBankFamily
public import Mathlib.Tactic.DeriveFintype

/-!
# The control graph of the reversed family

One fixed cyclic graph runs every call of the reversed family, as `M8.Machine.Control` does for
stage 1. A call of `n` atoms enters at `prepare`, which computes `f = ⌊n/m⌋` and `δ = n mod m`.
The `test` block then loops: while leaf pairs remain it runs one `leaf` (the `δ` remainder pairs,
or all `n` pairs when `n < m`); then, if `f > 0`, it runs the node (`split`, the node's schedule of
pieces, `merge`); and it ends at `finish` and the return `pop`. A schedule piece is a nonrecursive
block (an atom segment, a gate, a reset) or a block call: its `enter` block pushes the call site's
return code and the graph jumps back to `prepare`; the decoded return reaches the site's `recover`
block. The ranks of the block calls are constants of the pieces; the atom count, `f`, `δ` and the
recursion depth are never program parameters. The blocks are explicit parameters
(`Implementation`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.Graph

noncomputable section
open IntegerMultBounds.Machine

/-- A piece of the node's schedule: a nonrecursive block or a block call. -/
inductive Piece (Seg Call : Type) where
  | seg (s : Seg)
  | call (c : Call)

/-- The exits of the test: one more leaf, the node, or the end of the call. -/
inductive Exit where
  | leaf
  | node
  | done

/-- The blocks of the graph, for a schedule of `n` pieces. -/
inductive PC (n : ℕ) where
  | prepare | test | leaf | split | merge | finish | pop | halt
  | piece (i : Fin n)
  | recover (i : Fin n)
  deriving DecidableEq, Fintype

abbrev Block (t a : ℕ) := SharedBankSkeleton.Skeleton t a

/-- The physical blocks, on one common bank of `t` tapes. -/
structure Implementation (t a k : ℕ) (Seg Call : Type) where
  prepare : Block t a
  test : Block t a
  exit : Fin test.states → Exit
  leaf : Block t a
  split : Block t a
  merge : Block t a
  finish : Block t a
  segment : Seg → Block t a
  enter : Call → FiniteReturnStack.Code k → Block t a
  recover : Call → Block t a

variable {Seg Call : Type} {t a k : ℕ} (pieces : List (Piece Seg Call))

/-- The schedule's call sites. -/
abbrev Site := Fin pieces.length

def encoding := Fintype.equivFin (PC pieces.length)

/-- A fixed adequate width of return codes exists. -/
theorem capacity_exists : ∃ k : ℕ, Fintype.card (PC pieces.length) ≤ 2^k :=
  ⟨_, (Nat.lt_two_pow_self).le⟩

/-- The first block of the node's schedule. -/
def first : PC pieces.length := if h : 0 < pieces.length then .piece ⟨0, h⟩ else .merge

/-- The block after piece `i`. -/
def successor (i : Site pieces) : PC pieces.length :=
  if h : i.val + 1 < pieces.length then .piece ⟨i.val + 1, h⟩ else .merge

/-- The return code of call site `i`. -/
def returnCode (capacity : Fintype.card (PC pieces.length) ≤ 2^k) (i : Site pieces) :
    FiniteReturnStack.Code k :=
  FiniteReturnStack.address capacity (encoding pieces (.recover i))

/-- The return code of the root: the halt block. -/
def rootCode (capacity : Fintype.card (PC pieces.length) ≤ 2^k) : FiniteReturnStack.Code k :=
  FiniteReturnStack.address capacity (encoding pieces .halt)

variable (capacity : Fintype.card (PC pieces.length) ≤ 2^k) (stack : Fin t) (ht : 0 < t)
  (impl : Implementation t a k Seg Call)

/-- The block at each control point. -/
def block : PC pieces.length → Block t a
  | .prepare => impl.prepare
  | .test => impl.test
  | .leaf => impl.leaf
  | .split => impl.split
  | .merge => impl.merge
  | .finish => impl.finish
  | .pop => SharedBankFamily.ofProgram (s := 0)
      (Placement.placed (FiniteReturnStack.pop a k) (FiniteReturnStackAt.placement stack))
  | .halt => SharedBankFamily.ofProgram (s := 0) (skip t a ht)
  | .piece i => match pieces[i] with
    | .seg s => impl.segment s
    | .call c => impl.enter c (returnCode pieces capacity i)
  | .recover i => match pieces[i] with
    | .call c => impl.recover c
    | .seg _ => SharedBankFamily.ofProgram (s := 0) (skip t a ht)

/-- The exit of the test. -/
def exitPC : Exit → PC pieces.length
  | .leaf => .leaf
  | .node => .split
  | .done => .finish

/-- The edges, selected by the terminal state of each block. -/
def edge : (pc : PC pieces.length) → Fin (block pieces capacity stack ht impl pc).states →
    Option (PC pieces.length)
  | .prepare, _ => some .test
  | .test, st => some (exitPC pieces (impl.exit st))
  | .leaf, _ => some .test
  | .split, _ => some (first pieces)
  | .merge, _ => some .finish
  | .finish, _ => some .pop
  | .pop, st => (FiniteReturnDispatch.select capacity st).map (encoding pieces).symm
  | .halt, _ => none
  | .piece i, _ => match pieces[i] with
    | .seg _ => some (successor pieces i)
    | .call _ => some .prepare
  | .recover i, _ => some (successor pieces i)

def states (pc : Fin (Fintype.card (PC pieces.length))) :=
  (block pieces capacity stack ht impl ((encoding pieces).symm pc)).states

def tapeCount := SharedBankFamily.tapeCount (block pieces capacity stack ht impl)

def family (pc : Fin (Fintype.card (PC pieces.length))) :
    Program (tapeCount pieces capacity stack ht impl) (states pieces capacity stack ht impl pc) a :=
  SharedBankFamily.program (block pieces capacity stack ht impl) ((encoding pieces).symm pc)

def next : FiniteFlow.Next (states pieces capacity stack ht impl) :=
  fun pc st => (edge pieces capacity stack ht impl ((encoding pieces).symm pc) st).map (encoding pieces)

/-- **The program of the family**: one fixed machine for every call. -/
def program :=
  FiniteFlow.program (family pieces capacity stack ht impl) (next pieces capacity stack ht impl)
    (encoding pieces .prepare)

/-- The configuration entering block `pc` on the common bank `x`. -/
def entryConfig (pc : PC pieces.length) (x : Tapes t a) :=
  ((SharedBankStageInput.raw x (tapeCount pieces capacity stack ht impl)).start
    (family pieces capacity stack ht impl (encoding pieces pc))).mapState
      (FiniteFlow.embed (states pieces capacity stack ht impl) (encoding pieces pc))

/-- The decoder routes the code of every block to that block. -/
theorem pop_edge (pc : PC pieces.length) :
    edge pieces capacity stack ht impl .pop
      (FiniteReturnStack.encode k (.inr (0, FiniteReturnStack.address capacity (encoding pieces pc)))) =
      some pc := by
  change (FiniteReturnDispatch.select capacity (FiniteReturnStack.encode k
    (.inr (0, FiniteReturnStack.address capacity (encoding pieces pc))))).map
      (encoding pieces).symm = _
  rw [FiniteReturnDispatch.select_return]
  simp only [Option.map_some, Equiv.symm_apply_apply]

/-- The decoder routes each call site's code to its recovery block. -/
theorem returns_to_site (i : Site pieces) :
    edge pieces capacity stack ht impl .pop
      (FiniteReturnStack.encode k (.inr (0, returnCode pieces capacity i))) = some (.recover i) := by
  change (FiniteReturnDispatch.select capacity (FiniteReturnStack.encode k
    (.inr (0, FiniteReturnStack.address capacity (encoding pieces (.recover i)))))).map
      (encoding pieces).symm = _
  rw [FiniteReturnDispatch.select_return]
  simp only [Option.map_some, Equiv.symm_apply_apply]

/-- The root's code reaches the halt block. -/
theorem returns_to_halt :
    edge pieces capacity stack ht impl .pop
      (FiniteReturnStack.encode k (.inr (0, rootCode pieces capacity))) = some .halt := by
  change (FiniteReturnDispatch.select capacity (FiniteReturnStack.encode k
    (.inr (0, FiniteReturnStack.address capacity (encoding pieces .halt))))).map
      (encoding pieces).symm = _
  rw [FiniteReturnDispatch.select_return]
  simp only [Option.map_some, Equiv.symm_apply_apply]

/-- A block call jumps back to the entry. -/
theorem call_edge (i : Site pieces) (c : Call) (hi : pieces[i] = .call c)
    (st : Fin (block pieces capacity stack ht impl (.piece i)).states) :
    edge pieces capacity stack ht impl (.piece i) st = some .prepare := by
  simp only [edge, hi]

/-- A nonrecursive piece continues with the next piece. -/
theorem seg_edge (i : Site pieces) (s : Seg) (hi : pieces[i] = .seg s)
    (st : Fin (block pieces capacity stack ht impl (.piece i)).states) :
    edge pieces capacity stack ht impl (.piece i) st = some (successor pieces i) := by
  simp only [edge, hi]

theorem recover_edge (i : Site pieces)
    (st : Fin (block pieces capacity stack ht impl (.recover i)).states) :
    edge pieces capacity stack ht impl (.recover i) st = some (successor pieces i) := rfl

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.Graph
