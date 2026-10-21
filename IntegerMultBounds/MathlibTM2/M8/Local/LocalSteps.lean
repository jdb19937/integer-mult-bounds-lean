module

public import IntegerMultBounds.MathlibTM2.M8.Frames.PairMask

/-!
# The local steps of the side slots, node by node, computably

The moves along the side slots of the PR97 word are sums over the nodes and roots of `φ` at
rank differences of node frames (`Global.LocalMoments`). Here those sums are formal: lists of
moves over a table `dims` of the node frames' ranks, a move of rank `r` counted positively as
`r` and negatively as `24 + r`, per addition node (`nodeFS`) and per root (`rootFS`).
`rankOk` checks one table entry against the node's pair mask; `Tree.hist` counts the moves of a
subtree by code. The kernel checks of `Checks/Rank*` and `Checks/Steps*` evaluate these on the
records; nothing here is trusted.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Local

/-- The first point of a support. -/
def pointOf : Supp → Nat
  | .three p0 _ _ => p0
  | .two x _ _ => x
  | .one c _ => c

/-- The entry of the rank table of node `n` is the rank of its pair mask. -/
noncomputable def rankOk (dims : Tree Nat) (n : Nat) (r : NodeRec) : Bool :=
  match relP (pointOf r.supp) r.supp with
  | some M => Frames.okC (pointOf r.supp) M && Nat.beq (Frames.dimC (pointOf r.supp) M) (dims.get width n)
  | none => false

theorem Tree.all_node {α : Type} (f : Nat → α → Bool) (pad : α → Bool) (bound : Nat) (l r : Tree α)
    (n w : Nat) : Tree.all f pad bound (.node l r) n w =
      (Tree.all f pad bound l n (w / 2) && Tree.all f pad bound r (n + w / 2) (w / 2)) := rfl

/-- A move of rank `r` counted negatively. -/
def neg (r : Nat) : Nat := Nat.add 24 r

/-- The moves of the final telescoping and the free use of a node of rank `d`. -/
def freeFS (d : Nat) : List Nat := [d, Nat.sub 23 d, neg 23]

/-- The moves of an addition of rank `dk` from its two sources of ranks `da`, `db`. -/
def addFS (dk da db : Nat) : List Nat :=
  [Nat.sub dk da, Nat.sub 23 dk, neg (Nat.sub 23 da), Nat.sub dk db, Nat.sub 23 dk,
    neg (Nat.sub 23 db), neg dk, neg (Nat.sub 23 dk), 23]

/-- The moves of node `k` with record `r`: an addition moves its argument slots from their
sources, and each argument without a donor is a free use of the argument. -/
noncomputable def nodeFS (dims : Tree Nat) (k : Nat) (r : NodeRec) : List Nat :=
  bif r.isAdd then
    addFS (dims.get width k) (dims.get width (r.donor0.getD r.a)) (dims.get width (r.donor1.getD r.b)) ++
      ((bif r.donor0.isNone then freeFS (dims.get width r.a) else []) ++
        (bif r.donor1.isNone then freeFS (dims.get width r.b) else []))
  else []

/-- The moves of root `j` with record `q`: its free use and its read frame, of rank `22` for an
output and the node's own rank for a centre. -/
noncomputable def rootFS (dims : Tree Nat) (j : Nat) (q : RootRec) : List Nat :=
  freeFS (dims.get width q.node) ++
    [Nat.sub (bif Nat.blt j (Nat.mul 3 leafCount) then 22 else dims.get width q.node)
        (dims.get width q.node),
      Nat.sub 23 (bif Nat.blt j (Nat.mul 3 leafCount) then 22 else dims.get width q.node),
      neg (Nat.sub 23 (dims.get width q.node))]

/-- No moves, by code. -/
def zeros : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Count one move. -/
def bump : Nat → List Nat → List Nat
  | _, [] => []
  | 0, x :: h => Nat.succ x :: h
  | i + 1, x :: h => x :: bump i h

/-- Add two counts. -/
def addH : List Nat → List Nat → List Nat
  | x :: a, y :: b => Nat.add x y :: addH a b
  | _, _ => []

/-- Count a list of moves. -/
def histOf : List Nat → List Nat
  | [] => zeros
  | e :: fs => bump e (histOf fs)

/-- Count the moves of the entries of a subtree of width `w` whose first index is `n`, below
`bound`. -/
def Tree.hist {α : Type} (f : Nat → α → List Nat) (bound : Nat) : Tree α → Nat → Nat → List Nat
  | .leaf v, n, _ => bif Nat.blt n bound then histOf (f n v) else zeros
  | .node l r, n, w =>
    addH (Tree.hist f bound l n (Nat.div w 2)) (Tree.hist f bound r (Nat.add n (Nat.div w 2)) (Nat.div w 2))

theorem Tree.hist_node {α : Type} (f : Nat → α → List Nat) (bound : Nat) (l r : Tree α) (n w : Nat) :
    Tree.hist f bound (.node l r) n w =
      addH (Tree.hist f bound l n (w / 2)) (Tree.hist f bound r (n + w / 2) (w / 2)) := rfl


end IntegerMultBounds.MathlibTM2.M8.Local
