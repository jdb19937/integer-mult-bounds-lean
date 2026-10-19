module

public import Mathlib.Init

/-!
# Kernel-checked records of the PR97 witness

The PR97 side DAG is stored as one record per node, in compile order, in a static balanced tree
(`Tree`), with a second tree of root records. This file defines the records and the local checks
as `Bool`-valued functions; generated modules (`M8/Local/Data/*`, `M8/Local/Checks/*`) hold the
data and the `decide +kernel` proofs that the checks pass, and `M8/Local/Witness` turns passed
checks into statements about the DAG.

The checks are written for kernel reduction: records are structures, so fields are projections;
arithmetic uses the `Nat` functions themselves (`Nat.add`, `Nat.land`, …), which the kernel
evaluates on literals directly; lookups go through the recursor `Tree.rec`; range checks are
conjunctions over the tree.

**Pairs.** A pair `{u, w}` of points `u < w < 23` is bit `pb u w = 23·u + w` of a pair mask. The
triples through a point `c` are the pairs of points other than `c`.

**Supports.** A support is three points (a leaf), two points `x < y` with the set `Z` of third
points, or one point `c` with the mask `P` of pairs completing it to a triple.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Local

noncomputable section

/-- A static binary tree. -/
inductive Tree (α : Type) where
  | leaf (v : α)
  | node (l r : Tree α)

/-- `t.get w i` is the entry at index `i` of a tree of width `w` (a power of two): the left
subtree holds the first half of the indices. -/
def Tree.get {α : Type} (t : Tree α) : Nat → Nat → α :=
  Tree.rec (motive := fun _ => Nat → Nat → α) (fun v _ _ => v)
    (fun _ _ gl gr w i =>
      bif Nat.blt i (Nat.div w 2) then gl (Nat.div w 2) i else gr (Nat.div w 2) (Nat.sub i (Nat.div w 2))) t

/-- Every entry of a subtree of width `w` whose first index is `n` passes `f`; entries at
indices from `bound` on pass `pad`. -/
def Tree.all {α : Type} (f : Nat → α → Bool) (pad : α → Bool) (bound : Nat) : Tree α → Nat → Nat → Bool
  | .leaf v, n, _ => bif Nat.blt n bound then f n v else pad v
  | .node l r, n, w =>
    Tree.all f pad bound l n (Nat.div w 2) && Tree.all f pad bound r (Nat.add n (Nat.div w 2)) (Nat.div w 2)

/-! ### Records -/

/-- A support. -/
inductive Supp where
  /-- The triple `{p0, p1, p2}`, `p0 < p1 < p2`. -/
  | three (p0 p1 p2 : Nat)
  /-- The triples `{x, y, z}` for the points `z` of `Z`, `x < y`. -/
  | two (x y Z : Nat)
  /-- The triples `{c, u, w}` for the pairs `{u, w}` of `P`. -/
  | one (c P : Nat)

/-- A path of three edges `u – x – y – w` in a pair graph. -/
structure Path where
  u : Nat
  x : Nat
  y : Nat
  w : Nat

/-- A donor's link: its argument `operand` serves argument `pos` of the later node `user`. For a
donor whose pairs are not all the user's, a point `point` and one path per missing pair. -/
structure Link where
  operand : Bool
  user : Nat
  pos : Bool
  point : Nat
  paths : List Path

/-- A use that no donor links: argument `pos` of `user`, or root `j`. -/
inductive Free where
  | gate (user : Nat) (pos : Bool)
  | root (j : Nat)

/-- A node record. -/
structure NodeRec where
  isAdd : Bool
  a : Nat
  b : Nat
  link : Option Link
  donor0 : Option Nat
  donor1 : Option Nat
  free : Free
  supp : Supp

/-- A root record: node `node`, point `c`, and for an output the other points `a < b` of `T`. -/
structure RootRec where
  node : Nat
  c : Nat
  out : Option (Nat × Nat)

/-- Padding records are leaves of the triple `{0, 0, 0}` with root `0` as their free use. -/
def NodeRec.isPad (r : NodeRec) : Bool :=
  !r.isAdd && Nat.beq r.a 0 && Nat.beq r.b 0 && r.link.isNone && r.donor0.isNone && r.donor1.isNone

def RootRec.isPad (q : RootRec) : Bool := Nat.beq q.node 0 && Nat.beq q.c 0 && q.out.isNone

/-- The width of the node tree, and the node, leaf and root counts. -/
def width : Nat := 65536
def nodeCount : Nat := 64042
def leafCount : Nat := 1771
def rootWidth : Nat := 8192
def rootCount : Nat := 5336

/-! ### Pair masks -/

/-- The bit of the pair `{u, w}`. -/
def pb (u w : Nat) : Nat := bif Nat.blt u w then Nat.add (Nat.mul 23 u) w else Nat.add (Nat.mul 23 w) u

/-- `2 ^ k`. -/
def bit (k : Nat) : Nat := Nat.shiftLeft 1 k

/-- Bit `k` of `m`. -/
def testB (m k : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight m k) 1) 1

/-- `S ⊆ T` as bit sets. -/
def subB (S T : Nat) : Bool := Nat.beq (Nat.land S T) S

/-- Disjoint union: `a ⊔ b = c`. -/
def disjUnion (a b c : Nat) : Bool := Nat.beq (Nat.land a b) 0 && Nat.beq (Nat.lor a b) c

/-- The pairs `{o, z}` for the points `z < k` of `Z`. -/
def starAux (o Z : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => Nat.lor (starAux o Z k) (bif testB Z k then bit (pb o k) else 0)

/-- The pairs `{o, z}`, for the points `z` of `Z` below 23. -/
def starMask (o Z : Nat) : Nat := starAux o Z 23

/-- All pairs of points below 23. -/
def allPairs : Nat :=
  0x200000600000e00001e00003e00007e0000fe0001fe0003fe0007fe000ffe001ffe003ffe007ffe00fffe01fffe03fffe07fffe0ffffe1ffffe3ffffe7ffffe

/-- The pairs containing `u`. -/
def touch (u : Nat) : Nat := starMask u (Nat.xor 0x7fffff (bit u))

/-- The pairs avoiding `c`. -/
def pairsWithout (c : Nat) : Nat := Nat.xor allPairs (Nat.land allPairs (touch c))

/-- The third points allowed with `x ≠ y`. -/
def validZ (x y : Nat) : Nat := Nat.xor (Nat.xor 0x7fffff (bit x)) (bit y)

/-- The pair mask of a support relative to `c`, if `c` is a point of all its triples. -/
def relP (c : Nat) : Supp → Option Nat
  | .three p0 p1 p2 =>
    bif Nat.beq c p0 then some (bit (pb p1 p2))
    else bif Nat.beq c p1 then some (bit (pb p0 p2))
    else bif Nat.beq c p2 then some (bit (pb p0 p1)) else none
  | .two x y Z =>
    bif Nat.beq c x then some (starMask y Z) else bif Nat.beq c y then some (starMask x Z) else none
  | .one c' P => bif Nat.beq c c' then some P else none

/-- The third points of a support relative to `x < y`, if they are points of all its triples. -/
def relZ (x y : Nat) : Supp → Option Nat
  | .three p0 p1 p2 =>
    bif Nat.beq x p0 && Nat.beq y p1 then some (bit p2)
    else bif Nat.beq x p0 && Nat.beq y p2 then some (bit p1)
    else bif Nat.beq x p1 && Nat.beq y p2 then some (bit p0) else none
  | .two x' y' Z => bif Nat.beq x x' && Nat.beq y y' then some Z else none
  | .one _ _ => none

/-- Both masks exist and form the disjoint union `c`. -/
def optUnion (a b : Option Nat) (c : Nat) : Bool :=
  match a, b with
  | some a, some b => disjUnion a b c
  | _, _ => false

/-- The support of an addition is the disjoint union of its arguments' supports, and is valid. -/
def supportOk (s sa sb : Supp) : Bool :=
  match s with
  | .two x y Z =>
    Nat.blt x y && Nat.blt y 23 && subB Z (validZ x y) && optUnion (relZ x y sa) (relZ x y sb) Z
  | .one c P => Nat.blt c 23 && subB P (pairsWithout c) && optUnion (relP c sa) (relP c sb) P
  | .three _ _ _ => false

/-- The points of a leaf support, `(0, 0, 0)` for others. -/
def points3 : Supp → Nat × Nat × Nat
  | .three p0 p1 p2 => (p0, p1, p2)
  | _ => (0, 0, 0)

/-- Strict lexicographic order on triples of points. -/
def lexLt (a b : Nat × Nat × Nat) : Bool :=
  Nat.blt a.1 b.1 || (Nat.beq a.1 b.1 && (Nat.blt a.2.1 b.2.1 || (Nat.beq a.2.1 b.2.1 && Nat.blt a.2.2 b.2.2)))

/-! ### The checks -/

variable (recs : Tree NodeRec) (roots : Tree RootRec)

/-- A node's argument `pos`. -/
def NodeRec.arg (r : NodeRec) (pos : Bool) : Nat := bif pos then r.b else r.a

/-- A node's donor at argument `pos`. -/
def NodeRec.donor (r : NodeRec) (pos : Bool) : Option Nat := bif pos then r.donor1 else r.donor0

/-- One node: a leaf (`n < v`) is a triple, later in lexicographic order than the previous leaf;
an addition has earlier arguments and the disjoint union of their supports. -/
def nodeOk (n : Nat) (r : NodeRec) : Bool :=
  bif Nat.blt n leafCount then
    !r.isAdd &&
      (match r.supp with
        | .three p0 p1 p2 => Nat.blt p0 p1 && Nat.blt p1 p2 && Nat.blt p2 23
        | _ => false) &&
      (bif Nat.beq n 0 then true else lexLt (points3 (recs.get width (Nat.sub n 1)).supp) (points3 r.supp))
  else
    r.isAdd && Nat.blt r.a n && Nat.blt r.b n &&
      supportOk r.supp (recs.get width r.a).supp (recs.get width r.b).supp

/-- The points of a support. -/
def suppPoints : Supp → List Nat
  | .three p0 p1 p2 => [p0, p1, p2]
  | .two x y _ => [x, y]
  | .one c _ => [c]

/-- One path is three edges of `Pt` between distinct points other than `c`. -/
def pathOk (c Pt : Nat) (p : Path) : Bool :=
  !(Nat.beq p.u c) && !(Nat.beq p.x c) && !(Nat.beq p.y c) && !(Nat.beq p.w c) &&
    !(Nat.beq p.u p.x) && !(Nat.beq p.x p.y) && !(Nat.beq p.y p.w) && !(Nat.beq p.u p.w) &&
    Nat.blt p.u 23 && Nat.blt p.x 23 && Nat.blt p.y 23 && Nat.blt p.w 23 &&
    testB Pt (pb p.u p.x) && testB Pt (pb p.x p.y) && testB Pt (pb p.y p.w)

/-- The mask of the end pairs of the paths. -/
def endsMask : List Path → Nat
  | [] => 0
  | p :: ps => Nat.lor (bit (pb p.u p.w)) (endsMask ps)

/-- The span condition of a link from support `s` to the user's support `st`. -/
def spanOk (L : Link) (s st : Supp) : Bool :=
  match L.paths with
  | [] => (suppPoints st).any fun c =>
      match relP c s, relP c st with
      | some pn, some pt => subB pn pt
      | _, _ => false
  | ps =>
    match relP L.point s, relP L.point st with
    | some pn, some pt => ps.all (pathOk L.point pt) && Nat.beq (Nat.xor pn (Nat.land pn pt)) (endsMask ps)
    | _, _ => false

/-- One link: the donor `n` links its argument `operand`, which is argument `pos` of the user
`t > n`; the user records `n` as its donor there; the span condition holds. -/
def linkOk (n : Nat) (r : NodeRec) : Bool :=
  match r.link with
  | none => true
  | some L =>
    r.isAdd && Nat.blt n L.user && Nat.blt L.user nodeCount && (recs.get width L.user).isAdd &&
      Nat.beq ((recs.get width L.user).arg L.pos) (r.arg L.operand) &&
      (match (recs.get width L.user).donor L.pos with
        | some d => Nat.beq d n
        | none => false) &&
      spanOk L r.supp (recs.get width L.user).supp

/-- The donor recorded at argument `pos` of `n` links exactly there. -/
def donorOk (n : Nat) (pos : Bool) : Option Nat → Bool
  | none => true
  | some d =>
    Nat.blt d nodeCount &&
      (match (recs.get width d).link with
        | some L => Nat.beq L.user n && (L.pos == pos)
        | none => false)

/-- The free use of `n`: an argument of a later node with no donor there, or a root of `n`. -/
def freeOk (n : Nat) (r : NodeRec) : Bool :=
  match r.free with
  | .gate u pos =>
    Nat.blt n u && Nat.blt u nodeCount && (recs.get width u).isAdd &&
      Nat.beq ((recs.get width u).arg pos) n &&
      (match (recs.get width u).donor pos with
        | none => true
        | some _ => false)
  | .root j => Nat.blt j rootCount && Nat.beq (roots.get rootWidth j).node n

/-- All checks of one node. -/
def allOk (n : Nat) (r : NodeRec) : Bool :=
  nodeOk recs n r && linkOk recs n r && donorOk recs n false r.donor0 &&
    donorOk recs n true r.donor1 && freeOk recs roots n r

/-- Root `j`: for `j < 3v`, the output `(c, T)` with `T` the triple of leaf `j / 3` and `c` its
point `j % 3`, whose node has the pairs avoiding `T`; for `j = 3v + c`, the retained `c`, whose
node has the pairs avoiding `c`. -/
def rootOk (j : Nat) (q : RootRec) : Bool :=
  Nat.blt q.node nodeCount && Nat.blt q.c 23 &&
  match relP q.c (recs.get width q.node).supp with
  | none => false
  | some M =>
    match q.out with
    | some (a, b) =>
      Nat.blt j (Nat.mul 3 leafCount) && Nat.blt a b && Nat.blt b 23 && !(Nat.beq a q.c) &&
        !(Nat.beq b q.c) &&
        (match (recs.get width (Nat.div j 3)).supp with
          | .three p0 p1 p2 =>
            ((Nat.beq q.c p0 && Nat.beq a p1 && Nat.beq b p2 && Nat.beq (Nat.mod j 3) 0) ||
              (Nat.beq q.c p1 && Nat.beq a p0 && Nat.beq b p2 && Nat.beq (Nat.mod j 3) 1) ||
              (Nat.beq q.c p2 && Nat.beq a p0 && Nat.beq b p1 && Nat.beq (Nat.mod j 3) 2))
          | _ => false) &&
        Nat.beq M (Nat.xor (pairsWithout q.c) (Nat.land (pairsWithout q.c) (Nat.lor (touch a) (touch b))))
    | none =>
      Nat.beq j (Nat.add (Nat.mul 3 leafCount) q.c) && Nat.beq M (pairsWithout q.c)

end

end IntegerMultBounds.MathlibTM2.M8.Local
