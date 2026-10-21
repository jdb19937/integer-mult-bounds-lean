module

public import IntegerMultBounds.MathlibTM2.M8.Local.LocalSteps

/-!
# Kernel checks of the design-B node frames

A lifted node carries the frame `Frames.liftFrame c M r` of the roots it reaches: the outputs
`(c, {c, u, w})` for the pairs of `M` and, when `r`, the retained centre `c`. Its record is the
centre, the mask `M` and `r`; an unlifted node keeps its plain frame. The
checks, evaluated by `Checks/Lift*`:
* `liftOk` at node `n`: a lifted record is a valid mask of pairs avoiding `c`, with a parity
  forest (`okC`); the support lies in the star of `c` and avoids the points of `M`; and when
  the source of an argument (its donor, else the argument) is lifted, `n` is lifted at the same
  centre, with fewer pairs, and with the centre only if the source has it (`liftLe`);
* `liftRootOk` at root `j`: a lifted root node has the root's centre, and reaches the root's
  pair or the centre.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Local

noncomputable section

/-- A lift record: the centre, the mask of the pairs and whether the centre is reached. -/
structure LiftRec where
  c : Nat
  mask : Nat
  ret : Bool

/-- The points below `x` on pairs of `M`. -/
def ptsAux (M : Nat) : Nat → Nat
  | 0 => 0
  | x + 1 => Nat.lor (ptsAux M x) (bif Nat.beq (Nat.land M (touch x)) 0 then 0 else bit x)

/-- The points on pairs of `M`. -/
def onPts (M : Nat) : Nat := ptsAux M 23

/-- A successor's record `k` against its source's record `p`. -/
def liftLe : Option LiftRec → Option LiftRec → Bool
  | _, none => true
  | none, some _ => false
  | some k, some p => Nat.beq k.c p.c && subB k.mask p.mask && (!k.ret || p.ret)

/-- A lifted record is valid for support `s`. -/
def liftValid (s : Supp) : Option LiftRec → Bool
  | none => true
  | some L =>
    Nat.blt L.c 23 && subB L.mask (pairsWithout L.c) && Frames.okC L.c L.mask &&
      match relP L.c s with
      | some P => Nat.beq (Nat.land (onPts P) (onPts L.mask)) 0
      | none => false

variable (lifts : Tree (Option LiftRec))

/-- The lift check of node `n`. -/
def liftOk (n : Nat) (r : NodeRec) : Bool :=
  liftValid r.supp (lifts.get width n) &&
    bif r.isAdd then
      liftLe (lifts.get width n) (lifts.get width ((r.donor false).getD r.a)) &&
        liftLe (lifts.get width n) (lifts.get width ((r.donor true).getD r.b))
    else true

/-- The lift check of root `j`: for an output, the centre is the root's point of the leaf
triple and the pair its other two points; for the centre `c`, the centre is `c` and reached. -/
def liftRootOk (recs : Tree NodeRec) (j : Nat) (q : RootRec) : Bool :=
  match lifts.get width q.node with
  | none => true
  | some L =>
    bif Nat.blt j (Nat.mul 3 leafCount) then
      match (recs.get width (Nat.div j 3)).supp with
      | .three p0 p1 p2 =>
        bif Nat.beq (Nat.mod j 3) 0 then Nat.beq L.c p0 && testB L.mask (pb p1 p2)
        else bif Nat.beq (Nat.mod j 3) 1 then Nat.beq L.c p1 && testB L.mask (pb p0 p2)
        else Nat.beq L.c p2 && testB L.mask (pb p0 p1)
      | _ => false
    else Nat.beq L.c (Nat.sub j (Nat.mul 3 leafCount)) && L.ret

end

end IntegerMultBounds.MathlibTM2.M8.Local
