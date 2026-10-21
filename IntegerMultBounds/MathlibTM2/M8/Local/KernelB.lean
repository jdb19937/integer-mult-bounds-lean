module

public import IntegerMultBounds.MathlibTM2.M8.Local.DataB.BData
public import IntegerMultBounds.MathlibTM2.M8.Local.Data.Records
public import IntegerMultBounds.MathlibTM2.M8.Local.Data.Roots

/-!
# Kernel checks of the design-B plan

The design-B data (`DataB/*`) give every node its phase bits (`Φ`, bit 0; `Ψ`, bit 1) and its
serving order. The `Bool` checks here are the local phase conditions of `M8/Local/Phase.lean`,
read on the node and root records: per node (`bnodeOk`), per deferred use (`deferredOk`) and per
retained centre (`centreOk`). The generated modules `ChecksB/*` run them with `decide +kernel`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Local

noncomputable section

/-- The design-B entry of node `n`. -/
def bAt (n : Nat) : Nat × List Use := bdata.get width n

/-- An addition of `n` is in the first phase. -/
def phiB (n : Nat) : Bool := Nat.beq (Nat.land (bAt n).1 1) 1

/-- The copies of `n` are in the first phase. -/
def psiB (n : Nat) : Bool := Nat.beq (Nat.land (bAt n).1 2) 2

/-- An argument is a leaf or has its copies in the first phase. -/
def argOkB (y : Nat) : Bool := Nat.blt y leafCount || psiB y

/-- The local phase conditions at node `n` with entry `x`: copies in the first phase only with
the addition, an addition in it only with its arguments' copies, a linked user in it only with
its donor. -/
def bnodeOk (n : Nat) (x : Nat × List Use) : Bool :=
  (!Nat.beq (Nat.land x.1 2) 2 || Nat.beq (Nat.land x.1 1) 1) &&
    (!Nat.beq (Nat.land x.1 1) 1 ||
      (argOkB (records.get width n).a && argOkB (records.get width n).b)) &&
    (match (records.get width n).link with
      | some L => !phiB L.user || Nat.beq (Nat.land x.1 1) 1
      | none => true)

/-- `w` is a use of `y` that no donor links. -/
def freeB (y : Nat) : Use → Bool
  | .gate t pos =>
    Nat.blt t nodeCount && (records.get width t).isAdd && Nat.beq ((records.get width t).arg pos) y &&
      (match (records.get width t).donor pos with
        | none => true
        | some _ => false)
  | .root j => Nat.blt j rootCount && Nat.beq (roots.get rootWidth j).node y

/-- The node a use consumes. -/
def useNodeB : Use → Nat
  | .gate t pos => (records.get width t).arg pos
  | .root j => (roots.get rootWidth j).node

/-- A deferred use: a free use of its node; of an addition, a copy outside the first phase that
is not the use keeping the node's slot; of a leaf, a use whose consumer is outside the first
phase. -/
def deferredOk (u : Use) : Bool :=
  freeB (useNodeB u) u && Nat.blt (useNodeB u) nodeCount &&
    bif Nat.ble leafCount (useNodeB u) then
      !psiB (useNodeB u) &&
        (match (bAt (useNodeB u)).2 with
          | w :: _ => !decide (w = u) && freeB (useNodeB u) w
          | [] => false)
    else
      (match u with
        | .gate t _ => !phiB t
        | .root j => Nat.blt j (3 * leafCount))

/-- A retained centre ends in the first phase, at an addition. -/
def centreOk (j : Nat) : Bool :=
  Nat.ble leafCount (roots.get rootWidth j).node && psiB (roots.get rootWidth j).node

end

end IntegerMultBounds.MathlibTM2.M8.Local
