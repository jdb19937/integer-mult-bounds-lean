module

public import IntegerMultBounds.MathlibTM2.M8.Local.Kernel

/-!
# Parity forests of pair masks, on bitmasks

The kernel-evaluable rank check of `Frames.SuppRank`, on bitmasks of the 23 points, written with
the kernel's natural-number primitives (`Local.testB`, `Local.bit`, `Nat.lor`, `Nat.land`) as the
other kernel checks are. A pair mask `M` relative to a point `c` gives the later neighbours of
each point (`upper`, `ups`), from which the neighbours of a set follow (`nbr`); a component is a
root and its breadth-first layers (`grow`, `comps`). `okC` checks that the layers are disjoint, cover
the points on edges, each lies in the neighbours of the one before, and each component is closed;
`dimC` counts the points on edges less the components without an edge inside the even or the
odd layers (`bipCount`). Nothing about the search is trusted: `SuppRank` proves the checks sound.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Frames

open IntegerMultBounds.MathlibTM2.M8.Local

/-- The later neighbours `w > u` of `u`: the bits `23 u + w` of `M`, without `c`. -/
def upper (c M u : Nat) : Nat :=
  bif Nat.beq u c then 0 else
    let x := Nat.shiftLeft (Nat.shiftRight (Nat.mod (Nat.shiftRight M (Nat.mul 23 u)) 8388608)
      (Nat.add u 1)) (Nat.add u 1)
    Nat.xor x (Nat.land x (bit c))

/-- The later neighbour masks of the points `u, …, u + n - 1`. -/
def ups (c M : Nat) : Nat → Nat → List Nat
  | _, 0 => []
  | u, n + 1 => upper c M u :: ups c M (Nat.add u 1) n

/-- The union of the masks of the points of `L`, from point `u` on. -/
def upFrom (L : Nat) : Nat → List Nat → Nat
  | _, [] => 0
  | u, x :: U => Nat.lor (bif testB L u then x else 0) (upFrom L (Nat.add u 1) U)

/-- The points, from `u` on, whose mask meets `L`. -/
def downFrom (L : Nat) : Nat → List Nat → Nat
  | _, [] => 0
  | u, x :: U => Nat.lor (bif Nat.beq (Nat.land x L) 0 then 0 else bit u) (downFrom L (Nat.add u 1) U)

/-- The neighbours of the points of `L`. -/
def nbr (U : List Nat) (L : Nat) : Nat := Nat.lor (upFrom L 0 U) (downFrom L 0 U)

/-- The points with a neighbour, from point `u` on. -/
def touchedFrom : Nat → List Nat → Nat
  | _, [] => 0
  | u, x :: U =>
    Nat.lor (Nat.lor (bif Nat.beq x 0 then 0 else bit u) x) (touchedFrom (Nat.add u 1) U)

/-- `x` without the points of `v`. -/
def minus (x v : Nat) : Nat := Nat.xor x (Nat.land x v)

/-- The union of a list of masks. -/
def unionL : List Nat → Nat
  | [] => 0
  | L :: ls => Nat.lor L (unionL ls)

/-- The breadth-first layers from `L`, avoiding `vis`. -/
def grow (U : List Nat) : Nat → Nat → Nat → List Nat
  | 0, L, _ => [L]
  | n + 1, L, vis =>
    let nx := minus (nbr U L) vis
    bif Nat.beq nx 0 then [L] else L :: grow U n nx (Nat.lor vis nx)

/-- The components of the points `V` from point `r` on: a search from each unvisited point. -/
def compsFrom (U : List Nat) (V : Nat) : Nat → Nat → Nat → List (Nat × List Nat)
  | _, 0, _ => []
  | r, n + 1, vis =>
    bif testB V r && !testB vis r then
      let ls := grow U 23 (bit r) (Nat.lor vis (bit r))
      (r, ls) :: compsFrom U V (Nat.add r 1) n (Nat.lor vis (unionL ls))
    else compsFrom U V (Nat.add r 1) n vis

/-- The even and the odd layers. -/
def parts : List Nat → Nat × Nat
  | [] => (0, 0)
  | L :: ls => let p := parts ls; (Nat.lor L p.2, p.1)

/-- Each layer lies in the neighbours of the one before. -/
def layersOk (U : List Nat) : Nat → List Nat → Bool
  | _, [] => true
  | L, L' :: ls => subB L' (nbr U L) && layersOk U L' ls

/-- A component: its first layer is its root, below 23, each later layer lies in the neighbours of
the one before, and the neighbours of its points are its points. -/
def compOk (U : List Nat) (p : Nat × List Nat) : Bool :=
  match p.2 with
  | [] => false
  | L :: ls => Nat.blt p.1 23 && Nat.beq L (bit p.1) && layersOk U L ls &&
      subB (nbr U (unionL p.2)) (unionL p.2)

/-- All components pass `compOk`. -/
def compsOk (U : List Nat) : List (Nat × List Nat) → Bool
  | [] => true
  | p :: cs => compOk U p && compsOk U cs

/-- The layers of all components. -/
def layersOf : List (Nat × List Nat) → List Nat
  | [] => []
  | p :: cs => p.2 ++ layersOf cs

/-- The masks are disjoint, and disjoint from `acc`. -/
def disjL : Nat → List Nat → Bool
  | _, [] => true
  | acc, L :: ls => Nat.beq (Nat.land L acc) 0 && disjL (Nat.lor acc L) ls

/-- No edge joins two points of `S`. -/
def freeOf (U : List Nat) (S : Nat) : Bool := Nat.beq (Nat.land (nbr U S) S) 0

/-- The number of bipartite components: no edge within the even or the odd layers. -/
def bipCount (U : List Nat) : List (Nat × List Nat) → Nat
  | [] => 0
  | p :: cs => Nat.add (bif freeOf U (parts p.2).1 && freeOf U (parts p.2).2 then 1 else 0)
      (bipCount U cs)

/-- The number of points below `n` of a mask. -/
def popc (x : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => Nat.add (popc x n) (bif testB x n then 1 else 0)

/-- The later neighbour masks of a pair mask. -/
def upsOf (c M : Nat) : List Nat := ups c M 0 23

/-- The points on edges of a pair mask. -/
def ptsOf (c M : Nat) : Nat := touchedFrom 0 (upsOf c M)

/-- The components of a pair mask. -/
def comps (c M : Nat) : List (Nat × List Nat) := compsFrom (upsOf c M) (ptsOf c M) 0 23 0

/-- The checks of the parity forest: disjoint layers covering the points on edges, and
components that pass `compOk`. -/
def okC (c M : Nat) : Bool :=
  disjL 0 (layersOf (comps c M)) && Nat.beq (unionL (layersOf (comps c M))) (ptsOf c M) &&
    compsOk (upsOf c M) (comps c M)

/-- The rank of the pair graph: points on edges less bipartite components. -/
def dimC (c M : Nat) : Nat := Nat.sub (popc (ptsOf c M) 23) (bipCount (upsOf c M) (comps c M))

end IntegerMultBounds.MathlibTM2.M8.Frames
