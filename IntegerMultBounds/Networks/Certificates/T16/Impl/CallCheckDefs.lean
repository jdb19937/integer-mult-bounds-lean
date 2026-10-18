module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.Roles
public import IntegerMultBounds.Networks.Certificates.T16.Impl.StreamLocal
public import IntegerMultBounds.Networks.Certificates.T16.Trace.Forward
public import IntegerMultBounds.Networks.Certificates.T16.Trace.Backward
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Catalog

/-! The data checks of a local invocation, as definitions only. The kernel checks of every
invocation import just this module, so edits to the proofs that use the checks do not rerun
them. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open BinaryWalsh Streams Geometry

/-- The coordinate entering at stage `s` in place `i`. -/
def entering (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 8) (i : Fin 8) : Fin 73 :=
  ⟨9 + 8 * (s - 1) + i.val, by omega⟩

/-- The nine low basis indices. -/
def lowIndices : List (Fin 73) := (List.finRange 73).filter fun k => k.val < 9

/-- The local indices at stage `s ≥ 1`: `B_0` and the entering coordinates. -/
def stageIndices (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 8) : List (Fin 73) :=
  0 :: (List.finRange 8).map (entering s hs)

/-- The local indices of the data chart at stage `s`. -/
def dataIndices (s : ℕ) : List (Fin 73) :=
  if hs : 1 ≤ s ∧ s ≤ 8 then stageIndices s hs else lowIndices

/-- The slot of an invocation in the hosted records. -/
def slotOf (s r : ℕ) : ℕ := s * 16 + r

/-- The entry label of register `w` in the word of orientation `rev`. -/
def entryLabel (rev : Bool) (w : ℕ) : ℕ :=
  if rev then Trace.backwardInitial.label w else Trace.forwardInitial.label w

/-- The exit label of register `w` in the word of orientation `rev`. -/
def exitLabel (rev : Bool) (w : ℕ) : ℕ :=
  if rev then Trace.backwardFinal.label w else Trace.forwardFinal.label w

/-- The group, stream and port of a family index. -/
def famReplica (f : ℕ) : ℕ := f / 896
def famStream (f : ℕ) : Fin 8 := toStream ((f % 896) / 112)
def famPort (f : ℕ) : ℕ := f % 112

/-- The hosted slice of a helper family at a slot, as a basis mask. -/
def helperMask (slot f : ℕ) : ℕ :=
  (hostAcc (groupData (famReplica f) (famPort f)) slot (famStream f)).1

/-- The basis indices in a mask. -/
def maskIndices (m : ℕ) : List (Fin 73) := (List.finRange 73).filter fun k : Fin 73 => m.testBit k.val

/-- Insert naturals into a bitmask, failing on a repeat. -/
def insertAll : ℕ → List ℕ → Option ℕ
  | m, [] => some m
  | m, f :: fs => if m.testBit f then none else insertAll (m ||| 2 ^ f) fs

/-- The families of the 704 non-private registers of an invocation. -/
def callFamilies (s r : ℕ) : List ℕ :=
  (List.range 112).map (fun a => famIdx r a (toStream (2 * localPair s))) ++
    (List.range 112).map (fun a => famIdx r a (toStream (2 * localPair s + 1))) ++
      rolesList s r

/-- The source frame of port `a` at stage `s`, and the others. -/
def frameX (s a : ℕ) : Fin 73 → ZMod 4 := (frameVec (portData a) s 0).toFun
def frameY (s a : ℕ) : Fin 73 → ZMod 4 := (frameVec (portData a) s 1).toFun

/-- The label pairs of the helpers. -/
def helperPairOK (a b : ℕ) : Bool :=
  ((catalog a).data.rank < (catalog b).data.rank) &&
    (((catalog a).data.rank == 0) || ((catalog b).data.rank == 9) ||
      (a == 2 && b == 999) || (a == 3 && b == 998))

/-- The data frames agree off the chart. -/
def extCheck (s a : ℕ) : Bool :=
  (List.finRange 73).all fun k => decide (k ∈ dataIndices s) ||
    (frameX s a k == frameX (s + 1) a k && frameY s a k == frameY (s + 1) a k &&
      frameX s a k == frameY (s + 1) a k)

/-- The checks of one helper register. -/
@[irreducible] def helperCheck (s r h f : ℕ) : Bool :=
  let m := helperMask (slotOf s r) f
  let a := entryLabel (localReverse s) (224 + h)
  let b := exitLabel (localReverse s) (224 + h)
  decide (f < 14336) &&
    ((hostAcc (groupData (famReplica f) (famPort f)) (slotOf s r) (famStream f)).2 == 0) &&
    decide ((maskIndices m).length ≤ 9) && helperPairOK a b &&
    ((catalog b).data.rank - (catalog a).data.rank == (maskIndices m).length)

/-- The checks of one invocation. -/
@[irreducible] def callCheck (s r : ℕ) : Bool :=
  ((rolesList s r).length == 480) && (insertAll 0 (callFamilies s r)).isSome &&
    ((List.range 480).zip (rolesList s r)).all (fun hf => helperCheck s r hf.1 hf.2) &&
    (List.range 112).all (extCheck s)

end IntegerMultBounds.Networks.Certificates.T16.Impl
