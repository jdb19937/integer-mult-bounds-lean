module

public import IntegerMultBounds.MathlibTM2.M8.Rev97Ranks
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphContract

/-!
# The schedule of the reversed family

The node's schedule is read off the network's control (`schedule`). An edge program on wire `i`
whose interchanges number `r > 0` is three pieces: its operations before the first interchange,
one block call of rank `r` on wire `i`, and its operations after the interchanges. An edge
program without interchanges, a gate and a reset are one nonrecursive piece each. The ranks of
the block calls are the network's child ranks (`ranks_schedule`), so the graph's recurrence is
`Rev97Ranks`' recurrence over `ranks97`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.Schedule

open IntegerMultBounds.Networks
open Graph (Piece)
open GraphContract (ranks)

variable {ι : Type} {m : ℕ}

/-- A nonrecursive piece: an edge segment, a gate or a reset. -/
inductive Seg (ι : Type) (m : ℕ) where
  | edge (wire : ι) (ops : FieldProgram m)
  | gate (g : Circuit.Gate ι (ZMod 2))
  | reset (wire : ι)

/-- A block call: its wire and its rank. -/
abbrev Call (ι : Type) := ι × ℕ

/-- The operations before the first interchange. -/
def before (p : FieldProgram m) : FieldProgram m := p.takeWhile fun op => !AffineFieldProgram.isInterchange op

/-- The operations after the interchanges. -/
def after (p : FieldProgram m) : FieldProgram m :=
  (p.dropWhile fun op => !AffineFieldProgram.isInterchange op).dropWhile AffineFieldProgram.isInterchange

/-- The pieces of one control step. -/
def stepPieces : Step ι (FieldProgram m) → List (Piece (Seg ι m) (Call ι))
  | .edge i p =>
    if 0 < AffineFieldProgram.interchanges p then
      [.seg (.edge i (before p)), .call (i, AffineFieldProgram.interchanges p), .seg (.edge i (after p))]
    else [.seg (.edge i p)]
  | .gate g => [.seg (.gate g)]
  | .reset w => [.seg (.reset w)]

/-- **The schedule** of a control. -/
def schedule (s : List (Step ι (FieldProgram m))) : List (Piece (Seg ι m) (Call ι)) :=
  s.flatMap stepPieces

theorem ranks_append {Seg Call : Type} (rank : Call → ℕ) :
    ∀ p q : List (Piece Seg Call), ranks rank (p ++ q) = ranks rank p ++ ranks rank q
  | [], _ => rfl
  | .seg _ :: p, q => ranks_append rank p q
  | .call c :: p, q => by simp only [List.cons_append, ranks, ranks_append rank p q]

/-- **The ranks of the schedule** are the child ranks of the control. -/
theorem ranks_schedule : ∀ s : List (Step ι (FieldProgram m)),
    ranks Prod.snd (schedule s) = childRanks s
  | [] => rfl
  | step :: s => by
    have ih := ranks_schedule s
    simp only [schedule, List.flatMap_cons, ranks_append] at ih ⊢
    rw [ih]
    cases step with
    | edge i p =>
      by_cases h : 0 < AffineFieldProgram.interchanges p
      · simp [stepPieces, h, ranks, childRanks, Step.programs]
      · simp [stepPieces, h, ranks, childRanks, Step.programs]
    | gate g => simp [stepPieces, ranks, childRanks, Step.programs]
    | reset w => simp [stepPieces, ranks, childRanks, Step.programs]

/-- The ranks of the stage-2 PR97 schedule are `ranks97`. -/
theorem ranks_schedule97 : ranks Prod.snd (schedule rev97m.control) = ranks97 := by
  rw [rev97m_control]; exact ranks_schedule _

end IntegerMultBounds.MathlibTM2.M8.RevMachine.Schedule
