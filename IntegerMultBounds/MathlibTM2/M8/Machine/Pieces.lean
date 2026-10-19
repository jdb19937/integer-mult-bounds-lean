module

public import IntegerMultBounds.MathlibTM2.M8.Machine.Net
public import IntegerMultBounds.Machine.FlatCoordinateCleanSchedule
public import IntegerMultBounds.Machine.OneSourceCircuit

/-!
# The pieces of the control

The control's steps become a fixed finite list of pieces (`pieces`), as
`Shared50PieceSchedule.pieces` does for Shared50:
* every edge program splits into its maximal nonrecursive runs (`Segment`), with one recursive
  interchange `call wire i j` between consecutive runs;
* every gate is an XOR of two distinct wires (`Gate`, `gate_xor`);
* every reset zeroes one wire (`Reset`).

Every field operation, gate and reset keeps its place (`expansion_exact`), and the list has
exactly `rankSum` calls (`calls_exact`). Each segment has one fixed clean machine
(`segment_realizes`), and each gate one fixed role-bank program (`gate_realizes`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine

noncomputable section
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
open ActualAffineScaling (modulus)
open AffineFieldSegments

variable [Net]

/-- A maximal nonrecursive run of an edge program, with its wire. -/
structure Segment where
  wire : Wire
  parent : FieldProgram
  ops : FieldProgram
  member : Step.edge wire parent ∈ control
  run_member : ops ∈ runs (split parent)

theorem Segment.good (seg : Segment) : Segments.Good seg.ops :=
  segment_good Net.supports seg.member seg.run_member

/-- The flat coordinate stages of a segment. -/
def Segment.stages (seg : Segment) : List (FlatCoordinateSchedule.Op (width + width)) :=
  Segments.description seg.ops seg.good

/-- The fixed clean machine of a segment. -/
def Segment.program (seg : Segment) := FlatCoordinateCleanSchedule.program seg.stages

/-- One fixed clean machine executes a segment at every width. -/
theorem Segment.realizes (seg : Segment) (b W : ℕ) (hW : 0 < W)
    (a : FlatCoordinateStages.Array (width + width) b W) :
    let _ : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩
    HoareTime seg.program
      (fun v => v = SharedBankStageInput.raw (FlatCoordinateShiftSharedBank.common a)
        (FlatCoordinateCleanSchedule.tapeCount seg.stages))
      (fun v => v = SharedBankStageInput.raw
        (FlatCoordinateShiftSharedBank.common (FlatCoordinateInitializedSchedule.array seg.stages b W hW a))
        (FlatCoordinateCleanSchedule.tapeCount seg.stages) ∧
        ∀ (s : Swap.Shear.State (Fin width) (ZMod (modulus b))) (j : Fin W),
          FlatCoordinateInitializedSchedule.array seg.stages b W hW a
            (FlatCoordinateLayout.index (AffineFieldCoordinates.embed (AffineFieldProgram.run
              (seg.ops.map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b)))) s)) j) =
                a (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j))
      (FlatCoordinateCleanSchedule.constant seg.stages * ((modulus b) ^ (width + width) * W)) :=
  Segments.realizes seg.ops seg.good b W hW a

/-- A gate of the control. -/
structure Gate where
  scalar : Circuit.Gate Wire (ZMod 2)
  member : Step.gate scalar ∈ control

theorem Gate.xor (gate : Gate) : OneSourceCircuit.IsXor [gate.scalar] := by
  intro g h
  have he : g = gate.scalar := List.mem_singleton.mp h
  subst g
  exact (Net.net).xor_gate _ gate.member

/-- The fixed role-bank program of a gate. -/
def Gate.program {a : ℕ} (gate : Gate) :=
  OneSourceCircuit.program (a := a) wireEquiv [gate.scalar] gate.xor

/-- A gate updates its target role by the exact module gate and keeps every other role,
background cell, head and counter. -/
theorem Gate.realizes {a L : ℕ} (gate : Gate)
    (background : Fin wireCount → ℤ → Fin (a + 4)) (origins : Fin wireCount → ℤ)
    (data : Wire → Fin L → ZMod 2) (bs : List Bool) (hL : Counter.value bs = L) :
    HoareTime (gate.program (a := a))
      (fun v => v = PointwiseRoleGate.bank background origins
        (SparseRoleCircuit.encoded (fun k i => data (wireEquiv k) i)) bs)
      (fun v => v = PointwiseRoleGate.bank background origins
        (SparseRoleCircuit.encoded (fun k i =>
          FramedCircuit.moduleGate gate.scalar data (wireEquiv k) i)) bs)
      (14 * L + 14 * bs.length + 34) := by
  have h := OneSourceCircuit.circuit_hoare wireEquiv [gate.scalar] gate.xor background origins data
    bs hL
  simpa only [Gate.program, List.length_singleton, one_mul, Circuit.run_cons, Circuit.run_nil,
    ← FramedCircuit.moduleGate_pointwise] using h

/-- A reset of the control. -/
structure Reset where
  wire : Wire
  member : Step.reset wire ∈ control

/-- A piece of the control. -/
inductive Piece where
  | segment (seg : Segment)
  | call (wire : Wire) (i j : Fin width)
  | gate (gate : Gate)
  | reset (reset : Reset)

/-- The pieces of one edge program: its runs, with a call between consecutive runs. Empty runs
are kept, so adjacent calls have an explicit continuation slot. -/
def edgePieces (wire : Wire) (parent : FieldProgram) (hp : Step.edge wire parent ∈ control) :
    (s : Segments width ℚ) → (∀ ops ∈ runs s, ops ∈ runs (split parent)) → List Piece
  | .done ops, hs => [.segment ⟨wire, parent, ops, hp, hs ops (by simp [runs])⟩]
  | .boundary ops i j tail, hs =>
      .segment ⟨wire, parent, ops, hp, hs ops (by simp [runs])⟩ :: .call wire i j ::
        edgePieces wire parent hp tail
          (fun ops h => hs ops (by simp only [runs, List.mem_cons]; exact Or.inr h))

def piecesOf (step : {step : Control // step ∈ control}) : List Piece :=
  match step with
  | ⟨.edge wire parent, hp⟩ => edgePieces wire parent hp (split parent) (fun _ h => h)
  | ⟨.gate g, hg⟩ => [.gate ⟨g, hg⟩]
  | ⟨.reset w, hr⟩ => [.reset ⟨w, hr⟩]

/-- The fixed finite list of pieces. -/
def pieces : List Piece := control.attach.flatMap piecesOf

/-- One elementary instruction. -/
inductive Atom where
  | field (wire : Wire) (op : AffineFieldProgram.Op (Fin width) ℚ)
  | gate (g : Circuit.Gate Wire (ZMod 2))
  | reset (wire : Wire)

def expandPiece : Piece → List Atom
  | .segment seg => seg.ops.map (Atom.field seg.wire)
  | .call wire i j => [.field wire (.interchange i j)]
  | .gate gate => [.gate gate.scalar]
  | .reset r => [.reset r.wire]

def expandControl : Control → List Atom
  | .edge wire p => p.map (Atom.field wire)
  | .gate g => [.gate g]
  | .reset wire => [.reset wire]

theorem edgePieces_expand (wire : Wire) (parent : FieldProgram)
    (hp : Step.edge wire parent ∈ control) (s : Segments width ℚ)
    (hs : ∀ ops ∈ runs s, ops ∈ runs (split parent)) :
    (edgePieces wire parent hp s hs).flatMap expandPiece = (flatten s).map (Atom.field wire) := by
  induction s with
  | done ops =>
    simp only [edgePieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, expandPiece, flatten]
  | boundary ops i j tail ih =>
    simp only [edgePieces, List.flatMap_cons, expandPiece, List.singleton_append, ih,
      flatten, List.map_append, List.map_cons]

theorem piecesOf_expand (step : {step : Control // step ∈ control}) :
    (piecesOf step).flatMap expandPiece = expandControl step.val := by
  obtain ⟨step, h⟩ := step
  cases step with
  | edge wire p => exact (edgePieces_expand wire p h (split p) _).trans (by rw [flatten_split]; rfl)
  | gate g => rfl
  | reset w => rfl

/-- Every field operation, gate and reset occurs at exactly its original place. -/
theorem expansion_exact : pieces.flatMap expandPiece = control.flatMap expandControl := by
  rw [pieces, List.flatMap_assoc]
  have he : (fun step : {step : Control // step ∈ control} => (piecesOf step).flatMap expandPiece) =
      fun step => expandControl step.val := funext piecesOf_expand
  rw [he]
  simp only [List.flatMap_def, List.attach_map_val]

def Piece.calls : Piece → ℕ
  | .call _ _ _ => 1
  | _ => 0

theorem edgePieces_calls (wire : Wire) (parent : FieldProgram)
    (hp : Step.edge wire parent ∈ control) (s : Segments width ℚ)
    (hs : ∀ ops ∈ runs s, ops ∈ runs (split parent)) :
    ((edgePieces wire parent hp s hs).map Piece.calls).sum = recursiveCalls s := by
  induction s with
  | done ops => rfl
  | boundary ops i j tail ih =>
    simp only [edgePieces, List.map_cons, List.sum_cons, Piece.calls, zero_add, ih, recursiveCalls]
    omega

def controlCalls : Control → ℕ
  | .edge _ p => recursiveCalls (split p)
  | _ => 0

theorem piecesOf_calls (step : {step : Control // step ∈ control}) :
    ((piecesOf step).map Piece.calls).sum = controlCalls step.val := by
  obtain ⟨step, h⟩ := step
  cases step with
  | edge wire p => exact edgePieces_calls wire p h (split p) _
  | gate g => rfl
  | reset w => rfl

private theorem controlCalls_sum (steps : List Control) :
    (steps.map controlCalls).sum = calls steps := by
  induction steps with
  | nil => rfl
  | cons step steps ih =>
    cases step with
    | edge wire p =>
      simp only [List.map_cons, List.sum_cons, controlCalls, ih, calls, Step.programs,
        List.filterMap_cons, split_recursiveCalls]
    | gate g =>
      simpa only [List.map_cons, List.sum_cons, controlCalls, zero_add, calls, Step.programs,
        List.filterMap_cons] using ih
    | reset w =>
      simpa only [List.map_cons, List.sum_cons, controlCalls, zero_add, calls, Step.programs,
        List.filterMap_cons] using ih

/-- Exact count of the recursive calls in the fixed list. -/
theorem calls_exact : (pieces.map Piece.calls).sum = (Net.net).rankSum := by
  rw [pieces, List.map_flatMap, List.flatMap_def, List.sum_flatten, List.map_map]
  have he : (fun step : {step : Control // step ∈ control} => ((piecesOf step).map Piece.calls).sum) =
      fun step => controlCalls step.val := funext piecesOf_calls
  change (control.attach.map (fun step => ((piecesOf step).map Piece.calls).sum)).sum = _
  rw [he, List.attach_map_val, controlCalls_sum, (Net.net).calls_exact]

end
end IntegerMultBounds.MathlibTM2.M8.Machine
