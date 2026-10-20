module

public import IntegerMultBounds.Networks.Shared50FixedControl
public import IntegerMultBounds.Machine.FlatCoordinateScheduleCompile
public import IntegerMultBounds.Networks.AffineFieldCoordinates
public import IntegerMultBounds.Machine.FlatCoordinateInitializedSchedule
public import IntegerMultBounds.Machine.FlatCoordinateCleanSchedule
public import IntegerMultBounds.Machine.Shared50TapeGlobal

/-! Fixed physical implementations of pieces of the actual interleaved Shared50
control. Segment certificates retain their original role and parent schedule;
scalar gates use the same fixed global role enumeration as the tape circuit.
This does not supply recursive interchange continuations or a whole-bank join. -/

@[expose] public section

namespace IntegerMultBounds.Machine.Shared50OrderedPieces
noncomputable section
open Networks Shared50OrderedControl
open Shared50GlobalBudget (World)
open Shared50FixedControl (control)
open ActualAffineScaling (modulus)
attribute [local irreducible] Shared50FixedControl.control Shared50GlobalCircuit.program50
  Shared50Finite.program SharedPointReplay.circuit SharedPointExecution.code

/-- An actual maximal nonrecursive run, with its original physical wire. -/
structure Segment where
  wire : World
  parent : FieldProgram
  ops : FieldProgram
  member : FramedControlSchedule.Step.edge wire parent ∈ control
  run_member : ops ∈ AffineFieldSegments.runs (AffineFieldSegments.split parent)

theorem segment_spec (seg : Segment) :
    seg.parent ∈ Shared50AffineControl.rationalSchedules ∧
    (∀ op ∈ seg.ops, op ∈ seg.parent) ∧
    (∀ op ∈ seg.ops, AffineFieldCoordinates.Nonrecursive op) := by
  have h : seg.parent ∈ FramedControlSchedule.programs control :=
    List.mem_filterMap.mpr ⟨.edge seg.wire seg.parent,seg.member,rfl⟩
  rw [Shared50FixedControl.programs_exact] at h
  exact ⟨h,AffineFieldSegments.split_run_spec _ _ seg.run_member⟩

/-- An actual scalar instruction at its retained interleaved position. -/
structure Gate where
  scalar : Circuit.Gate World (ZMod 2)
  member : FramedControlSchedule.Step.gate scalar ∈ control

theorem gate_xor (gate : Gate) : OneSourceCircuit.IsXor [gate.scalar] := by
  have hg : gate.scalar ∈ FramedControlSchedule.gates control :=
    List.mem_filterMap.mpr ⟨.gate gate.scalar,gate.member,rfl⟩
  rw [Shared50FixedControl.gates_exact] at hg
  intro g h
  have he : g = gate.scalar := List.mem_singleton.mp h
  subst g
  exact Shared50XorLists.global50 gate.scalar hg

end
end IntegerMultBounds.Machine.Shared50OrderedPieces
