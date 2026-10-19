module

public import IntegerMultBounds.Networks.PairedSharedBound
public import IntegerMultBounds.Networks.SharedPointOutputIndex

/-! The sharp fifty-copy bounds for the structural shared circuit: 9,813 live
local additions per copy and 40,256 proved duplicate stars, with no generated
witness. These are scalar circuit bounds; the rank-frame assembly and literal
tape runtime remain separate obligations. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Shared50Certificate

open DisjointCircuit NeighborCounts SharedPointReplay SharedPointExecution

attribute [local irreducible] SharedPointReplay.circuit

/-- At most 450,394 distinct lifted supports over the fifty copies. -/
theorem support_image_bound :
    (SharedPointFamily.domain.image SharedPointFamily.support).card ≤ 450394 :=
  PairedStarShared.support_bound

/-- Physical roles allocated by the literal compiler, not an assigned cost. -/
theorem role_bound : code.state.next ≤ 509194 :=
  SharedPointExecution.role_bound support_image_bound

/-- Number of actual scalar XOR instructions emitted by the same compiler. -/
theorem instruction_bound : code.program.length ≤ 959588 :=
  SharedPointExecution.instruction_bound support_image_bound

theorem output_slot_bound (c : Fin 50) (j : Fin 1176) :
    code.outputSlot (SharedPointOutputIndex.index c j) < 509194 :=
  Nat.lt_of_lt_of_le (SharedPointExecution.output_slot_bound _
    (SharedPointOutputIndex.index_bound c j)) role_bound

end IntegerMultBounds.Networks.Shared50Certificate
