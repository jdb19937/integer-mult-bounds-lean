module

public import IntegerMultBounds.Networks.ComplexRecursiveCallSchema
public import IntegerMultBounds.Machine.CompactComplexRecursiveGeometry

/-! The Section 5 recursive geometry milestone. The canonical partition and
literal occurrence-indexed call schema are certified together; this theorem
does not assert execution of the recursive tape controller. -/

@[expose] public section

namespace IntegerMultBounds.Networks.ComplexRecursiveCallSchema
noncomputable section

open Machine.CompactComplexRecursiveGeometry

/-- The original active axes are covered by fitting base-15625 power pieces;
every actual child call occurs exactly once, the number of calls is the
original network rank sum, and stopping is the manuscript beta criterion.
Every descendant interval also fits inside the original active axes. -/
theorem schema_complete (activeAxes globalAxes remainingExponent : ℕ) :
    arity = 15625 ∧
    (widths activeAxes).sum = activeAxes ∧
    (∀ piece : Fin (exponents activeAxes).length,
      pieceLeft activeAxes piece + arity ^ pieceExponent activeAxes piece ≤ activeAxes) ∧
    (∀ {left remaining : ℕ}, Visit activeAxes left remaining →
      left + arity ^ remaining ≤ activeAxes) ∧
    calls.Nodup ∧
    (∀ call : Call, call ∈ calls) ∧
    calls.length = ComplexRank25.rankSum ∧
    (stopped globalAxes remainingExponent = true ↔
      remainingExponent = 0 ∨ (arity ^ remainingExponent) ^ 1000 < globalAxes) := by
  refine ⟨rfl, widths_sum activeAxes, piece_fits activeAxes, ?_,
    calls_nodup, calls_complete, calls_rankSum, stopped_iff globalAxes remainingExponent⟩
  intro left remaining visit
  exact visit.fits

end
end IntegerMultBounds.Networks.ComplexRecursiveCallSchema
