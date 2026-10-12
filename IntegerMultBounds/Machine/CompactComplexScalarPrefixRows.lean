module

public import IntegerMultBounds.Machine.CompactComplexScalarSegmentRows
public import Mathlib.Data.List.FinRange

/-! Original named scalar rows for an arbitrary grouped-network prefix.
Symbolic list enumeration identifies their exact compiled circuit and length
without evaluating the concrete complex25 program. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexScalarPrefixRows
noncomputable section
open CompactComplexScalarIntegerRows (GroupIndex RowIndex gates)
open CompactComplexScalarSegmentRows (block)
open CompactComplexScalarSequenceSemantics (circuit)
open Networks
attribute [local irreducible] ComplexRank25.program CompactComplexScalarIntegerRows.gates
  ComplexFramedExecution.rows

/-- Every preceding original group, in its literal order, followed by that
group's original row names. Prefixes beyond the program length are clipped. -/
def prefixRows (scalarPrefix : ℕ) : List RowIndex :=
  ((List.finRange ComplexRank25.program.length).take scalarPrefix).flatMap block

private theorem indexed_prefix_flatMap {Element Output : Type*}
    (items : List Element) (render : Element → List Output) (prefixLength : ℕ) :
    ((List.finRange items.length).take prefixLength).flatMap (fun index => render items[index.val])=
      (items.take prefixLength).flatMap render := by
  have prefixEntries : ((List.finRange items.length).take prefixLength).map (fun index => items[index.val])=
      items.take prefixLength := by
    rw [List.map_take,←List.ofFn_eq_map,List.ofFn_getElem]
  simpa only [List.flatMap_map,Function.comp_def] using congrArg (List.flatMap render) prefixEntries

/-- The actual named scalar prefix is exactly the original rational compiled
prefix circuit, with no supplied circuit-equality premise. -/
theorem prefix_circuit (scalarPrefix : ℕ) :
    circuit (prefixRows scalarPrefix)=RationalScalarGrid.castRows (CompactFramedScalarGrid.rows scalarPrefix) := by
  unfold prefixRows circuit
  rw [List.map_flatMap]
  change ((List.finRange ComplexRank25.program.length).take scalarPrefix).flatMap
    (fun group => circuit (block group))=RationalScalarGrid.castRows (CompactFramedScalarGrid.rows scalarPrefix)
  simp_rw [CompactComplexScalarSegmentRows.block_circuit]
  unfold RationalScalarGrid.castRows
  rw [←List.map_flatMap]
  apply congrArg (List.map RationalScalarGrid.castGate)
  unfold CompactComplexScalarIntegerRows.gates CompactFramedScalarGrid.vertex
  have groupEnumeration := indexed_prefix_flatMap ComplexRank25.program
    (fun vertex => GroupedCircuit.compile vertex.group) scalarPrefix
  simpa only [CompactFramedScalarGrid.rows,GroupedCircuit.compileGroups,List.flatMap_map,Function.comp_def] using groupEnumeration

/-- Named row count is the genuine compiled scalar-prefix denominator count. -/
theorem prefix_length (scalarPrefix : ℕ) :
    (prefixRows scalarPrefix).length=(CompactFramedScalarGrid.rows scalarPrefix).length := by
  have circuitLength := congrArg List.length (prefix_circuit scalarPrefix)
  simpa only [circuit,RationalScalarGrid.castRows,List.length_map] using circuitLength

end
end IntegerMultBounds.Machine.CompactComplexScalarPrefixRows
