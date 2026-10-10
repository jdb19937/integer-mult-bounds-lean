import IntegerMultBounds.Machine.CompactComplexScalarPrefixAdvance

/-! Actual integer scalar blocks advance the literal original framed-network
compiler networkPrefix. The input equality is the current aligned-networkPrefix invariant,
not an assumed completed-network result. -/
namespace IntegerMultBounds.Machine.CompactComplexActualScalarNetworkPrefix
noncomputable section
open Networks
open CompactComplexRecursiveGeometry (arity)
open CompactComplexScalarIntegerRows (GroupIndex Wire gates wireIndex guardBits)
open CompactComplexScalarRowBlock (wireCount)
open CompactComplexScalarSegmentRows (block)
open CompactComplexScalarSequenceSemantics (values Bound circuit)
open CompactComplexScalarPolynomialSequence (execute)
open CompactGadgetReservationShape (Shape)
open GaussianPrecision (BoundedGrid)
attribute [local irreducible] ComplexRank25.program ComplexFramedExecution.rows
  CompactComplexScalarIntegerRows.gates

private theorem compile_append {ι L R E : Type*} [DecidableEq ι] [CommRing R] [DecidableEq R]
    [AddCommGroup E] [Module R E] (frames : L → FramedCircuit.Frame R E)
    (current : ι → L) (xs ys : List (GroupedFrames.Vertex ι L R)) :
    GroupedModuleFrames.compile frames current (xs++ys)=
      GroupedModuleFrames.compile frames current xs++
      GroupedModuleFrames.compile frames (GroupedFrames.finalLabels current xs) ys := by
  induction xs generalizing current with
  | nil => rfl
  | cons v xs ih =>
    simp only [List.cons_append,GroupedModuleFrames.compile,GroupedFrames.finalLabels,ih,List.append_assoc]

def inputLabels : Wire → ComplexPhaseBudget.Label := GlobalLabels.source ComplexRank25.vector

def labels (g : ℕ) := GroupedFrames.finalLabels inputLabels (ComplexRank25.program.take g)

/-- Exact compiler networkPrefix of the original complex25 network. -/
def networkPrefix (columns g : ℕ) :=
  GroupedModuleFrames.compile (ComplexFramedExecution.frameOf columns) inputLabels
    (ComplexRank25.program.take g)

/-- Actual alignment immediately before the named scalar group's rows. -/
def alignment (columns : ℕ) (g : GroupIndex) :=
  FramedCircuit.edges
    (GroupedModuleFrames.profile (ComplexFramedExecution.frameOf columns) (labels g.val))
    (fun _ => ComplexFramedExecution.frameOf columns (CompactFramedScalarGrid.vertex g).label)
    (GroupedCircuit.touched (CompactFramedScalarGrid.vertex g).group)

/-- Remaining original groups and the original terminal sink incidences. -/
def networkTail (columns g : ℕ) :=
  GroupedModuleFrames.compile (ComplexFramedExecution.frameOf columns) (labels g)
    (ComplexRank25.program.drop g)++
  FramedCircuit.edges
    (GroupedModuleFrames.profile (ComplexFramedExecution.frameOf columns)
      (GroupedFrames.finalLabels inputLabels ComplexRank25.program))
    (GroupedModuleFrames.profile (ComplexFramedExecution.frameOf columns)
      (GlobalLabels.sink (Labels.binary 25) ComplexRank25.vector)) ComplexRank25.wires

/-- These prefixes are literal segments of the named original network,
including the full terminal scratch-wire incidence list. -/
theorem original_network_split (columns g : ℕ) :
    ComplexFramedExecution.network columns=networkPrefix columns g++networkTail columns g := by
  have hc := compile_append (ComplexFramedExecution.frameOf columns) inputLabels
    (ComplexRank25.program.take g) (ComplexRank25.program.drop g)
  rw [List.take_append_drop] at hc
  unfold ComplexFramedExecution.network GroupedModuleFrames.network networkPrefix networkTail labels inputLabels at *
  rw [hc]
  exact List.append_assoc _ _ _

/-- The physical scalar row names are the gate instructions following that
group's own alignment, at its genuine position in the original network. -/
theorem prefix_step (columns : ℕ) (g : GroupIndex) :
    networkPrefix columns (g.val+1)=networkPrefix columns g.val++alignment columns g++
      (gates g).map (FramedCircuit.Instruction.gate
        (E:=BinaryColumns.Arrays (25^3) columns)) := by
  unfold networkPrefix
  rw [List.take_succ_eq_append_getElem g.isLt,compile_append]
  simp only [GroupedModuleFrames.compile,GroupedCircuit.compileFramed,List.append_nil]
  simp only [alignment,labels,gates,CompactFramedScalarGrid.vertex,List.append_assoc]

private theorem run_gates {ι R E : Type*} [DecidableEq ι] [CommRing R]
    [AddCommGroup E] [Module R E] (gs : List (Circuit.Gate ι R)) (stored : ι → E) :
    FramedCircuit.run (gs.map FramedCircuit.Instruction.gate) stored=
      FramedCircuit.moduleRun gs stored := by
  induction gs generalizing stored with
  | nil => rfl
  | cons g gs ih => exact ih _

/-- Reconstruct every actual named wire from the real scalar records along
an arbitrary anchored native lookup. All wire and address spectators remain. -/
def bank {N : ℕ} (columns b n : ℕ)
    (data : Fin wireCount → Fin N → ButterflyStreamData.Coefficient)
    (lookup : BinaryColumns.Address (25^3) columns → Fin N) :
    Wire → BinaryColumns.Arrays (25^3) columns :=
  fun wire address => values b n data (lookup address) wire

/-- Genuine Path and the current scalar-networkPrefix Grid supply every signed
guard. The physical integer block has exactly the original framed gate action. -/
theorem group_gate_values {sh : Shape} {left exponent levels frames returned N : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left exponent levels frames returned)
    (columns : ℕ) (g : GroupIndex)
    (data : Fin wireCount → Fin N → ButterflyStreamData.Coefficient)
    (lookup : BinaryColumns.Address (25^3) columns → Fin N)
    (p C axes metadataP n : ℕ) (ha : 0<sh.active)
    (hp : p+2*sh.bits≤metadataP) (haxes : axes≤sh.bits)
    (hC : CompactFramedScalarGrid.growthConstant≤C)
    (hroom : CompactSpectatorInheritedGrid.dependencyCoefficient C+Nat.clog 2 (C+1)+
      (block g).length*guardBits≤sh.chunk)
    (hw : ∀ j i,(data j i).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (data j i).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1)
    (hg : ∀ wire i,BoundedGrid n
      (CompactFramedScalarGrid.bound g.val
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)))
      (values (ButterflyGuard.halfWidth metadataP sh.bits) n data i wire)) :
    bank columns (ButterflyGuard.halfWidth metadataP sh.bits) (n+(block g).length)
      (execute (block g) data) lookup=
    FramedCircuit.run ((gates g).map FramedCircuit.Instruction.gate)
      (bank columns (ButterflyGuard.halfWidth metadataP sh.bits) n data lookup) := by
  let M := CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)
  have hM : CompactFramedScalarGrid.bound g.val M≤
      CompactComplexScalarPathGuard.budget p C levels frames returned axes := by
    exact (CompactFramedScalarGrid.bound_le g.val M C hC).trans_eq
      (CompactRecursiveGridBudget.scalar_step p C levels (frames+2*returned+axes))
  have hb : Bound (ButterflyGuard.halfWidth metadataP sh.bits)
      (CompactComplexScalarPathGuard.power sh p C axes) data := by
    intro j i
    have hn := ButterflyGuard.represented_bound _ _ n _
      (GaussianPrecision.bound_mono hM (hg (wireIndex.symm j) i))
    simp only [Equiv.apply_symm_apply] at hn
    have hpower := Int.ofNat_le.mpr (CompactComplexScalarPathGuard.growth_power path p C axes).le
    exact ⟨hn.1.trans hpower,hn.2.trans hpower⟩
  rw [run_gates]
  funext wire address
  have h := CompactComplexScalarSequenceSemantics.sequence_values (block g) data _
    (CompactComplexScalarPathGuard.power sh p C axes) n hw hb
    (CompactComplexScalarRoleSemantics.stored_reserve sh p C axes metadataP (block g).length
      ha hp haxes hroom) (lookup address)
  rw [CompactComplexScalarSegmentRows.block_circuit] at h
  exact (congrFun h wire).trans
    (RationalScalarGrid.run_pointwise (gates g)
      (bank columns (ButterflyGuard.halfWidth metadataP sh.bits) n data lookup) wire address).symm

/-- Once actual child alignments establish the current literal compiler
networkPrefix, the physical scalar block closes the next group's exact network
networkPrefix equality. No complete-network equality is assumed. -/
theorem group_prefix_advance {sh : Shape} {left exponent levels frames returned N : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left exponent levels frames returned)
    (columns : ℕ) (g : GroupIndex)
    (data : Fin wireCount → Fin N → ButterflyStreamData.Coefficient)
    (lookup : BinaryColumns.Address (25^3) columns → Fin N)
    (p C axes metadataP n : ℕ) (ha : 0<sh.active)
    (hp : p+2*sh.bits≤metadataP) (haxes : axes≤sh.bits)
    (hC : CompactFramedScalarGrid.growthConstant≤C)
    (hroom : CompactSpectatorInheritedGrid.dependencyCoefficient C+Nat.clog 2 (C+1)+
      (block g).length*guardBits≤sh.chunk)
    (hw : ∀ j i,(data j i).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (data j i).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1)
    (hg : ∀ wire i,BoundedGrid n
      (CompactFramedScalarGrid.bound g.val
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)))
      (values (ButterflyGuard.halfWidth metadataP sh.bits) n data i wire))
    (original : Wire → BinaryColumns.Arrays (25^3) columns)
    (hprefix : bank columns (ButterflyGuard.halfWidth metadataP sh.bits) n data lookup=
      FramedCircuit.run (networkPrefix columns g.val++alignment columns g) original) :
    bank columns (ButterflyGuard.halfWidth metadataP sh.bits) (n+(block g).length)
      (execute (block g) data) lookup=
      FramedCircuit.run (networkPrefix columns (g.val+1)) original := by
  rw [group_gate_values path columns g data lookup p C axes metadataP n ha hp haxes hC hroom hw hg,
    hprefix,prefix_step]
  simp only [FramedCircuit.run_append]

end
end IntegerMultBounds.Machine.CompactComplexActualScalarNetworkPrefix
