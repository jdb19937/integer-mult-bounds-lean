module
public import IntegerMultBounds.Machine.CompactComplexFixedNodePaths
@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexFixedNodePathAlgebra
noncomputable section
open CompactComplexFixedNodePaths
variable {t a N extra addressWidth : ℕ}
/-- Empty physical paths require no transition. -/
theorem nil (addressRoom : N ≤ 2^addressWidth) (stack : Fin t)
    (programs : Fin (N+extra) → Σ count, Program t count a)
    (edges : ∀ pc, Fin (programs pc).1 → Option (Fin (N+extra+2)))
    (startPC : Fin (N+extra+2)) (bank : Tapes t a) :
    pathWith addressRoom stack programs edges startPC bank 0 startPC bank :=
  FiniteFlowPath.Path.nil _ _
/-- Local path runtimes already include all their physical joins. -/
theorem append (addressRoom : N ≤ 2^addressWidth) (stack : Fin t)
    (programs : Fin (N+extra) → Σ count, Program t count a)
    (edges : ∀ pc, Fin (programs pc).1 → Option (Fin (N+extra+2)))
    {startPC middlePC finalPC : Fin (N+extra+2)} {initialBank middleBank finalBank : Tapes t a}
    {priorSteps eventSteps : ℕ}
    (priorPath : pathWith addressRoom stack programs edges startPC initialBank priorSteps middlePC middleBank)
    (eventPath : pathWith addressRoom stack programs edges middlePC middleBank eventSteps finalPC finalBank) :
    pathWith addressRoom stack programs edges startPC initialBank (priorSteps+eventSteps) finalPC finalBank :=
  FiniteFlowPath.append priorPath eventPath
attribute [local irreducible] pathWith
open CompactComplexCompletedLiveLower (Event schedule)
open CompactComplexScheduledPCLayout (originalCount)
open Networks.ComplexRecursiveCallSchema (Call)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites schedule
  CompactComplexCallReturn.addressCount CompactComplexCallReturn.addressWidth

/-- Empty paths specialize to the original finite node table symbolically. -/
theorem node_nil (tapesPositive : 0<t) (stack : Fin t)
    (childReturn : Call → Σ count, Program t count a)
    (controls : Fin 4 → Σ count, Program t count a) (event : Event → Σ count, Program t count a)
    (isStopped : Fin (controls 0).1 → Bool)
    (startPC : Fin (originalCount+(4+schedule.length)+2)) (bank : Tapes t a) :
    nodePath tapesPositive stack childReturn controls event isStopped startPC bank 0 startPC bank := by
  unfold nodePath
  exact nil _ _ _ _ startPC bank

/-- Fixed-node composition avoids unfolding the compiled block family. -/
theorem node_append (tapesPositive : 0<t) (stack : Fin t)
    (childReturn : Call → Σ count, Program t count a)
    (controls : Fin 4 → Σ count, Program t count a) (event : Event → Σ count, Program t count a)
    (isStopped : Fin (controls 0).1 → Bool)
    {startPC middlePC finalPC : Fin (originalCount+(4+schedule.length)+2)}
    {initialBank middleBank finalBank : Tapes t a} {priorSteps eventSteps : ℕ}
    (priorPath : nodePath tapesPositive stack childReturn controls event isStopped
      startPC initialBank priorSteps middlePC middleBank)
    (eventPath : nodePath tapesPositive stack childReturn controls event isStopped
      middlePC middleBank eventSteps finalPC finalBank) :
    nodePath tapesPositive stack childReturn controls event isStopped
      startPC initialBank (priorSteps+eventSteps) finalPC finalBank := by
  unfold nodePath at priorPath eventPath ⊢
  exact append _ _ _ _ priorPath eventPath
end
end IntegerMultBounds.Machine.CompactComplexFixedNodePathAlgebra
