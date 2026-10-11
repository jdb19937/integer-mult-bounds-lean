module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyAlignedActualTable
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventInvariant

/-! Actual reached scalar steps execute inside the final shared-alphabet table,
with identical literal arrays and numerical/call invariants. No local execution
callback is supplied: the original reached scalar lifecycle provides its run. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexAlignedScalarEventPath
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactNativeRoleConjugatedPorts (encoding)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes ready output)
open CompactComplexScalarIntegerRows (GroupIndex gates guardBits)
open CompactComplexScalarSegmentRows (block)
open CompactComplexScalarPolynomialSequence (execute)
open CompactComplexDenominatorCapacity (scalarRows)
open CompactComplexSourceReadyReachedEventInvariant (Reached nextCaller)
open CompactComplexSourceReadyAlignedActualTable (savedStackSlot controls event classify)
open CompactComplexActualCallFullAlignment (localTapes)
variable {s q : ℕ} {sh : CompactGadgetReservationShape.Shape}
attribute [local irreducible] Networks.ComplexRank25.program
  Networks.ComplexRecursiveCallSchema.sites CompactComplexCompletedLiveLower.schedule
  CompactComplexRolePhaseSite.roleCount

def bank (v : Tapes (nodeTapes s roles) 2) :=
  (Alphabet.mapTapes encoding (ready v)).append (SharedBank.empty (localTapes roles) prime)

def path (P : Program ActivePrefixStageNative.tapes q prime)
    (headerStack pcStack liveStack : Fin s) :=
  CompactComplexFixedNodePaths.nodePath
    (Nat.zero_lt_of_lt (savedStackSlot pcStack).isLt) (savedStackSlot pcStack)
    (CompactComplexActualCallFullAlignment.childReturn P headerStack liveStack)
    (controls pcStack) (event P headerStack pcStack liveStack) (classify pcStack)

/-- Local rule names the actual final table without reducing its unrelated
recursive basis blocks during later reached-bank specialization. -/
theorem scalar_local (P : Program ActivePrefixStageNative.tapes q prime)
    (headerStack pcStack liveStack : Fin s)
    (i : Fin CompactComplexCompletedLiveLower.schedule.length) (g : GroupIndex)
    (hi : CompactComplexCompletedLiveLower.schedule.get i=CompactComplexCompletedLiveLower.Event.scalar g)
    (before after : Tapes (CompactComplexActualCallFullAlignment.tapes s roles) prime) (B : ℕ)
    (hlocal : HoareTime (CompactComplexSourceReadyAlignedActualTable.scalar (s:=s) g).2
      (fun z => z=before) (fun z => z=after) B) :
    ∃ m≤B+1,path P headerStack pcStack liveStack
      (CompactComplexScheduledPCLayout.eventPC i) before m
      (CompactComplexScheduledPCLayout.nextPC i) after :=
  CompactComplexFixedNodePaths.scalar_path
    (Nat.zero_lt_of_lt (savedStackSlot pcStack).isLt) (savedStackSlot pcStack)
    (CompactComplexActualCallFullAlignment.childReturn P headerStack liveStack)
    (controls pcStack) (event P headerStack pcStack liveStack) (classify pcStack)
    i g hi before after B hlocal

variable {stage : ActivePrefixStageParameters.Stage sh}
  {rows ell metadataP nodeExponent p C axes baseline levels frames returned n : ℕ}
  {pcStack : Fin s} {origin : ℤ}
  {calls : List Networks.ComplexRecursiveCallSchema.Call}
  {v : Tapes (nodeTapes s roles) 2}

/-- The real scalar table block and its paid edge retain the concrete next
reached invariant on the alphabet-lifted full caller and blank basis suffix. -/
theorem scalar_successor {left : ℕ}
    (P : Program ActivePrefixStageNative.tapes q prime)
    (dependency : CompactRecursiveDependencyBudget.Path sh.active left nodeExponent levels frames returned)
    (g : GroupIndex)
    (h : Reached stage rows ell metadataP nodeExponent p C axes baseline levels frames returned g.val n pcStack origin calls v)
    (hrows : 0<rows/roles) (hG : 0<sh.guard) (hK : 0<sh.chunk)
    (ha : 0<sh.active) (hp : p+2*sh.bits≤metadataP) (haxes : axes≤sh.bits)
    (hroom : CompactSpectatorInheritedGrid.dependencyCoefficient C+Nat.clog 2 (C+1)+(gates g).length*guardBits≤sh.chunk)
    (hC : CompactFramedScalarGrid.growthConstant≤C) (hbase : baseline≤p)
    (hdenRoom : CompactComplexDenominatorCapacity.room scalarRows≤sh.chunk)
    (headerStack liveStack : Fin s)
    (i : Fin CompactComplexCompletedLiveLower.schedule.length)
    (hi : CompactComplexCompletedLiveLower.schedule.get i=CompactComplexCompletedLiveLower.Event.scalar g) :
    ∃ hn : Reached stage rows ell metadataP nodeExponent p C axes baseline levels frames returned (g.val+1)
      (n+(gates g).length) pcStack origin calls (output v (nextCaller h g)),
      hn.data=execute (block g) h.data ∧
      ∃ m≤CompactComplexScalarCountLifecycle.roleTimeConstant (block g)*
        (rows*2^sh.bits*2^ell)*(ButterflyGuard.halfWidth metadataP sh.bits+2)+1,
        path P headerStack pcStack liveStack (CompactComplexScheduledPCLayout.eventPC i)
          (bank v) m (CompactComplexScheduledPCLayout.nextPC i) (bank (output v (nextCaller h g))) := by
  obtain ⟨hr,hn,he⟩ := CompactComplexSourceReadyReachedEventInvariant.scalar_successor
    dependency g h hrows hG hK ha hp haxes hroom hC hbase hdenRoom
  have hlift := CompactComplexSourceReadyAlignedActualTable.lift_runs _ _ _
    (SharedBank.empty (localTapes roles) prime) hr
  refine ⟨hn,he,?_⟩
  exact scalar_local P headerStack pcStack liveStack i g hi
    (bank v) (bank (output v (nextCaller h g))) _ hlift

end
end IntegerMultBounds.Machine.CompactComplexAlignedScalarEventPath
