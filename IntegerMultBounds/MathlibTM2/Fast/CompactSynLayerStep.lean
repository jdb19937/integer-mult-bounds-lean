module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepFrame
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRoundSources
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRoundRest
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRoundPark
public import IntegerMultBounds.MathlibTM2.Node.CompactBasisRefresh
public import IntegerMultBounds.MathlibTM2.Node.CompactTopProc
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Concrete compact chunk-round code, with original global inputs retained
across rounds and all temporary sources and compact fields restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

/-- Compute chunk metadata, read the retained original global values, and supply
one outside row. The coefficient multiplicity remains in the separate `p.r`. -/
def compactSynLayerSources : Pr P (nT CompactHostBReg) Q A U :=
  .seq compactSynChunkSourcePlaced (.seq compactSynGlobalRead compactSynOutsideRowPush)

/-- Construct actual original-input records, refresh five per-round basis values,
and erase their temporary source copies before parking persistent wires. -/
def compactSynLayerPrepare (G F : ℕ) : Pr P (nT CompactHostBReg) Q A U :=
  .seq compactSynLayerSources
    (.seq (compactTopPlaced G F (.ly 0))
      (.seq compactBasisRefresh compactSynSourceClear))

/-- The complete concrete round. The only procedure call is the actual compact
recursive layer used inside the top program. -/
def compactSynLayerStep (ds : ComplexFramedExecution.Directions) :
    Pr LProc (nT CompactHostBReg) Q A U :=
  .seq (compactSynLayerPrepare (gateCount (program ds)) (factorCount (program ds)))
    (.seq compactSynRestUp
      (.seq compactSynStash
        (.seq compactSynPushCfg
          (.seq (compactTopProg (.call .layer))
            (.seq compactSynDropCfg
              (.seq compactSynUnstash
                (.seq compactSynRestDown compactBasisRefreshCleanup)))))))

end
end IntegerMultBounds.MathlibTM2.Fast
