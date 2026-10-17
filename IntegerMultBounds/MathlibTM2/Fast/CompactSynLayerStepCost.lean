module
public import IntegerMultBounds.MathlibTM2.Node.CompactBasisRefresh
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRoundSources
public import IntegerMultBounds.MathlibTM2.Fast.SynRound
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd


/-! Exact non-top overhead of an actual compact round. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section

def compactSynLayerPrepareCost (G F N d g K D o W r h b : ℕ) :=
  (compactSynChunkSourceCost h b K D+(((4*d+4)+(4*g+4))+1))+
    (compactTopOriginalCost G F N d g K D o W 1+
      (compactBasisRefreshCost d g K D o r+(((2*d+2)+(2*g+2))+(2*o+2)+4)))

def compactSynLayerParkCost (N r working K ρ prLen cfgLen stash : ℕ) :=
  synRestUpCost N r working K ρ prLen+((stash+1)+(2*cfgLen+2))

def compactSynLayerUnparkCost (N r working K ρ prLen cfgLen stash : ℕ) :=
  ((2*cfgLen+11)+(2*cfgLen+2))+((stash+1)+synRestDownCost N r working K ρ prLen)

def compactSynLayerRoundOverhead (G F N d g K D o W r h b ρ working prLen cfgLen stash : ℕ) :=
  compactSynLayerPrepareCost G F N d g K D o W r h b+
    (compactSynLayerParkCost N r working K ρ prLen cfgLen stash+
      (compactSynLayerUnparkCost N r working K ρ prLen cfgLen stash+
        compactClear7Cost (compactZeroTail (compactBasisSetupValues d g K D o r))))

end
end IntegerMultBounds.MathlibTM2.Fast
