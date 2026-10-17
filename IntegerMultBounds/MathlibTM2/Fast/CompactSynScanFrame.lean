module
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRoundFrame
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
import Mathlib.Tactic.ENatToNat


/-! Full-host frame equalities for the synthetic round scans. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Node
noncomputable section
variable {A : ℕ}

theorem compactSynView_wire {R : Fin compactMnT → List (Fin (A+4))}
    {io park : List (Fin (A+4))} {v : SynW → List (Fin (A+4))}
    (h : compactSynView R=synG (synIdle io park) v) (x : SynW) :
    R (compactSynDispatchReg x)=v x := by
  change compactSynView R (sreg x)=v x
  rw [h,synG_sreg]

theorem compactSynView_io_value {R : Fin compactMnT → List (Fin (A+4))}
    {io park : List (Fin (A+4))} {v : SynW → List (Fin (A+4))}
    (h : compactSynView R=synG (synIdle io park) v) :
    R (compactMnRg (.src (.v .io)))=io := by
  have he := congrFun h mnLio
  change R (compactMnLegacyReg (mnLayE mnLio))=synG (synIdle io park) v mnLio at he
  rw [mnLayE_io,compactMnLegacyReg_rg,synG_of_ne (lreg_out (by simp))] at he
  simpa [synIdle,mnLio,lreg] using he

theorem compactScan_update_io {T : ℕ} (R : Fin T → List (Fin (A+4)))
    {io c t : Fin T} (hc : c≠io) (ht : t≠io) (out out' cs ts : List (Fin (A+4))) :
    Function.update (Function.update (Function.update (Function.update R io out) c cs) t ts) io out'=
      Function.update (Function.update (Function.update R io out') c cs) t ts := by
  funext i
  by_cases hi : i=io
  · subst i; simp [hc.symm,ht.symm]
  · by_cases hic : i=c
    · subst i; simp [Function.update_apply,hc]
    · by_cases hit : i=t
      · subst i; simp [ht]
      · simp [hi,hic,hit]

theorem compactScan_restore {T : ℕ} (R : Fin T → List (Fin (A+4)))
    {io c t : Fin T} (hc : c≠io) (ht : t≠io) (out : List (Fin (A+4))) :
    Function.update (Function.update (Function.update R io out) c (R c)) t (R t)=
      Function.update R io out := by
  rw [show R c=(Function.update R io out) c by rw [Function.update_of_ne hc],Function.update_eq_self,
    show R t=(Function.update R io out) t by rw [Function.update_of_ne ht],Function.update_eq_self]

end
end IntegerMultBounds.MathlibTM2.Fast.Main
