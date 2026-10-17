module
import IntegerMultBounds.MathlibTM2.Cost.CompactCallerScalarBudget
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

/-! One explicit polynomial scalar budget for the actual compact caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast CompactGadgetReservationCapacity Filter
noncomputable section

private theorem scalarFields (N d g K D o W h b qrow f back active E working c p : ℕ)
    (hN : N≤p) (hd : d≤p) (hg : g≤p) (hK : K≤p) (hD : D≤d)
    (hfit : qrow+f+back≤D) (haddress : o+K*D≤N)
    (hactive : active=D-qrow-f-back) (hE : E≤W)
    (hwork : working≤2*W) (hW : W≤2^c*(p+1)) (hh : h≤p) (hb : b≤p) :
    CompactCallerScalarBounds N d g K D o W h b qrow f back active E working
      (compactCallerScalarBudget c p) := by
  have hB : 1≤compactCallerScalarBudget c p :=
    Nat.mul_pos (pow_pos (by decide : 0<2) _) (pow_pos (Nat.succ_pos p) _)
  have hp2 : p^2≤compactCallerScalarBudget c p :=
    (Nat.pow_le_pow_left (Nat.le_succ p) 2).trans
      (Nat.le_mul_of_pos_left _ (pow_pos (by decide : 0<2) _))
  have hp : p≤compactCallerScalarBudget c p := (Nat.le_self_pow (by decide : 2≠0) p).trans hp2
  have h2W : 2*W≤compactCallerScalarBudget c p := by
    calc
      2*W≤2*(2^c*(p+1)) := Nat.mul_le_mul_left _ hW
      _ = 2^(c+1)*(p+1) := by rw [pow_succ]; ring
      _ ≤ 2^(c+2)*(p+1)^2 := Nat.mul_le_mul
        (Nat.pow_le_pow_right (by decide : 0<2) (by omega : c+1≤c+2))
        (Nat.le_self_pow (by decide : 2≠0) _)
  have hWB : W≤compactCallerScalarBudget c p := (by omega : W≤2*W).trans h2W
  have hDp : D≤p := hD.trans hd
  have hbackD : back≤D := by omega
  have hqD : qrow+f≤D := by omega
  have hbaD : back+active≤D := by omega
  have hoff : o+K*back≤p :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left K hbackD) o).trans (haddress.trans hN)
  have haT : o+K*(back+active)≤p :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left K hbaD) o).trans (haddress.trans hN)
  have hKq : K*(qrow+f)≤p := (Nat.mul_le_mul_left K hqD).trans (by omega)
  refine ⟨hB,hN.trans hp,hd.trans hp,hg.trans hp,hK.trans hp,hDp.trans hp,
    (by omega : o≤p).trans hp,hWB,?_,hh.trans hp,hb.trans hp,
    (by omega : qrow≤p).trans hp,(by omega : f≤p).trans hp,
    (by omega : back≤p).trans hp,(by omega : active≤p).trans hp,
    hoff.trans hp,hE.trans hWB,hqD.trans (hDp.trans hp),haT.trans hp,hKq.trans hp,hwork.trans h2W⟩
  have hprod : d*g≤p^2 := by simpa only [pow_two] using Nat.mul_le_mul hd hg
  exact hprod.trans hp2

end
end IntegerMultBounds.MathlibTM2.Cost
