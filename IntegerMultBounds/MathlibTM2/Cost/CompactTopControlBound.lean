module
public import IntegerMultBounds.MathlibTM2.Node.CompactTopProcStages
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
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
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal


/-! Linear volume bounds for actual top-level control stages. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Node

/-- Both full-array phase scans are linear in actual bit volume once address
length fits the coefficient payload. Configuration reads stay explicit. -/
theorem compactTopPhaseSCost_linear (cfg : List ℕ) (N R r w K ρ o D : ℕ)
    (hR : 1 ≤ R) (hrw : 1 ≤ r*w) (hN : N ≤ r*w)
    (hρo : ρ+o ≤ N) (hDK : D*K ≤ N) (hD : D ≤ N) :
    compactTopPhaseSCost cfg N R r w K ρ o D ≤
      3*topGetCost cfg + 512*(R*2^N*(r*w)) := by
  have hpow : 1 ≤ 2^N := Nat.one_le_pow N 2 (by decide)
  have hstock : 1 ≤ R*2^N := by nlinarith
  have hV : r*w ≤ R*2^N*(r*w) := Nat.le_mul_of_pos_left _ (by omega)
  have hNstock : R*2^N*N ≤ R*2^N*(r*w) := Nat.mul_le_mul_left _ hN
  have hstockV : R*2^N ≤ R*2^N*(r*w) := Nat.le_mul_of_pos_right _ hrw
  unfold compactTopPhaseSCost
  nlinarith only [hρo,hDK,hD,hN,hV,hNstock,hstockV,hstock]

/-- The final unit multiplication is linear in stream volume, with configuration
reads and the unary dimension header charged explicitly. -/
theorem compactTopUnitSCost_linear (cfg : List ℕ) (R N r w D : ℕ)
    (hw : 1 ≤ w) :
    compactTopUnitSCost cfg R N r w D ≤
      topGetCost cfg + 16*(R*2^N*(r*w)) + 6*D + 17 := by
  have hcoeff : R*2^N*r ≤ R*2^N*r*w := Nat.le_mul_of_pos_right _ hw
  unfold compactTopUnitSCost compactTopUnitCost
  nlinarith only [hcoeff, Nat.zero_le (R*2^N*r*w)]

/-- Widening charges the output width, including both unary header cleanups. -/
theorem compactTopWidenSCost_linear (cfg : List ℕ) (R N r w w' : ℕ)
    (hw' : 1 ≤ w') (hww : w ≤ w') :
    compactTopWidenSCost cfg R N r w w' ≤
      topGetCost cfg + 16*(R*2^N*(r*w')) + 12*w' + 16 := by
  have hcoeff : R*2^N*r ≤ R*2^N*r*w' := Nat.le_mul_of_pos_right _ hw'
  have hsub : w'-w+w=w' := Nat.sub_add_cancel hww
  have hsubmul := congrArg (fun x => (R*2^N*r)*x) hsub
  unfold compactTopWidenSCost topWidenCost
  nlinarith only [hcoeff,hsubmul,hww,Nat.sub_le w' w,Nat.zero_le (R*2^N*r*w')]

/-- Per-word truncation is linear in the working width. -/
theorem compactTopShiftWordCost_linear (w' s w : ℕ) (hsw : s+w ≤ w') :
    topShiftWordCost w' s w ≤ 16*w'+22 := by
  have hsub : w'-s-w+s+w=w' := by omega
  unfold topShiftWordCost
  omega

/-- Final truncation charges actual working-width volume and explicit headers. -/
theorem compactTopShiftSCost_linear (cfg : List ℕ) (R N r w' s w : ℕ)
    (hw' : 1 ≤ w') (hsw : s+w ≤ w') :
    compactTopShiftSCost cfg R N r w' s w ≤
      2*topGetCost cfg + 64*(R*2^N*(r*w')) + 16*w'+24 := by
  have hc := compactTopShiftWordCost_linear w' s w hsw
  have hcoeff : R*2^N*r ≤ R*2^N*r*w' := Nat.le_mul_of_pos_right _ hw'
  have hmul := Nat.mul_le_mul_left (R*2^N*r) hc
  have hw : w ≤ w' := by omega
  have hvol := Nat.mul_le_mul_left (R*2^N*r) hw
  have hsub : w'-s-w ≤ w' := (Nat.sub_le _ _).trans (Nat.sub_le _ _)
  unfold compactTopShiftSCost topShiftCost
  nlinarith only [hmul,hcoeff,hvol,hsw,hsub,Nat.zero_le (R*2^N*r*w')]

end IntegerMultBounds.MathlibTM2.Cost
