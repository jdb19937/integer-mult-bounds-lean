module
public import IntegerMultBounds.MathlibTM2.Fast.SynBase
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic.ReduceModChar
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
import Mathlib.Tactic.ENatToNat


/-! Unary top-level coordinates from original N,D,K,o and the actual reservation
counts. All input tapes are preserved, and every arithmetic temporary is restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

def compactTopCoordinates : Pr P (nT SXReg) Q A U :=
  .seq (ucopy (sreg (.p .D)) (sreg (.s 10)) (sreg (.s 2))) <|
  .seq (usub (sreg (.s 8)) (sreg (.s 10)) (sreg (.s 2))) <|
  .seq (synMulR (sreg (.p .K)) (sreg (.s 10)) (sreg (.s 11)) (sreg (.s 2)) (sreg (.s 3))) <|
  .seq (ucopy (sreg (.s 7)) (sreg (.s 11)) (sreg (.s 2))) <|
  .seq (ucopy (sreg (.p .N)) (sreg (.s 30)) (sreg (.s 2))) <|
  .seq (usub (sreg (.s 11)) (sreg (.s 30)) (sreg (.s 2))) <|
  .seq (ucopy (sreg (.s 8)) (sreg (.s 25)) (sreg (.s 2))) <|
  .seq (ucopy (sreg (.s 9)) (sreg (.s 25)) (sreg (.s 2))) <|
  .seq (ucopy (sreg (.s 5)) (sreg (.s 12)) (sreg (.s 2))) <|
  .seq (ucopy (sreg (.s 26)) (sreg (.s 12)) (sreg (.s 2))) <|
  .seq (synMulR (sreg (.p .K)) (sreg (.s 12)) (sreg (.s 28)) (sreg (.s 2)) (sreg (.s 3))) <|
  .seq (ucopy (sreg (.s 7)) (sreg (.s 28)) (sreg (.s 2))) <|
  .seq (synMulR (sreg (.p .K)) (sreg (.s 25)) (sreg (.s 27)) (sreg (.s 2)) (sreg (.s 3))) <|
  .seq (uclear (sreg (.s 10))) <|
  .seq (uclear (sreg (.s 11)))
    (uclear (sreg (.s 12)))

def compactTopCoordinatesCost (N D K q f b active o : ℕ) : ℕ :=
  (4*(D)+4)+((4*(q)+4)+((synMulRCost (K) (D-q))+((4*(o)+4)+((4*(N)+4)+((4*(o+K*(D-q))+4)+((4*(q)+4)+((4*(f)+4)+((4*(b)+4)+((4*(active)+4)+((synMulRCost (K) (active+b))+((4*(o)+4)+((synMulRCost (K) (f+q))+((2*(D-q)+2)+((2*(o+K*(D-q))+2)+((2*(active+b)+2))))))))))))))))

theorem sg_compactTopCoordinates (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (N D K q f b active o : ℕ)
    (hN : (v (.p .N)).length=N) (hD : (v (.p .D)).length=D) (hK : (v (.p .K)).length=K)
    (hq : (v (.s 8)).length=q) (hf : (v (.s 9)).length=f) (hb : (v (.s 5)).length=b)
    (hactive : (v (.s 26)).length=active) (ho : (v (.s 7)).length=o)
    (hz : ∀ i : Fin 32, i∈[2,3,10,11,12,25,27,28,30] → v (.s i)=[]) :
    LayRuns body compactTopCoordinates (synG R v)
      (synG R (Function.update (Function.update (Function.update (Function.update v
        (.s 30) (List.replicate (N-(o+K*(D-q))) tick))
        (.s 25) (List.replicate (q+f) tick))
        (.s 28) (List.replicate (o+K*(b+active)) tick))
        (.s 27) (List.replicate (K*(q+f)) tick)))
      (compactTopCoordinatesCost N D K q f b active o) := by
  have h2 := hz 2 (by simp)
  have h3 := hz 3 (by simp)
  have h10 := hz 10 (by simp)
  have h11 := hz 11 (by simp)
  have h12 := hz 12 (by simp)
  have h25 := hz 25 (by simp)
  have h27 := hz 27 (by simp)
  have h28 := hz 28 (by simp)
  have h30 := hz 30 (by simp)
  refine lr_weaken body
    ((sgU_copy body (R := R) (v := v) (a := .p .D) (b := .s 10) (t := .s 2) (x := D) (y := 0)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hD]) (by simp [h10])).seq <|
    (sgU_sub body (a := .s 8) (b := .s 10) (t := .s 2) (x := q) (y := D)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hq]) (by simp)).seq <|
    (sgU_mulR body (a := .p .K) (b := .s 10) (c := .s 11) (t₁ := .s 2) (t₂ := .s 3)
      (x := K) (y := D-q) (z := 0) (by decide)
      (by simp [h2]) (by simp [h3]) (by simp [hK]) (by simp) (by simp [h11])).seq <|
    (sgU_copy body (a := .s 7) (b := .s 11) (t := .s 2) (x := o) (y := K*(D-q))
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [ho]) (by simp)).seq <|
    (sgU_copy body (a := .p .N) (b := .s 30) (t := .s 2) (x := N) (y := 0)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hN]) (by simp [h30])).seq <|
    (sgU_sub body (a := .s 11) (b := .s 30) (t := .s 2) (x := o+K*(D-q)) (y := N)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp) (by simp)).seq <|
    (sgU_copy body (a := .s 8) (b := .s 25) (t := .s 2) (x := q) (y := 0)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hq]) (by simp [h25])).seq <|
    (sgU_copy body (a := .s 9) (b := .s 25) (t := .s 2) (x := f) (y := q)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hf]) (by simp)).seq <|
    (sgU_copy body (a := .s 5) (b := .s 12) (t := .s 2) (x := b) (y := 0)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hb]) (by simp [h12])).seq <|
    (sgU_copy body (a := .s 26) (b := .s 12) (t := .s 2) (x := active) (y := b)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hactive]) (by simp)).seq <|
    (sgU_mulR body (a := .p .K) (b := .s 12) (c := .s 28) (t₁ := .s 2) (t₂ := .s 3)
      (x := K) (y := active+b) (z := 0) (by decide)
      (by simp [h2]) (by simp [h3]) (by simp [hK]) (by simp) (by simp [h28])).seq <|
    (sgU_copy body (a := .s 7) (b := .s 28) (t := .s 2) (x := o) (y := K*(active+b))
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [ho]) (by simp)).seq <|
    (sgU_mulR body (a := .p .K) (b := .s 25) (c := .s 27) (t₁ := .s 2) (t₂ := .s 3)
      (x := K) (y := f+q) (z := 0) (by decide)
      (by simp [h2]) (by simp [h3]) (by simp [hK]) (by simp) (by simp [h27])).seq <|
    (sgU_clear body (a := .s 10) (x := D-q) (by simp)).seq <|
    (sgU_clear body (a := .s 11) (x := o+K*(D-q)) (by simp)).seq <|
    (sgU_clear body (a := .s 12) (x := active+b) (by simp))) ?_ (Nat.le_refl _)
  apply congrArg (synG R)
  funext z
  simp only [Function.update_apply]
  split_ifs <;> simp_all [Nat.add_comm]

end
end IntegerMultBounds.MathlibTM2.Fast
