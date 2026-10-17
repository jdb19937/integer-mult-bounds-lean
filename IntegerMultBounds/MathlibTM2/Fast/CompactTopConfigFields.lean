module
public import IntegerMultBounds.MathlibTM2.Fast.SynRec
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
import Mathlib.Tactic.ENatToNat


/-! Runtime serialization of the complete compact top configuration, preserving
all outside rows. Derived scalar inputs are explicit; this primitive computes
the shift, emits all ten fields, and preserves its scalar sources. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

noncomputable def compactTopConfigFields : Pr P (nT SXReg) Q A U :=
  .seq (synHalfAdd (.p .D) (.s 25)) <|
  .seq (ucopy (sreg (.s 5)) (sreg (.s 16)) (sreg (.s 2))) <|
  .seq (synCF (.p .w)) <| .seq (synCF (.s 16)) <| .seq (synCF (.s 30)) <|
  .seq (synCF (.s 29)) <|
  .seq (synCF (.s 7)) <| .seq (synCF (.s 25)) <| .seq (synCF (.s 28)) <| .seq (synCF (.s 27)) <|
  .seq (synCF (.s 6)) (synCF (.p .D))

variable (body : P → Pr P (nT SXReg) Q A U)
  {R : Fin (nT SXReg) → List (Fin (A+4))}

/-- The step bound of `compactTopConfigFields`. -/
def compactTopConfigFieldsCost (W a' Dv q E Rv R2 aT Kq oS : ℕ) : ℕ :=
  (4 * Dv + 4 + (1 + (4 * (Dv + 1) + 4 + (2 * (Dv + 1) + 2 + (4 * q + 4))))) +
    (4 * ((Dv + 1) / 2 + q) + 4) +
    (4 * W + 5) + (4 * ((Dv + 1) / 2 + q + E) + 5) + (4 * a' + 5) + (4 * Rv + 5) + (4 * R2 + 5) +
    (4 * q + 5) + (4 * aT + 5) + (4 * Kq + 5) + (4 * oS + 5) + (4 * Dv + 5)

theorem sg_compactTopConfigFields (v : SynW → List (Fin (A + 4))) (W a' Dv q E Rv R2 aT Kq oS : ℕ)
    (ha : v (.s 30) = List.replicate a' tick) (hE : v (.s 16) = List.replicate E tick)
    (hRows : (v (.s 29)).length = Rv)
    (hR : v (.s 7) = List.replicate R2 tick) (hoS : v (.s 6) = List.replicate oS tick)
    (hq : v (.s 25) = List.replicate q tick) (haT : v (.s 28) = List.replicate aT tick)
    (hKq : v (.s 27) = List.replicate Kq tick)
    (h1 : v (.s 1) = []) (h2 : v (.s 2) = []) (h5 : v (.s 5) = []) (hcf : v (.p .cf) = [])
    (hW : (v (.p .w)).length = W) (hD : (v (.p .D)).length = Dv) :
    LayRuns body compactTopConfigFields (synG R v)
      (synG R (Function.update (Function.update (Function.update v (.s 5)
        (List.replicate ((Dv + 1) / 2 + q) tick)) (.s 16)
        (List.replicate ((Dv + 1) / 2 + q + E) tick)) (.p .cf)
        (topRec [W, (Dv + 1) / 2 + q + E, a', Rv, R2, q, aT, Kq, oS, Dv]).reverse))
      (compactTopConfigFieldsCost W a' Dv q E Rv R2 aT Kq oS) := by
  refine lr_weaken body
    ((sg_synHalfAdd body (x := .p .D) (y := .s 25) (by decide) (by decide) (by decide)
      (by decide) (by decide) _ Dv q hD (by simp [hq]) h1 h2 h5).seq <|
    (sgU_copy body (a := .s 5) (b := .s 16) (t := .s 2) (x := (Dv + 1) / 2 + q) (y := E)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp) (by simp [hE])).seq <|
    (sg_synCF body (x := .p .w) (by decide) (by decide) _ [] W (by simp [h2]) (by simp [hW])
      (by simp [hcf])).seq <|
    (sg_synCF body (x := .s 16) (by decide) (by decide) _ [W] ((Dv + 1) / 2 + q + E)
      (by simp [h2]) (by simp) (by simp)).seq <|
    (sg_synCF body (x := .s 30) (by decide) (by decide) _ [W, (Dv + 1) / 2 + q + E] a'
      (by simp [h2]) (by simp [ha]) (by simp)).seq <|
    (sg_synCF body (x := .s 29) (by decide) (by decide) _
      [W, (Dv + 1) / 2 + q + E, a'] Rv (by simp [h2]) (by simp [hRows]) (by simp)).seq <|
    (sg_synCF body (x := .s 7) (by decide) (by decide) _ [W, (Dv + 1) / 2 + q + E, a', Rv] R2
      (by simp [h2]) (by simp [hR]) (by simp)).seq <|
    (sg_synCF body (x := .s 25) (by decide) (by decide) _ [W, (Dv + 1) / 2 + q + E, a', Rv, R2]
      q (by simp [h2]) (by simp [hq]) (by simp)).seq <|
    (sg_synCF body (x := .s 28) (by decide) (by decide) _
      [W, (Dv + 1) / 2 + q + E, a', Rv, R2, q] aT (by simp [h2]) (by simp [haT]) (by simp)).seq <|
    (sg_synCF body (x := .s 27) (by decide) (by decide) _
      [W, (Dv + 1) / 2 + q + E, a', Rv, R2, q, aT] Kq (by simp [h2]) (by simp [hKq])
      (by simp)).seq <|
    (sg_synCF body (x := .s 6) (by decide) (by decide) _
      [W, (Dv + 1) / 2 + q + E, a', Rv, R2, q, aT, Kq] oS (by simp [h2]) (by simp [hoS])
      (by simp)).seq <|
    sg_synCF body (x := .p .D) (by decide) (by decide) _
      [W, (Dv + 1) / 2 + q + E, a', Rv, R2, q, aT, Kq, oS] Dv (by simp [h2]) (by simp [hD])
      (by simp)) ?_ ?_
  · refine congrArg (synG R) ?_
    funext y
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · simp only [compactTopConfigFieldsCost]
    omega

end
end IntegerMultBounds.MathlibTM2.Fast
