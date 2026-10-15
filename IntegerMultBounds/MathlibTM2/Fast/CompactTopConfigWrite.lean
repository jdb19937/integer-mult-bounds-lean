module

public import IntegerMultBounds.MathlibTM2.Fast.CompactTopConfigFields

/-! Complete ten-field serialization and guarded working width. All sources and
scratch are restored literally; only the configuration and working-width outputs change. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

def compactTopConfigWrite : Pr P (nT SXReg) Q A U :=
  .seq compactTopConfigFields <|
  .seq (synW2P (.s 16)) <|
  .seq (usub (sreg (.s 5)) (sreg (.s 16)) (sreg (.s 2))) (uclear (sreg (.s 5)))

def compactTopConfigWriteCost (W a' Dv q E Rv R2 aT Kq oS : ℕ) : ℕ :=
  compactTopConfigFieldsCost W a' Dv q E Rv R2 aT Kq oS+
    ((4*W+4+(4*((Dv+1)/2+q+E)+4+(4*Dv+4)))+
      ((4*((Dv+1)/2+q)+4)+(2*((Dv+1)/2+q)+2)))

variable (body : P → Pr P (nT SXReg) Q A U)
  {R : Fin (nT SXReg) → List (Fin (A+4))}

theorem sg_compactTopConfigWrite (v : SynW → List (Fin (A + 4))) (W a' Dv q E Rv R2 aT Kq oS : ℕ)
    (ha : v (.s 30) = List.replicate a' tick) (hE : v (.s 16) = List.replicate E tick)
    (hRows : (v (.s 29)).length = Rv)
    (hR : v (.s 7) = List.replicate R2 tick) (hoS : v (.s 6) = List.replicate oS tick)
    (hq : v (.s 25) = List.replicate q tick) (haT : v (.s 28) = List.replicate aT tick)
    (hKq : v (.s 27) = List.replicate Kq tick)
    (h1 : v (.s 1) = []) (h2 : v (.s 2) = []) (h5 : v (.s 5) = []) (hcf : v (.p .cf) = [])
    (hw2 : v (.p .w2) = [])
    (hW : (v (.p .w)).length = W) (hD : (v (.p .D)).length = Dv) :
    LayRuns body compactTopConfigWrite (synG R v)
      (synG R (Function.update (Function.update v (.p .cf)
        (topRec [W, (Dv + 1) / 2 + q + E, a', Rv, R2, q, aT, Kq, oS, Dv]).reverse)
        (.p .w2) (List.replicate (W+((Dv+1)/2+q+E)+Dv) tick)))
      (compactTopConfigWriteCost W a' Dv q E Rv R2 aT Kq oS) := by
  have hc := sg_compactTopConfigFields body (R := R) v W a' Dv q E Rv R2 aT Kq oS
    ha hE hRows hR hoS hq haT hKq h1 h2 h5 hcf hW hD
  refine lr_weaken body (hc.seq <|
    (sg_synW2P body (x := .s 16) (by decide) (by decide) _ W ((Dv+1)/2+q+E) Dv
      (by simp [h2]) (by simp [hw2]) (by simp [hW]) (by simp) (by simp [hD])).seq <|
    (sgU_sub body (a := .s 5) (b := .s 16) (t := .s 2)
      (x := (Dv+1)/2+q) (y := (Dv+1)/2+q+E) (by decide) (by decide) (by decide)
      (by simp [h2]) (by simp) (by simp)).seq <|
    sgU_clear body (a := .s 5) (x := (Dv+1)/2+q) (by simp)) ?_ (Nat.le_refl _)
  apply congrArg (synG R)
  funext z
  simp only [Function.update_apply]
  split_ifs <;> simp_all

end
end IntegerMultBounds.MathlibTM2.Fast
