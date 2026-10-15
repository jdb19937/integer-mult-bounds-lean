module

public import IntegerMultBounds.MathlibTM2.Fast.CompactTopConfigRows
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopConfigWrite

/-! Complete top configuration from derived scalar coordinates. The machine
computes the global recursive divisor and exact padded row stock, serializes
all ten fields, computes the guarded working width and restores its scratch.
Deriving a, q, aT and K*q from original reservation inputs is a separate stage. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

def compactTopConfig : Pr P (nT SXReg) Q A U :=
  .seq compactTopConfigRows (.seq compactTopConfigWrite (uclear (sreg (.s 7))))

def compactTopConfigCost (d W a D q E Rv aT K oS : ℕ) : ℕ :=
  compactTopConfigRowsCost d a Rv+
    (compactTopConfigWriteCost W a D q E Rv (compactTopRows d Rv a) aT (K*q) oS+
      (2*compactTopRows d Rv a+2))

private theorem sg_compactTopConfigOfRows (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (W a D q E Rv R2 aT K oS rowCost : ℕ) (rowProg : Pr P (nT SXReg) Q A U)
    (ha : v (.s 30)=List.replicate a tick) (hE : v (.s 16)=List.replicate E tick)
    (hRows : (v (.s 29)).length=Rv) (hoS : v (.s 6)=List.replicate oS tick)
    (hq : v (.s 25)=List.replicate q tick) (haT : v (.s 28)=List.replicate aT tick)
    (hKq : v (.s 27)=List.replicate (K*q) tick)
    (h1 : v (.s 1)=[]) (h2 : v (.s 2)=[]) (h5 : v (.s 5)=[]) (h7 : v (.s 7)=[])
    (hcf : v (.p .cf)=[]) (hw2 : v (.p .w2)=[])
    (hW : (v (.p .w)).length=W) (hD : (v (.p .D)).length=D)
    (hr : LayRuns body rowProg (synG R v)
      (synG R (Function.update v (.s 7) (List.replicate R2 tick))) rowCost) :
    LayRuns body (.seq rowProg (.seq compactTopConfigWrite (uclear (sreg (.s 7))))) (synG R v)
      (synG R (Function.update (Function.update v (.p .cf)
        (topRec (topCfg W ((D+1)/2+q+E) a Rv R2 q aT K oS D)).reverse)
        (.p .w2) (List.replicate (W+((D+1)/2+q+E)+D) tick)))
      (rowCost+(compactTopConfigWriteCost W a D q E Rv R2 aT (K*q) oS+(2*R2+2))) := by
  have hc := sg_compactTopConfigWrite body (R := R)
    (Function.update v (.s 7) (List.replicate R2 tick)) W a D q E Rv R2 aT (K*q) oS
    (by simp [ha]) (by simp [hE]) (by simp [hRows]) (by simp)
    (by simp [hoS]) (by simp [hq]) (by simp [haT]) (by simp [hKq])
    (by simp [h1]) (by simp [h2]) (by simp [h5]) (by simp [hcf])
    (by simp [hw2]) (by simp [hW]) (by simp [hD])
  refine lr_weaken body (hr.seq (hc.seq
    (sgU_clear body (a := .s 7) (x := R2) (by simp)))) ?_ (Nat.le_refl _)
  apply congrArg (synG R)
  funext z
  simp only [Function.update_apply,topCfg]
  split_ifs <;> simp_all

/-- The exact original global depth is computed internally; R2 is never an
assumed runtime descriptor. Every source and temporary tape is restored. -/
theorem sg_compactTopConfig (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (d W a D q E Rv aT K oS : ℕ) (hd : 0<d) (hdv : (v (.s 0)).length=d)
    (ha : v (.s 30)=List.replicate a tick) (hE : v (.s 16)=List.replicate E tick)
    (hRows : (v (.s 29)).length=Rv) (hoS : v (.s 6)=List.replicate oS tick)
    (hq : v (.s 25)=List.replicate q tick) (haT : v (.s 28)=List.replicate aT tick)
    (hKq : v (.s 27)=List.replicate (K*q) tick)
    (hcf : v (.p .cf)=[]) (hw2 : v (.p .w2)=[])
    (hW : (v (.p .w)).length=W) (hD : (v (.p .D)).length=D)
    (hz : ∀ i : Fin 32, i∈[1,2,3,4,5,7,8,9,10,11,12,13,14,17,22,23] → v (.s i)=[]) :
    LayRuns body compactTopConfig (synG R v)
      (synG R (Function.update (Function.update v (.p .cf)
        (topRec (topCfg W ((D+1)/2+q+E) a Rv (compactTopRows d Rv a) q aT K oS D)).reverse)
        (.p .w2) (List.replicate (W+((D+1)/2+q+E)+D) tick)))
      (compactTopConfigCost d W a D q E Rv aT K oS) := by
  have hsub : ∀ i : Fin 32, i∈[2,3,4,7,8,9,10,11,12,13,14,17,22,23] →
      i∈[1,2,3,4,5,7,8,9,10,11,12,13,14,17,22,23] := by decide
  exact sg_compactTopConfigOfRows body R v W a D q E Rv (compactTopRows d Rv a) aT K oS
    (compactTopConfigRowsCost d a Rv) compactTopConfigRows ha hE hRows hoS hq haT hKq
    (hz 1 (by simp)) (hz 2 (by simp)) (hz 5 (by simp)) (hz 7 (by simp)) hcf hw2 hW hD
    (sg_compactTopConfigRows body R v d a Rv hd hdv (by simp [ha]) hRows
      (fun i hi => hz i (hsub i hi)))

end
end IntegerMultBounds.MathlibTM2.Fast
