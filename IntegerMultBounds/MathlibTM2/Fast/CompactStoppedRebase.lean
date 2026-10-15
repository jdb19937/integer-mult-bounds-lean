module

public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedPower

/-! Actual unary cutoff rebasing, with charged work and complete wire frame. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}
variable (body : P → Pr P (nT SXReg) Q A U) {R : Fin (nT SXReg) → List (Fin (A+4))}

/-- Cutoff on s22; depth on s14, leaf count on s18, depth power on s13.
The cutoff and all other wires are restored; s12, s23, s2, s3 are scratch. -/
def compactStoppedRebase : Pr P (nT SXReg) Q A U :=
  .seq (ucopy (sreg (.s 14)) (sreg (.s 12)) (sreg (.s 2))) <|
  .seq (usub (sreg (.s 22)) (sreg (.s 14)) (sreg (.s 2))) <|
  .seq (usub (sreg (.s 14)) (sreg (.s 12)) (sreg (.s 2))) <|
  .seq compactStoppedLeafPow <|
  .seq (uclear (sreg (.s 13))) <|
  .seq (synPush (sreg (.s 13)) tick) <|
  .seq compactStoppedDepthPow (uclear (sreg (.s 12)))

def compactStoppedPowCost (n y : ℕ) : ℕ :=
  (∑ i ∈ Finset.range n,(8*(m^i*y)+8+3))+2*n+4

def compactStoppedRebaseCost (cutoff j u : ℕ) : ℕ :=
  (4*j+4)+(4*cutoff+4)+(4*(j-cutoff)+4)+
    compactStoppedPowCost (min j cutoff) u+(2*m^j+2)+1+
    compactStoppedPowCost (j-cutoff) 1+(2*min j cutoff+2)

theorem sg_compactStoppedRebase (v : SynW → List (Fin (A+4))) (cutoff j u : ℕ)
    (hj : v (.s 14)=List.replicate j tick) (hu : v (.s 18)=List.replicate u tick)
    (hp : v (.s 13)=List.replicate (m^j) tick) (hc : (v (.s 22)).length=cutoff)
    (h12 : v (.s 12)=[]) (h23 : v (.s 23)=[]) (h2 : v (.s 2)=[]) (h3 : v (.s 3)=[]) :
    LayRuns body compactStoppedRebase (synG R v)
      (synG R (Function.update (Function.update (Function.update v (.s 14)
        (List.replicate (j-cutoff) tick)) (.s 18)
        (List.replicate (u*m^(min j cutoff)) tick)) (.s 13)
        (List.replicate (m^(j-cutoff)) tick))) (compactStoppedRebaseCost cutoff j u) := by
  have he : j-(j-cutoff)=min j cutoff := by omega
  refine lr_weaken body
    ((sgU_copy body (a:=.s 14) (b:=.s 12) (t:=.s 2) (x:=j) (y:=0)
      (by decide) (by decide) (by decide) h2 (by simp [hj]) (by simpa using h12)).seq <|
    (sgU_sub body (a:=.s 22) (b:=.s 14) (t:=.s 2) (x:=cutoff) (y:=j)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hc]) (by simp [hj])).seq <|
    (sgU_sub body (a:=.s 14) (b:=.s 12) (t:=.s 2) (x:=j-cutoff) (y:=j)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp) (by simp)).seq <|
    (sg_compactStoppedLeafPow body _ (min j cutoff) u
      (by simp [he]) (by simp [h23]) (by simp [hu]) (by simp [h2]) (by simp [h3])).seq <|
    (sgU_clear body (a:=.s 13) (x:=m^j) (by simp [hp])).seq <|
    (sgU_push body (a:=.s 13) (y:=0) (by simp)).seq <|
    (sg_compactStoppedDepthPow body _ (j-cutoff) 1
      (by simp) (by simp [h23]) (by simp) (by simp [h2]) (by simp [h3])).seq <|
    sgU_clear body (a:=.s 12) (x:=min j cutoff) (by simp [he])) ?_ ?_
  · apply congrArg (synG R)
    funext z
    simp only [Function.update_apply]
    split_ifs <;> simp_all [Nat.mul_comm]
  · simp only [compactStoppedRebaseCost,compactStoppedPowCost]
    omega

end
end IntegerMultBounds.MathlibTM2.Fast
