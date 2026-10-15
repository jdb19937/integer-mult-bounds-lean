module

public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedRebase

/-! Executed stopped-piece record generation with a freshly computed exponent. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}
variable (body : P → Pr P (nT SXReg) Q A U) {R : Fin (nT SXReg) → List (Fin (A+4))}

def compactStoppedRecord (G F : ℕ) : Pr P (nT SXReg) Q A U :=
  .seq compactStoppedRebase (synPieceP G F)

def compactStoppedRecordCost (G F K cutoff j u a : ℕ) : ℕ :=
  compactStoppedRebaseCost cutoff j u+
    synPieceCost G F K (u*m^(min j cutoff)) (j-cutoff) a

/-- The cutoff is supplied on s22. The constructor writes the rebased record,
adds its new exponent to s16, advances the offset, and restores every other wire
except the three explicitly rebased parameter wires. -/
theorem sg_compactStoppedRecord (G F : ℕ) (v : SynW → List (Fin (A+4)))
    (cutoff K j u a E : ℕ) (pr : List (Fin (A+4)))
    (hj : v (.s 14)=List.replicate j tick) (hu : v (.s 18)=List.replicate u tick)
    (hp : v (.s 13)=List.replicate (m^j) tick) (hc : (v (.s 22)).length=cutoff)
    (ha : v (.s 15)=List.replicate a tick) (he : v (.s 16)=List.replicate E tick)
    (hpr : v (.p .pr)=pr) (hK : (v (.p .K)).length=K)
    (h12 : v (.s 12)=[]) (h23 : v (.s 23)=[]) (h2 : v (.s 2)=[]) (h3 : v (.s 3)=[])
    (h4 : v (.s 4)=[]) (h19 : v (.s 19)=[]) (h20 : v (.s 20)=[]) (h21 : v (.s 21)=[]) :
    let j' := j-cutoff
    let u' := u*m^(min j cutoff)
    let v' := Function.update (Function.update (Function.update v (.s 14)
      (List.replicate j' tick)) (.s 18) (List.replicate u' tick)) (.s 13)
      (List.replicate (m^j') tick)
    LayRuns body (compactStoppedRecord G F) (synG R v)
      (synG R (Function.update (Function.update (Function.update v' (.s 15)
        (List.replicate (K*bits u j+a) tick)) (.s 16)
        (List.replicate (expSeq G F u' j'+E) tick)) (.p .pr)
        (topRec [j',u',a,K*bits u j]++pr)))
      (compactStoppedRecordCost G F K cutoff j u a) := by
  dsimp only
  have hbits : u*m^(min j cutoff)*m^(j-cutoff)=bits u j := by
    have h := compactStoppedPiece_bits cutoff (⟨j,u,1,a⟩ : TopPc)
    simpa only [compactStoppedPiece,bits_eq_mul,show j-min j cutoff=j-cutoff by omega] using h
  refine lr_weaken body
    ((sg_compactStoppedRebase body v cutoff j u hj hu hp hc h12 h23 h2 h3).seq
      (sg_synPiece body G F _ K (u*m^(min j cutoff)) (j-cutoff) a E pr
        (by simp) (by simp) (by simp) (by simp [ha]) (by simp [he]) (by simp [hpr])
        (by simp [hK]) (by simp [h2]) (by simp [h3]) (by simp [h4])
        (by simp [h19]) (by simp [h20]) (by simp [h21]))) ?_ le_rfl
  simp only [hbits]

end
end IntegerMultBounds.MathlibTM2.Fast
