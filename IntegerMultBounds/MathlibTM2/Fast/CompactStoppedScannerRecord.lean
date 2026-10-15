module

public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedRecord

/-!
# Stopped-piece records with the live digit-scanner frame preserved

Save arbitrary quotient and prefix lists from s12/s23 by reversible moves, and
save the unary power/depth from s13/s14 by copies. The record call uses its
supplied cutoff on s22; restore all four scanner wires afterwards. Only s18,
the offset, the accumulated exponent and the record output change. Registers
s27/s28 remain live and untouched. This is a piece-call wrapper, not a complete
stopped scanner or a cutoff-computation program.
-/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}
variable (body : P → Pr P (nT SXReg) Q A U) {R : Fin (nT SXReg) → List (Fin (A+4))}

/-- Four saves, the stopped record call, and six restoring operations. -/
def compactStoppedScannerRecord (G F : ℕ) : Pr P (nT SXReg) Q A U :=
  .seq (moveR (sreg (.s 12)) (sreg (.s 29)) id) <|
  .seq (moveR (sreg (.s 23)) (sreg (.s 30)) id) <|
  .seq (ucopy (sreg (.s 13)) (sreg (.s 31)) (sreg (.s 2))) <|
  .seq (ucopy (sreg (.s 14)) (sreg (.s 24)) (sreg (.s 2))) <|
  .seq (compactStoppedRecord G F) <|
  .seq (uclear (sreg (.s 13))) <|
  .seq (uclear (sreg (.s 14))) <|
  .seq (moveR (sreg (.s 31)) (sreg (.s 13)) id) <|
  .seq (moveR (sreg (.s 24)) (sreg (.s 14)) id) <|
  .seq (moveR (sreg (.s 29)) (sreg (.s 12)) id)
    (moveR (sreg (.s 30)) (sreg (.s 23)) id)

def compactStoppedScannerRecordCost (G F K cutoff j u a quotientLen prefixLen : ℕ) : ℕ :=
  compactStoppedRecordCost G F K cutoff j u a +
    4*quotientLen + 4*prefixLen + 6*m^j + 6*j +
    2*m^(j-cutoff) + 2*(j-cutoff) + 24

/-- Charged full-frame execution: arbitrary live s12/s23 lists are restored by
 double reversal; the original unary power/depth and every scratch wire return
unchanged. The leaf digit is rebased and the stopped record is emitted. -/
theorem sg_compactStoppedScannerRecord (G F : ℕ) (v : SynW → List (Fin (A+4)))
    (cutoff K j u a E : ℕ) (pr : List (Fin (A+4)))
    (hj : v (.s 14)=List.replicate j tick) (hu : v (.s 18)=List.replicate u tick)
    (hp : v (.s 13)=List.replicate (m^j) tick) (hc : (v (.s 22)).length=cutoff)
    (ha : v (.s 15)=List.replicate a tick) (he : v (.s 16)=List.replicate E tick)
    (hpr : v (.p .pr)=pr) (hK : (v (.p .K)).length=K)
    (h2 : v (.s 2)=[]) (h3 : v (.s 3)=[]) (h4 : v (.s 4)=[])
    (h19 : v (.s 19)=[]) (h20 : v (.s 20)=[]) (h21 : v (.s 21)=[])
    (h24 : v (.s 24)=[]) (h29 : v (.s 29)=[]) (h30 : v (.s 30)=[]) (h31 : v (.s 31)=[]) :
    LayRuns body (compactStoppedScannerRecord G F) (synG R v)
      (synG R (Function.update (Function.update (Function.update (Function.update v
        (.s 18) (List.replicate (u*m^(min j cutoff)) tick))
        (.s 15) (List.replicate (K*bits u j+a) tick))
        (.s 16) (List.replicate (expSeq G F (u*m^(min j cutoff)) (j-cutoff)+E) tick))
        (.p .pr) (topRec [j-cutoff,u*m^(min j cutoff),a,K*bits u j]++pr)))
      (compactStoppedScannerRecordCost G F K cutoff j u a
        (v (.s 12)).length (v (.s 23)).length) := by
  refine lr_weaken body
    ((sg_moveR body (a:=.s 12) (b:=.s 29) (by decide)).seq <|
    (sg_moveR body (a:=.s 23) (b:=.s 30) (by decide)).seq <|
    (sgU_copy body (a:=.s 13) (b:=.s 31) (t:=.s 2) (x:=m^j) (y:=0)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hp]) (by simpa using h31)).seq <|
    (sgU_copy body (a:=.s 14) (b:=.s 24) (t:=.s 2) (x:=j) (y:=0)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hj]) (by simpa using h24)).seq <|
    (sg_compactStoppedRecord body G F _ cutoff K j u a E pr
      (by simp [hj]) (by simp [hu]) (by simp [hp]) (by simp [hc])
      (by simp [ha]) (by simp [he]) (by simp [hpr]) (by simp [hK])
      (by simp) (by simp) (by simp [h2]) (by simp [h3]) (by simp [h4])
      (by simp [h19]) (by simp [h20]) (by simp [h21])).seq <|
    (sgU_clear body (a:=.s 13) (x:=m^(j-cutoff)) (by simp)).seq <|
    (sgU_clear body (a:=.s 14) (x:=j-cutoff) (by simp)).seq <|
    (sgU_move body (a:=.s 31) (b:=.s 13) (x:=m^j)
      (by decide) (by simp) (by simp)).seq <|
    (sgU_move body (a:=.s 24) (b:=.s 14) (x:=j)
      (by decide) (by simp) (by simp)).seq <|
    (sg_moveR body (a:=.s 29) (b:=.s 12) (by decide)).seq <|
    sg_moveR body (a:=.s 30) (b:=.s 23) (by decide)) ?_ ?_
  · apply congrArg (synG R)
    funext z
    by_cases hz12 : z = .s 12
    · subst z
      simp [h29, h30]
    by_cases hz23 : z = .s 23
    · subst z
      simp [h29, h30]
    by_cases hz13 : z = .s 13
    · subst z
      simp [h29, h30, hp]
    by_cases hz14 : z = .s 14
    · subst z
      simp [h29, h30, hj]
    by_cases hz24 : z = .s 24
    · subst z
      simp [h29, h30, h24]
    by_cases hz29 : z = .s 29
    · subst z
      simp [h29, h30]
    by_cases hz30 : z = .s 30
    · subst z
      simp [h29, h30]
    by_cases hz31 : z = .s 31
    · subst z
      simp [h29, h30, h31]
    simp [Function.update_apply, hz12, hz23, hz13, hz14, hz24, hz29, hz30, hz31, h29, h30]
  · simp only [compactStoppedScannerRecordCost]
    simp [h29,h30]
    omega

end
end IntegerMultBounds.MathlibTM2.Fast
