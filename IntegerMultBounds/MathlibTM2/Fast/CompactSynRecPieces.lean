module

public import IntegerMultBounds.MathlibTM2.Fast.SynRec

/-! # Runtime reserved active-piece records

The existing digit scanner constructs the active pieces at the shifted offset.
A separate level-zero piece processes the back reservation. All inputs are
preserved; the only outputs are the piece record and its total exponent.
-/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

/-- Prepend the back leaf from `s 5 = B`, `s 7 = oS`; add B to the exponent on s16. -/
def compactBackPiece : Pr P (nT SXReg) Q A U :=
  .seq (synMulR (sreg (.p .K)) (sreg (.s 5)) (sreg (.s 13)) (sreg (.s 2)) (sreg (.s 3))) <|
  .seq (synFieldF (sreg (.s 13)) (sreg (.p .pr)) (sreg (.s 2))) <|
  .seq (synFieldF (sreg (.s 7)) (sreg (.p .pr)) (sreg (.s 2))) <|
  .seq (synFieldF (sreg (.s 5)) (sreg (.p .pr)) (sreg (.s 2))) <|
  .seq (synFieldF (sreg (.s 12)) (sreg (.p .pr)) (sreg (.s 2))) <|
  .seq (ucopy (sreg (.s 5)) (sreg (.s 16)) (sreg (.s 2))) (uclear (sreg (.s 13)))

def compactBackPieceCost (K B oS : ℕ) : ℕ :=
  synMulRCost K B+(4*(K*B)+5)+(4*oS+5)+(4*B+5)+5+(4*B+4)+(2*(K*B)+2)

theorem sg_compactBackPiece (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (K B oS E : ℕ) (l : List (Fin (A+4)))
    (hK : (v (.p .K)).length=K) (hB : (v (.s 5)).length=B)
    (ho : (v (.s 7)).length=oS) (hE : v (.s 16)=List.replicate E tick) (hl : v (.p .pr)=l)
    (h2 : v (.s 2)=[]) (h3 : v (.s 3)=[]) (h12 : v (.s 12)=[]) (h13 : v (.s 13)=[]) :
    LayRuns body compactBackPiece (synG R v)
      (synG R (Function.update (Function.update v (.s 16) (List.replicate (B+E) tick))
        (.p .pr) (topRec [0,B,oS,K*B] ++ l))) (compactBackPieceCost K B oS) := by
  refine lr_weaken body
    ((sgU_mulR body (R := R) (v := v) (a := .p .K) (b := .s 5) (c := .s 13)
      (t₁ := .s 2) (t₂ := .s 3) (x := K) (y := B) (z := 0)
      (by decide) h2 h3 hK hB (by simpa using h13)).seq <|
    (sgR_fieldF body (a := .s 13) (b := .p .pr) (t := .s 2) (x := K*B) (l := l)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp) (by simp [hl])).seq <|
    (sgR_fieldF body (a := .s 7) (b := .p .pr) (t := .s 2) (x := oS) (l := List.replicate (K*B) tick ++ topSep :: l)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [ho]) (by simp)).seq <|
    (sgR_fieldF body (a := .s 5) (b := .p .pr) (t := .s 2) (x := B) (l := List.replicate oS tick ++ topSep :: (List.replicate (K*B) tick ++ topSep :: l))
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hB]) (by simp)).seq <|
    (sgR_fieldF body (a := .s 12) (b := .p .pr) (t := .s 2) (x := 0) (l := List.replicate B tick ++ topSep :: (List.replicate oS tick ++ topSep :: (List.replicate (K*B) tick ++ topSep :: l)))
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [h12]) (by simp)).seq <|
    (sgU_copy body (a := .s 5) (b := .s 16) (t := .s 2) (x := B) (y := E)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hB]) (by simp [hE])).seq <|
    sgU_clear body (a := .s 13) (x := K*B) (by simp)) ?_ ?_
  · apply congrArg (synG R)
    funext z
    simp only [Function.update_apply]
    split_ifs <;> simp_all [topRec_cons]
  · simp only [compactBackPieceCost]
    omega

/-- The executable digit construction followed by the optional back-reservation leaf. -/
def compactReservedPieces (G F : ℕ) : Pr P (nT SXReg) Q A U :=
  .seq (synDigits G F) <|
  .seq (uclear (sreg (.s 14)))
    (synIfNE (sreg (.s 5)) compactBackPiece synSkip)

noncomputable def compactReservedPcs (K a oS B activeOffset J D : ℕ) : List TopPc :=
  (if B=0 then [] else [⟨0,B,rowsAt (2^a) J,oS⟩]) ++ synPcs K a D activeOffset J D

def compactReservedPiecesCost (G F K B oS activeOffset D : ℕ) : ℕ :=
  synDigitsCost G F K activeOffset D+(2*synJ D D+2)+
    (if B=0 then 3 else compactBackPieceCost K B oS+2)

theorem sg_compactReservedPieces (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (G F K a oS B activeOffset J D : ℕ)
    (hK : (v (.p .K)).length=K) (hB : (v (.s 5)).length=B)
    (ho : (v (.s 7)).length=oS) (hactive : v (.s 6)=List.replicate activeOffset tick)
    (hD : (v (.s 26)).length=D) (hpr : v (.p .pr)=[])
    (hs : ∀ i, 12 ≤ i → i ≤ 24 → v (.s i)=[])
    (h2 : v (.s 2)=[]) (h3 : v (.s 3)=[]) (h4 : v (.s 4)=[]) :
    LayRuns body (compactReservedPieces G F) (synG R v)
      (synG R (Function.update (Function.update v (.s 16)
        (List.replicate (B+synE G F D D) tick)) (.p .pr)
        (topRec (topPcRec K (compactReservedPcs K a oS B activeOffset J D)))))
      (compactReservedPiecesCost G F K B oS activeOffset D) := by
  have h12 := hs 12 (by decide) (by decide)
  have h13 := hs 13 (by decide) (by decide)
  have h14 := hs 14 (by decide) (by decide)
  have h16 := hs 16 (by decide) (by decide)
  have hd := sg_synDigits body (R := R) G F v K a activeOffset J D hactive hK hD hpr hs h2 h3 h4
  have hc := sgU_clear body (R := R) (a := .s 14) (x := synJ D D)
    (v := Function.update (Function.update (Function.update v (.s 14)
      (List.replicate (synJ D D) tick)) (.s 16) (List.replicate (synE G F D D) tick))
      (.p .pr) (topRec (topPcRec K (synPcs K a D activeOffset J D)))) (by simp)
  have heq : Function.update (Function.update (Function.update (Function.update v (.s 14)
      (List.replicate (synJ D D) tick)) (.s 16) (List.replicate (synE G F D D) tick))
      (.p .pr) (topRec (topPcRec K (synPcs K a D activeOffset J D)))) (.s 14) [] =
      Function.update (Function.update v (.s 16) (List.replicate (synE G F D D) tick))
      (.p .pr) (topRec (topPcRec K (synPcs K a D activeOffset J D))) := by
    funext z; simp only [Function.update_apply]; split_ifs <;> simp_all
  rw [heq] at hc
  by_cases hb : B=0
  · have hz : v (.s 5)=[] := List.eq_nil_of_length_eq_zero (hB.trans hb)
    have he := sg_ifNE_neg body (x := .s 5) (p := compactBackPiece) (by simp [hz]) (sg_skip body (R := R)
      (v := Function.update (Function.update v (.s 16) (List.replicate (synE G F D D) tick))
        (.p .pr) (topRec (topPcRec K (synPcs K a D activeOffset J D)))))
    simpa [compactReservedPieces,compactReservedPiecesCost,compactReservedPcs,hb,Nat.add_assoc] using hd.seq (hc.seq he)
  · have hn : v (.s 5)≠[] := by intro hh; simp [hh] at hB; exact hb hB.symm
    have he := sg_ifNE_pos body (x := .s 5) (q := synSkip) (by simp [hn])
      (sg_compactBackPiece body R (Function.update (Function.update v (.s 16) (List.replicate (synE G F D D) tick)) (.p .pr) (topRec (topPcRec K (synPcs K a D activeOffset J D)))) K B oS (synE G F D D) (topRec (topPcRec K (synPcs K a D activeOffset J D)))
        (by simp [hK]) (by simp [hB]) (by simp [ho]) (by simp) (by simp)
        (by simp [h2]) (by simp [h3]) (by simp [h12]) (by simp [h13]))
    refine lr_weaken body (hd.seq (hc.seq he)) ?_ ?_
    · apply congrArg (synG R)
      funext z
      simp only [Function.update_apply]
      split_ifs <;> simp_all [compactReservedPcs,topPcRec,topPcFields,topRec_cons,List.append_assoc,bits]
    · simp only [compactReservedPiecesCost,ite_eq_right hb]
      omega

end
end IntegerMultBounds.MathlibTM2.Fast
