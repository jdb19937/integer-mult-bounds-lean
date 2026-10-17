module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRecPieces
public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedGlobalPipeline

/-! Actual reserved-piece builder with global-dimension stopping for active digits.
The independent back-reservation leaf and its exponent contribution remain intact. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

/-- The executable digit construction followed by the optional back-reservation leaf. -/
def compactStoppedReservedPieces (G F : ℕ) : Pr P (nT SXReg) Q A U :=
  .seq (compactStoppedGlobalPipeline G F) <|
  .seq (uclear (sreg (.s 14)))
    (synIfNE (sreg (.s 5)) compactBackPiece synSkip)

noncomputable def compactStoppedReservedPcs (K a oS B activeOffset J D globalD : ℕ) : List TopPc :=
  (if B=0 then [] else [⟨0,B,rowsAt (2^a) J,oS⟩]) ++ (synPcs K a D activeOffset J D).map (compactStoppedPiece (compactGlobalCutoff globalD))

def compactStoppedReservedPiecesCost (G F K B oS activeOffset D globalD : ℕ) : ℕ :=
  compactStoppedGlobalPipelineCost G F K activeOffset D globalD+(2*synJ D D+2)+
    (if B=0 then 3 else compactBackPieceCost K B oS+2)

theorem sg_compactStoppedReservedPieces (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (ds : Networks.ComplexFramedExecution.Directions) (K a oS B activeOffset J D globalD : ℕ)
    (hglobalDpos : 0 < globalD) (hglobalD : (v (.p .D)).length=globalD)
    (hK : (v (.p .K)).length=K) (hB : (v (.s 5)).length=B)
    (ho : (v (.s 7)).length=oS) (hactive : v (.s 6)=List.replicate activeOffset tick)
    (hD : (v (.s 26)).length=D) (hpr : v (.p .pr)=[])
    (hs : ∀ i, 12 ≤ i → i ≤ 24 → v (.s i)=[])
    (h29 : v (.s 29)=[]) (h30 : v (.s 30)=[]) (h31 : v (.s 31)=[])
    (h2 : v (.s 2)=[]) (h3 : v (.s 3)=[]) (h4 : v (.s 4)=[]) :
    LayRuns body (compactStoppedReservedPieces (gateCount (program ds)) (factorCount (program ds))) (synG R v)
      (synG R (Function.update (Function.update v (.s 16)
        (List.replicate (B+((synPcs K a D activeOffset J D).map (compactStoppedPiece (compactGlobalCutoff globalD)) |>.map (fun pc => expZ pc.u ds pc.j) |>.sum)) tick)) (.p .pr)
        (topRec (topPcRec K (compactStoppedReservedPcs K a oS B activeOffset J D globalD)))))
      (compactStoppedReservedPiecesCost (gateCount (program ds)) (factorCount (program ds)) K B oS activeOffset D globalD) := by
  have h12 := hs 12 (by decide) (by decide)
  have h13 := hs 13 (by decide) (by decide)
  have h14 := hs 14 (by decide) (by decide)
  have h16 := hs 16 (by decide) (by decide)
  have hd := sg_compactStoppedGlobalPipeline body (R := R) ds v K a activeOffset J D globalD
    hglobalDpos hglobalD hactive hK hD hpr hs h29 h30 h31 h2 h3 h4
  have hc := sgU_clear body (R := R) (a := .s 14) (x := synJ D D)
    (v := Function.update (Function.update (Function.update v (.s 14)
      (List.replicate (synJ D D) tick)) (.s 16) (List.replicate (((synPcs K a D activeOffset J D).map (compactStoppedPiece (compactGlobalCutoff globalD)) |>.map (fun pc => expZ pc.u ds pc.j) |>.sum)) tick))
      (.p .pr) (topRec (topPcRec K ((synPcs K a D activeOffset J D).map (compactStoppedPiece (compactGlobalCutoff globalD)))))) (by simp)
  have heq : Function.update (Function.update (Function.update (Function.update v (.s 14)
      (List.replicate (synJ D D) tick)) (.s 16) (List.replicate (((synPcs K a D activeOffset J D).map (compactStoppedPiece (compactGlobalCutoff globalD)) |>.map (fun pc => expZ pc.u ds pc.j) |>.sum)) tick))
      (.p .pr) (topRec (topPcRec K ((synPcs K a D activeOffset J D).map (compactStoppedPiece (compactGlobalCutoff globalD)))))) (.s 14) [] =
      Function.update (Function.update v (.s 16) (List.replicate (((synPcs K a D activeOffset J D).map (compactStoppedPiece (compactGlobalCutoff globalD)) |>.map (fun pc => expZ pc.u ds pc.j) |>.sum)) tick))
      (.p .pr) (topRec (topPcRec K ((synPcs K a D activeOffset J D).map (compactStoppedPiece (compactGlobalCutoff globalD))))) := by
    funext z; simp only [Function.update_apply]; split_ifs <;> simp_all
  rw [heq] at hc
  by_cases hb : B=0
  · have hz : v (.s 5)=[] := List.eq_nil_of_length_eq_zero (hB.trans hb)
    have he := sg_ifNE_neg body (x := .s 5) (p := compactBackPiece) (by simp [hz]) (sg_skip body (R := R)
      (v := Function.update (Function.update v (.s 16) (List.replicate (((synPcs K a D activeOffset J D).map (compactStoppedPiece (compactGlobalCutoff globalD)) |>.map (fun pc => expZ pc.u ds pc.j) |>.sum)) tick))
        (.p .pr) (topRec (topPcRec K ((synPcs K a D activeOffset J D).map (compactStoppedPiece (compactGlobalCutoff globalD)))))))
    simpa [compactStoppedReservedPieces,compactStoppedReservedPiecesCost,compactStoppedReservedPcs,hb,Nat.add_assoc] using hd.seq (hc.seq he)
  · have hn : v (.s 5)≠[] := by intro hh; simp [hh] at hB; exact hb hB.symm
    have he := sg_ifNE_pos body (x := .s 5) (q := synSkip) (by simp [hn])
      (sg_compactBackPiece body R (Function.update (Function.update v (.s 16) (List.replicate (((synPcs K a D activeOffset J D).map (compactStoppedPiece (compactGlobalCutoff globalD)) |>.map (fun pc => expZ pc.u ds pc.j) |>.sum)) tick)) (.p .pr) (topRec (topPcRec K ((synPcs K a D activeOffset J D).map (compactStoppedPiece (compactGlobalCutoff globalD)))))) K B oS (((synPcs K a D activeOffset J D).map (compactStoppedPiece (compactGlobalCutoff globalD)) |>.map (fun pc => expZ pc.u ds pc.j) |>.sum)) (topRec (topPcRec K ((synPcs K a D activeOffset J D).map (compactStoppedPiece (compactGlobalCutoff globalD)))))
        (by simp [hK]) (by simp [hB]) (by simp [ho]) (by simp) (by simp)
        (by simp [h2]) (by simp [h3]) (by simp [h12]) (by simp [h13]))
    refine lr_weaken body (hd.seq (hc.seq he)) ?_ ?_
    · apply congrArg (synG R)
      funext z
      simp only [Function.update_apply]
      split_ifs <;> simp_all [compactStoppedReservedPcs,topPcRec,topPcFields,topRec_cons,List.append_assoc,bits]
    · simp only [compactStoppedReservedPiecesCost,ite_eq_right hb]
      omega

end
end IntegerMultBounds.MathlibTM2.Fast
