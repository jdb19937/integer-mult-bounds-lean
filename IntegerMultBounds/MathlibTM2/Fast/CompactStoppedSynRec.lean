module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRec
public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedReservedPieces

/-! # Executable compact root piece-record construction

The original global axis count, guard, chunk width, selected count, reserved row
count and low offset determine the front/back reservation and active pieces at
runtime. Only the piece record and exponent sum remain; derived counters and
all scratch registers are cleared. The separate row classifier supplies q0.
-/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open CompactGadgetReservationCapacity
noncomputable section
variable {Q A : ℕ} {U P : Type}

def compactStoppedSynRec (G F : ℕ) : Pr P (nT SXReg) Q A U :=
  .seq (compactReserveCounts compactReserveWires) <|
  .seq (compactStoppedReservedPieces G F) <|
  .seq (uclear (sreg (.s 5))) <|
  .seq (uclear (sreg (.s 6))) <|
  .seq (uclear (sreg (.s 9))) (uclear (sreg (.s 26)))

def compactStoppedSynRecCost (G F d g k D q o : ℕ) : ℕ :=
  let f := frontChunks d g k
  let b := backChunks d g k
  let active := D-q-f-b
  let offset := o+k*b
  compactReserveCountsCost d g k D q o+
    compactStoppedReservedPiecesCost G F k b o offset active D+
    (2*b+2)+(2*offset+2)+(2*f+2)+(2*active+2)

theorem sg_compactStoppedSynRec (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (ds : Networks.ComplexFramedExecution.Directions) (d g k D q o a J : ℕ)
    (hDpos : 0 < D) (hk : 1≤k)
    (hd : (v (.s 0)).length=d) (hg : (v (.s 1)).length=g)
    (hK : (v (.p .K)).length=k) (hD : (v (.p .D)).length=D)
    (hq : (v (.s 8)).length=q) (ho : (v (.s 7)).length=o)
    (hpr : v (.p .pr)=[]) (hs : ∀ i : Fin 32, i≠0 → i≠1 → i≠7 → i≠8 → v (.s i)=[]) :
    let f := frontChunks d g k
    let b := backChunks d g k
    let active := D-q-f-b
    let offset := o+k*b
    LayRuns body (compactStoppedSynRec (gateCount (program ds)) (factorCount (program ds))) (synG R v)
      (synG R (Function.update (Function.update v (.s 16)
        (List.replicate (b+((synPcs k a active offset J active).map (compactStoppedPiece (compactGlobalCutoff D)) |>.map (fun pc => expZ pc.u ds pc.j) |>.sum)) tick)) (.p .pr)
        (topRec (topPcRec k (compactStoppedReservedPcs k a o b offset J active D)))))
      (compactStoppedSynRecCost (gateCount (program ds)) (factorCount (program ds)) d g k D q o) := by
  let f := frontChunks d g k
  let b := backChunks d g k
  let active := D-q-f-b
  let offset := o+k*b
  have hz (i : Fin 32) (h0 : i≠0) (h1 : i≠1) (h7 : i≠7) (h8 : i≠8) := hs i h0 h1 h7 h8
  have hc := sg_compactReserveCounts body compactReserveWires compactReserveWires_injective
    R v d g k D q o hk
    (by intro i; fin_cases i <;> simp_all [compactReserveWires])
    (by intro i hi; fin_cases i <;> simp_all [compactReserveWires])
  change LayRuns body _ (synG R v)
    (synG R (Function.update (Function.update (Function.update (Function.update v
      (.s 9) (List.replicate f tick)) (.s 5) (List.replicate b tick))
      (.s 26) (List.replicate active tick)) (.s 6) (List.replicate offset tick))) _ at hc
  let v1 := Function.update (Function.update (Function.update (Function.update v
      (.s 9) (List.replicate f tick)) (.s 5) (List.replicate b tick))
      (.s 26) (List.replicate active tick)) (.s 6) (List.replicate offset tick)
  have hp := sg_compactStoppedReservedPieces body R v1 ds k a o b offset J active D hDpos
    (by simp [v1,hD])
    (by simp [v1,hK]) (by simp [v1]) (by simp [v1,ho]) (by simp [v1]) (by simp [v1])
    (by simp [v1,hpr])
    (by intro i hi hj; simp [v1,hs i (by omega) (by omega) (by omega) (by omega),
      show i≠5 by omega,show i≠6 by omega,show i≠9 by omega,show i≠26 by omega])
    (by simp [v1,hs]) (by simp [v1,hs]) (by simp [v1,hs])
    (by simp [v1,hs]) (by simp [v1,hs]) (by simp [v1,hs])
  refine lr_weaken body (hc.seq (hp.seq <|
    (sgU_clear body (a := .s 5) (x := b) (by simp [v1])).seq <|
    (sgU_clear body (a := .s 6) (x := offset) (by simp [v1])).seq <|
    (sgU_clear body (a := .s 9) (x := f) (by simp [v1])).seq <|
    sgU_clear body (a := .s 26) (x := active) (by simp [v1]))) ?_ ?_
  · apply congrArg (synG R)
    funext z
    simp only [v1,Function.update_apply]
    split_ifs <;> simp_all [f,b,active,offset]
  · simp only [compactStoppedSynRecCost]
    dsimp [f,b,active,offset]
    omega

end
end IntegerMultBounds.MathlibTM2.Fast
