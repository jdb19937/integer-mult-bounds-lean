module

public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedTopSetup
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopAdapterContract

/-! Original-input compact piece and configuration construction. The outside row
count comes from an explicitly chosen persistent source. Original guard/offset
words are parked and restored literally, without assuming canonical symbols. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open CompactGadgetReservationCapacity
noncomputable section
variable {Q A : ℕ} {U P : Type}

/-- Fixed host program. Outside rows are supplied in a chosen persistent tape;
all derived coordinates, records, padding and precision are computed at runtime. -/
def compactStoppedTopOriginal (ds : Networks.ComplexFramedExecution.Directions) (rowsSrc : SynW) : Pr P (nT SXReg) Q A U :=
  .seq (compactStoppedTopRecordSetup (gateCount (program ds)) (factorCount (program ds))) (compactTopOriginalAdapter rowsSrc)

def compactStoppedTopOriginalCost (ds : Networks.ComplexFramedExecution.Directions) (N d g K D o W Rv : ℕ) : ℕ :=
  let q := CompactGlobalRowPadding.rowAxes NW m d
  let f := frontChunks d g K
  let b := backChunks d g K
  let active := D-q-f-b
  let E := b+((synPcs K 0 active (o+K*b) (CompactGlobalRowPadding.depth m d) active).map (compactStoppedPiece (compactGlobalCutoff D)) |>.map (fun pc => expZ pc.u ds pc.j) |>.sum)
  let a := N-(o+K*(D-q))
  compactStoppedTopRecordSetupCost (gateCount (program ds)) (factorCount (program ds)) N d g K D o+
    compactTopOriginalAdapterCost d g W a D (q+f) E Rv (o+K*(b+active)) K o

/-- From original unary parameters to complete records. Only p.pr, p.cf and
p.w2 change; even noncanonical original guard/offset words are restored literally. -/
theorem sg_compactStoppedTopOriginal (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (rowsSrc : SynW) (hsrc : ∀ i, rowsSrc≠.s i)
    (hsrcpr : rowsSrc≠.p .pr) (_hsrccf : rowsSrc≠.p .cf) (_hsrcw2 : rowsSrc≠.p .w2)
    (ds : Networks.ComplexFramedExecution.Directions) (N d g K D o W Rv : ℕ) (hDpos : 0<D) (hdpos : 0<d) (hk : 1≤K)
    (hN : (v (.p .N)).length=N) (hd : (v (.s 0)).length=d) (hg : (v (.s 1)).length=g)
    (hK : (v (.p .K)).length=K) (hD : (v (.p .D)).length=D) (ho : (v (.s 7)).length=o)
    (hW : (v (.p .w)).length=W) (hRows : (v rowsSrc).length=Rv)
    (hpr : v (.p .pr)=[]) (hcf : v (.p .cf)=[]) (hw2 : v (.p .w2)=[])
    (hs : ∀ i : Fin 32, i≠0 → i≠1 → i≠7 → v (.s i)=[]) :
    let q := CompactGlobalRowPadding.rowAxes NW m d
    let f := frontChunks d g K
    let b := backChunks d g K
    let active := D-q-f-b
    let E := b+((synPcs K 0 active (o+K*b) (CompactGlobalRowPadding.depth m d) active).map (compactStoppedPiece (compactGlobalCutoff D)) |>.map (fun pc => expZ pc.u ds pc.j) |>.sum)
    let a := N-(o+K*(D-q))
    let shift := (D+1)/2+(q+f)+E
    let record := topRec (topPcRec K (compactStoppedReservedPcs K 0 o b (o+K*b)
      (CompactGlobalRowPadding.depth m d) active D))
    LayRuns body (compactStoppedTopOriginal ds rowsSrc) (synG R v)
      (synG R (Function.update (Function.update (Function.update v (.p .pr) record) (.p .cf)
        (topRec (topCfg W shift a Rv (compactTopRows d Rv a) (q+f)
          (o+K*(b+active)) K o D)).reverse)
        (.p .w2) (List.replicate (W+shift+D) tick)))
      (compactStoppedTopOriginalCost ds N d g K D o W Rv) := by
  let q := CompactGlobalRowPadding.rowAxes NW m d
  let f := frontChunks d g K
  let b := backChunks d g K
  let active := D-q-f-b
  exact sg_compactTopAdapterFinish body R v rowsSrc hsrc hsrcpr d g W
    (N-(o+K*(D-q))) D (q+f) (b+((synPcs K 0 active (o+K*b) (CompactGlobalRowPadding.depth m d) active).map (compactStoppedPiece (compactGlobalCutoff D)) |>.map (fun pc => expZ pc.u ds pc.j) |>.sum)) Rv (o+K*(b+active)) K o
    (compactStoppedTopRecordSetupCost (gateCount (program ds)) (factorCount (program ds)) N d g K D o)
    (topRec (topPcRec K (compactStoppedReservedPcs K 0 o b (o+K*b)
      (CompactGlobalRowPadding.depth m d) active D))) (compactStoppedTopRecordSetup (gateCount (program ds)) (factorCount (program ds)))
    hdpos hd hg ho hRows hcf hw2 hW hD hs
    (sg_compactStoppedTopRecordSetup body R v ds N d g K D o hDpos hdpos hk hN hd hg hK hD ho hpr hs)

end
end IntegerMultBounds.MathlibTM2.Fast
