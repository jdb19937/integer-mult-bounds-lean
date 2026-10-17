module

public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedTopOriginal
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopPlaced

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

def compactStoppedTopPlaced (ds : Networks.ComplexFramedExecution.Directions)
    (rowsSrc : SynW) : Pr P (nT CompactHostBReg) Q A U :=
  embProg compactLegacyReg (fun f : Empty => f.elim)
    (compactStoppedTopOriginal (P:=Empty) ds rowsSrc)

theorem compactStoppedTopPlaced_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
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
    CompactPlacedRuns body (compactStoppedTopPlaced ds rowsSrc) (synG R v)
      (synG R (Function.update (Function.update (Function.update v (.p .pr) record) (.p .cf)
        (topRec (topCfg W shift a Rv (compactTopRows d Rv a) (q+f)
          (o+K*(b+active)) K o D)).reverse)
        (.p .w2) (List.replicate (W+shift+D) tick)))
      (compactStoppedTopOriginalCost ds N d g K D o W Rv) := by
  dsimp only
  intro vbig S hL hR
  exact compactEmptySetup_exec compactLegacyReg compactLegacyReg_injective body
    (sg_compactStoppedTopOriginal (fun f : Empty => f.elim) R v rowsSrc hsrc hsrcpr _hsrccf _hsrcw2
      ds N d g K D o W Rv hDpos hdpos hk hN hd hg hK hD ho hW hRows hpr hcf hw2 hs)
    vbig S hL hR

end
end IntegerMultBounds.MathlibTM2.Fast
