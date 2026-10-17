module

public import IntegerMultBounds.MathlibTM2.Fast.CompactTopSetup
public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedSynRoot

/-! The stopped root constructor followed by the existing coordinate setup.
The fresh exponent sum and stopped records survive coordinate computation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open CompactGadgetReservationCapacity
noncomputable section
variable {Q A : ℕ} {U P : Type}

def compactStoppedTopRecordSetup (G F : ℕ) : Pr P (nT SXReg) Q A U :=
  .seq (compactStoppedSynRoot G F) compactTopSetup

def compactStoppedTopRecordSetupCost (G F N d g K D o : ℕ) : ℕ :=
  compactStoppedSynRootCost G F d g K D o+compactTopSetupCost N d g K D o

theorem sg_compactStoppedTopRecordSetup (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (ds : Networks.ComplexFramedExecution.Directions) (N d g K D o : ℕ) (hDpos : 0<D) (hdpos : 0<d) (hk : 1≤K)
    (hN : (v (.p .N)).length=N) (hd : (v (.s 0)).length=d) (hg : (v (.s 1)).length=g)
    (hK : (v (.p .K)).length=K) (hD : (v (.p .D)).length=D) (ho : (v (.s 7)).length=o)
    (hpr : v (.p .pr)=[]) (hs : ∀ i : Fin 32, i≠0 → i≠1 → i≠7 → v (.s i)=[]) :
    let q := CompactGlobalRowPadding.rowAxes NW m d
    let f := frontChunks d g K
    let b := backChunks d g K
    let active := D-q-f-b
    let vr := Function.update (Function.update v (.s 16)
      (List.replicate (b+((synPcs K 0 active (o+K*b) (CompactGlobalRowPadding.depth m d) active).map (compactStoppedPiece (compactGlobalCutoff D)) |>.map (fun pc => expZ pc.u ds pc.j) |>.sum)) tick)) (.p .pr)
      (topRec (topPcRec K (compactStoppedReservedPcs K 0 o b (o+K*b)
        (CompactGlobalRowPadding.depth m d) active D)))
    LayRuns body (compactStoppedTopRecordSetup (gateCount (program ds)) (factorCount (program ds))) (synG R v)
      (synG R (Function.update (Function.update (Function.update (Function.update vr
        (.s 30) (List.replicate (N-(o+K*(D-q))) tick))
        (.s 25) (List.replicate (q+f) tick))
        (.s 28) (List.replicate (o+K*(b+active)) tick))
        (.s 27) (List.replicate (K*(q+f)) tick)))
      (compactStoppedTopRecordSetupCost (gateCount (program ds)) (factorCount (program ds)) N d g K D o) := by
  have hr := sg_compactStoppedSynRoot body R v ds d g K D o 0
    (CompactGlobalRowPadding.depth m d) hDpos hdpos hk hd hg hK hD ho hpr hs
  exact hr.seq (sg_compactTopSetup body R _ N d g K D o hdpos hk
    (by simp [hN]) (by simp [hd]) (by simp [hg]) (by simp [hK]) (by simp [hD])
    (by simp [ho]) (by intro i h0 h1 h7 h16; simp [h16,hs i h0 h1 h7]))

end
end IntegerMultBounds.MathlibTM2.Fast
