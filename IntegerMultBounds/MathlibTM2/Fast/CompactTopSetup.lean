module

public import IntegerMultBounds.MathlibTM2.Fast.CompactTopCoordinates
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRecRoot

/-! Actual top coordinates from original parameters. Recompute the reservations
cleared by the piece-record builder, derive a,qTop,aT,K*qTop, then clear those
intermediates. The existing exponent and piece-record outputs are preserved. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open CompactGadgetReservationCapacity
noncomputable section
variable {Q A : ℕ} {U P : Type}

def compactTopSetupAfter : Pr P (nT SXReg) Q A U :=
  .seq (compactReserveCounts compactReserveWires) <|
  .seq compactTopCoordinates <|
  .seq (uclear (sreg (.s 8))) <|
  .seq (uclear (sreg (.s 9))) <|
  .seq (uclear (sreg (.s 5))) <|
  .seq (uclear (sreg (.s 26))) (uclear (sreg (.s 6)))

def compactTopSetupAfterCost (N d g K D q o : ℕ) : ℕ :=
  let f := frontChunks d g K
  let b := backChunks d g K
  let active := D-q-f-b
  compactReserveCountsCost d g K D q o+
    (compactTopCoordinatesCost N D K q f b active o+
      ((2*q+2)+((2*f+2)+((2*b+2)+((2*active+2)+(2*(o+K*b)+2))))))

private theorem sg_compactTopSetupAfter (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (N d g K D q o : ℕ) (hk : 1≤K)
    (hN : (v (.p .N)).length=N) (hd : (v (.s 0)).length=d) (hg : (v (.s 1)).length=g)
    (hK : (v (.p .K)).length=K) (hD : (v (.p .D)).length=D)
    (hq : (v (.s 8)).length=q) (ho : (v (.s 7)).length=o)
    (hs : ∀ i : Fin 32, i≠0 → i≠1 → i≠7 → i≠8 → i≠16 → v (.s i)=[]) :
    let f := frontChunks d g K
    let b := backChunks d g K
    let active := D-q-f-b
    LayRuns body compactTopSetupAfter (synG R v)
      (synG R (Function.update (Function.update (Function.update (Function.update
        (Function.update v (.s 8) [])
        (.s 30) (List.replicate (N-(o+K*(D-q))) tick))
        (.s 25) (List.replicate (q+f) tick))
        (.s 28) (List.replicate (o+K*(b+active)) tick))
        (.s 27) (List.replicate (K*(q+f)) tick)))
      (compactTopSetupAfterCost N d g K D q o) := by
  let f := frontChunks d g K
  let b := backChunks d g K
  let active := D-q-f-b
  let offset := o+K*b
  have hc := sg_compactReserveCounts body compactReserveWires compactReserveWires_injective
    R v d g K D q o hk
    (by intro i; fin_cases i <;> simp_all [compactReserveWires])
    (by intro i hi; fin_cases i <;> simp_all [compactReserveWires])
  let v1 := Function.update (Function.update (Function.update (Function.update v
    (.s 9) (List.replicate f tick)) (.s 5) (List.replicate b tick))
    (.s 26) (List.replicate active tick)) (.s 6) (List.replicate offset tick)
  change LayRuns body _ (synG R v) (synG R v1) _ at hc
  have hallowed : ∀ i : Fin 32, i∈[2,3,10,11,12,25,27,28,30] →
      i≠0 ∧ i≠1 ∧ i≠7 ∧ i≠8 ∧ i≠16 ∧ i≠9 ∧ i≠5 ∧ i≠26 ∧ i≠6 := by decide
  have hh := sg_compactTopCoordinates body R v1 N D K q f b active o
    (by simp [v1,hN]) (by simp [v1,hD]) (by simp [v1,hK])
    (by simp [v1,hq]) (by simp [v1]) (by simp [v1]) (by simp [v1]) (by simp [v1,ho])
    (by
      intro i hi
      obtain ⟨h0,h1,h7,h8,h16,h9,h5,h26,h6⟩ := hallowed i hi
      simp [v1,h9,h5,h26,h6,hs i h0 h1 h7 h8 h16])
  refine lr_weaken body (hc.seq (hh.seq <|
    (sgU_clear body (a := .s 8) (x := q) (by simp [v1,hq])).seq <|
    (sgU_clear body (a := .s 9) (x := f) (by simp [v1])).seq <|
    (sgU_clear body (a := .s 5) (x := b) (by simp [v1])).seq <|
    (sgU_clear body (a := .s 26) (x := active) (by simp [v1])).seq <|
    sgU_clear body (a := .s 6) (x := offset) (by simp [v1]))) ?_ (Nat.le_refl _)
  apply congrArg (synG R)
  funext z
  have h5 := hs 5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h6 := hs 6 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h9 := hs 9 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h26 := hs 26 (by decide) (by decide) (by decide) (by decide) (by decide)
  by_cases hz8 : z=.s 8
  · subst z; simp [v1,f,b,active,offset]
  by_cases hz9 : z=.s 9
  · subst z; simp [v1,f,b,active,offset,h9]
  by_cases hz5 : z=.s 5
  · subst z; simp [v1,f,b,active,offset,h5]
  by_cases hz26 : z=.s 26
  · subst z; simp [v1,f,b,active,offset,h26]
  by_cases hz6 : z=.s 6
  · subst z; simp [v1,f,b,active,offset,h6]
  by_cases hz30 : z=.s 30
  · subst z; simp [v1,f,b,active,offset]
  by_cases hz25 : z=.s 25
  · subst z; simp [v1,f,b,active,offset]
  by_cases hz28 : z=.s 28
  · subst z; simp [v1,f,b,active,offset]
  by_cases hz27 : z=.s 27
  · subst z; simp [v1,f,b,active,offset]
  simp [v1,Function.update_of_ne,hz8,hz9,hz5,hz26,hz6,hz30,hz25,hz28,hz27]

def compactTopSetup : Pr P (nT SXReg) Q A U :=
  .seq compactRowReserve compactTopSetupAfter

def compactTopSetupCost (N d g K D o : ℕ) : ℕ :=
  compactRowReserveCost d+
    compactTopSetupAfterCost N d g K D (CompactGlobalRowPadding.rowAxes NW m d) o

private theorem sg_compactTopSetupOfRows (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (N d g K D q o rowCost : ℕ) (rowProg : Pr P (nT SXReg) Q A U) (hk : 1≤K)
    (hN : (v (.p .N)).length=N) (hd : (v (.s 0)).length=d) (hg : (v (.s 1)).length=g)
    (hK : (v (.p .K)).length=K) (hD : (v (.p .D)).length=D) (ho : (v (.s 7)).length=o)
    (hs : ∀ i : Fin 32, i≠0 → i≠1 → i≠7 → i≠16 → v (.s i)=[])
    (hr : LayRuns body rowProg (synG R v)
      (synG R (Function.update v (.s 8) (List.replicate q tick))) rowCost) :
    let f := frontChunks d g K
    let b := backChunks d g K
    let active := D-q-f-b
    LayRuns body (.seq rowProg compactTopSetupAfter) (synG R v)
      (synG R (Function.update (Function.update (Function.update (Function.update v
        (.s 30) (List.replicate (N-(o+K*(D-q))) tick))
        (.s 25) (List.replicate (q+f) tick))
        (.s 28) (List.replicate (o+K*(b+active)) tick))
        (.s 27) (List.replicate (K*(q+f)) tick)))
      (rowCost+compactTopSetupAfterCost N d g K D q o) := by
  have hh := sg_compactTopSetupAfter body R
    (Function.update v (.s 8) (List.replicate q tick)) N d g K D q o hk
    (by simp [hN]) (by simp [hd]) (by simp [hg]) (by simp [hK]) (by simp [hD])
    (by simp) (by simp [ho])
    (by intro i h0 h1 h7 h8 h16; simp [h8,hs i h0 h1 h7 h16])
  refine lr_weaken body (hr.seq hh) ?_ (Nat.le_refl _)
  have h8 := hs 8 (by decide) (by decide) (by decide) (by decide)
  have hv : Function.update v (.s 8) [] = v := by rw [← h8]; exact Function.update_eq_self _ _
  simp only [Function.update_idem,hv]

/-- Original d,g,K,D,N,o suffice. In particular the active count cleared by
compactSynRoot is recomputed, not required as an oracle input. -/
theorem sg_compactTopSetup (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (N d g K D o : ℕ) (hdpos : 0<d) (hk : 1≤K)
    (hN : (v (.p .N)).length=N) (hd : (v (.s 0)).length=d) (hg : (v (.s 1)).length=g)
    (hK : (v (.p .K)).length=K) (hD : (v (.p .D)).length=D) (ho : (v (.s 7)).length=o)
    (hs : ∀ i : Fin 32, i≠0 → i≠1 → i≠7 → i≠16 → v (.s i)=[]) :
    let q := CompactGlobalRowPadding.rowAxes NW m d
    let f := frontChunks d g K
    let b := backChunks d g K
    let active := D-q-f-b
    LayRuns body compactTopSetup (synG R v)
      (synG R (Function.update (Function.update (Function.update (Function.update v
        (.s 30) (List.replicate (N-(o+K*(D-q))) tick))
        (.s 25) (List.replicate (q+f) tick))
        (.s 28) (List.replicate (o+K*(b+active)) tick))
        (.s 27) (List.replicate (K*(q+f)) tick)))
      (compactTopSetupCost N d g K D o) := by
  exact sg_compactTopSetupOfRows body R v N d g K D
    (CompactGlobalRowPadding.rowAxes NW m d) o (compactRowReserveCost d) compactRowReserve
    hk hN hd hg hK hD ho hs
    (sg_compactRowReserve body R v d hdpos hd
      (by intro i hi; apply hs i <;> intro hh <;> subst i <;> simp at hi))


/-- Piece records and every top coordinate, starting from the original parameters.
The cleared reservation counts are deliberately recomputed by the second stage. -/
def compactTopRecordSetup (G F : ℕ) : Pr P (nT SXReg) Q A U :=
  .seq (compactSynRoot G F) compactTopSetup

def compactTopRecordSetupCost (G F N d g K D o : ℕ) : ℕ :=
  compactSynRootCost G F d g K D o+compactTopSetupCost N d g K D o

theorem sg_compactTopRecordSetup (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (G F N d g K D o : ℕ) (hdpos : 0<d) (hk : 1≤K)
    (hN : (v (.p .N)).length=N) (hd : (v (.s 0)).length=d) (hg : (v (.s 1)).length=g)
    (hK : (v (.p .K)).length=K) (hD : (v (.p .D)).length=D) (ho : (v (.s 7)).length=o)
    (hpr : v (.p .pr)=[]) (hs : ∀ i : Fin 32, i≠0 → i≠1 → i≠7 → v (.s i)=[]) :
    let q := CompactGlobalRowPadding.rowAxes NW m d
    let f := frontChunks d g K
    let b := backChunks d g K
    let active := D-q-f-b
    let vr := Function.update (Function.update v (.s 16)
      (List.replicate (b+synE G F active active) tick)) (.p .pr)
      (topRec (topPcRec K (compactReservedPcs K 0 o b (o+K*b)
        (CompactGlobalRowPadding.depth m d) active)))
    LayRuns body (compactTopRecordSetup G F) (synG R v)
      (synG R (Function.update (Function.update (Function.update (Function.update vr
        (.s 30) (List.replicate (N-(o+K*(D-q))) tick))
        (.s 25) (List.replicate (q+f) tick))
        (.s 28) (List.replicate (o+K*(b+active)) tick))
        (.s 27) (List.replicate (K*(q+f)) tick)))
      (compactTopRecordSetupCost G F N d g K D o) := by
  have hr := sg_compactSynRoot body R v G F d g K D o 0
    (CompactGlobalRowPadding.depth m d) hdpos hk hd hg hK hD ho hpr hs
  exact hr.seq (sg_compactTopSetup body R _ N d g K D o hdpos hk
    (by simp [hN]) (by simp [hd]) (by simp [hg]) (by simp [hK]) (by simp [hD])
    (by simp [ho]) (by intro i h0 h1 h7 h16; simp [h16,hs i h0 h1 h7]))

end
end IntegerMultBounds.MathlibTM2.Fast
