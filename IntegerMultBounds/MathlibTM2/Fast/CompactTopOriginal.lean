module

public import IntegerMultBounds.MathlibTM2.Fast.CompactTopSetup
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopConfig
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

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

private theorem sg_compactPark (body : P → Pr P (nT SXReg) Q A U)
    {R : Fin (nT SXReg) → List (Fin (A+4))} {v : SynW → List (Fin (A+4))}
    {a b : SynW} (x : ℕ) (hab : a≠b) (ha : (v a).length=x) (hb : v b=[]) :
    LayRuns body (moveR (sreg a) (sreg b) id) (synG R v)
      (synG R (Function.update (Function.update v a []) b (v a).reverse)) (2*x+2) :=
  lr_weaken body (sg_moveR body hab) (by simp [hb]) (by simp [ha])

def compactTopOriginalPark (rowsSrc : SynW) : Pr P (nT SXReg) Q A U :=
  .seq (moveR (sreg (.s 1)) (sreg (.s 15)) id) <|
  .seq (moveR (sreg (.s 7)) (sreg (.s 31)) id) <|
  .seq (ucopy (sreg (.s 31)) (sreg (.s 6)) (sreg (.s 2))) <|
    (ucopy (sreg rowsSrc) (sreg (.s 29)) (sreg (.s 2)))

def compactTopOriginalAdapter (rowsSrc : SynW) : Pr P (nT SXReg) Q A U :=
  .seq (compactTopOriginalPark rowsSrc) <|
  .seq compactTopConfig <|
  .seq (uclear (sreg (.s 6))) <|
  .seq (uclear (sreg (.s 29))) <|
  .seq (uclear (sreg (.s 25))) <|
  .seq (uclear (sreg (.s 27))) <|
  .seq (uclear (sreg (.s 28))) <|
  .seq (uclear (sreg (.s 30))) <|
  .seq (uclear (sreg (.s 16))) <|
  .seq (moveR (sreg (.s 15)) (sreg (.s 1)) id) (moveR (sreg (.s 31)) (sreg (.s 7)) id)

def compactTopOriginalAdapterCost (d g W a D q E Rv aT K o : ℕ) : ℕ :=
  (2*g+2)+((2*o+2)+((4*o+4)+((4*Rv+4)+
    (compactTopConfigCost d W a D q E Rv aT K o+
      ((2*o+2)+((2*Rv+2)+((2*q+2)+((2*(K*q)+2)+((2*aT+2)+((2*a+2)+
        ((2*E+2)+((2*g+2)+(2*o+2)))))))))))))

theorem sg_compactTopOriginalAdapter (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (rowsSrc : SynW) (hsrc : ∀ i, rowsSrc≠.s i)
    (d g W a D q E Rv aT K o : ℕ) (hdpos : 0<d)
    (hd : (v (.s 0)).length=d) (hg : (v (.s 1)).length=g) (ho : (v (.s 7)).length=o)
    (ha : v (.s 30)=List.replicate a tick) (hE : v (.s 16)=List.replicate E tick)
    (hRows : (v rowsSrc).length=Rv) (hq : v (.s 25)=List.replicate q tick)
    (haT : v (.s 28)=List.replicate aT tick) (hKq : v (.s 27)=List.replicate (K*q) tick)
    (hcf : v (.p .cf)=[]) (hw2 : v (.p .w2)=[])
    (hW : (v (.p .w)).length=W) (hD : (v (.p .D)).length=D)
    (hs : ∀ i : Fin 32, i≠0 → i≠1 → i≠7 → i≠16 → i≠25 → i≠27 → i≠28 → i≠30 → v (.s i)=[]) :
    LayRuns body (compactTopOriginalAdapter rowsSrc) (synG R v)
      (synG R (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update v (.s 16) []) (.s 25) [])
          (.s 27) []) (.s 28) []) (.s 30) []) (.p .cf)
          (topRec (topCfg W ((D+1)/2+q+E) a Rv (compactTopRows d Rv a) q aT K o D)).reverse)
        (.p .w2) (List.replicate (W+((D+1)/2+q+E)+D) tick)))
      (compactTopOriginalAdapterCost d g W a D q E Rv aT K o) := by
  have h2 := hs 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h6 := hs 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h15 := hs 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h29 := hs 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h31 := hs 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  let vp := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update v (.s 1) []) (.s 15) (v (.s 1)).reverse)
      (.s 7) []) (.s 31) (v (.s 7)).reverse) (.s 6) (List.replicate o tick))
      (.s 29) (List.replicate Rv tick)
  have hp := (sg_compactPark body (R := R) (v := v) g (by decide : (SynW.s 1)≠.s 15) hg h15).seq <|
    (sg_compactPark body o (by decide : (SynW.s 7)≠.s 31) (by simp [ho]) (by simp [h31])).seq <|
    (sgU_copy body (a := .s 31) (b := .s 6) (t := .s 2) (x := o) (y := 0)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [ho]) (by simp [h6])).seq <|
    sgU_copy body (a := rowsSrc) (b := .s 29) (t := .s 2) (x := Rv) (y := 0)
      (hsrc 29) (hsrc 2) (by decide) (by simp [h2]) (by simp [hsrc,hRows]) (by simp [h29])
  change LayRuns body _ (synG R v) (synG R vp) _ at hp
  have hc := sg_compactTopConfig body R vp d W a D q E Rv aT K o hdpos
    (by simp [vp,hd]) (by simp [vp,ha]) (by simp [vp,hE]) (by simp [vp]) (by simp [vp])
    (by simp [vp,hq]) (by simp [vp,haT]) (by simp [vp,hKq])
    (by simp [vp,hcf]) (by simp [vp,hw2]) (by simp [vp,hW]) (by simp [vp,hD])
    (by
      intro i hi
      by_cases h7i : i=7
      · subst i; simp [vp]
      by_cases h1i : i=1
      · subst i; simp [vp]
      have htest : ∀ i : Fin 32, i∈[1,2,3,4,5,7,8,9,10,11,12,13,14,17,22,23] →
        i≠0 ∧ i≠16 ∧ i≠25 ∧ i≠27 ∧ i≠28 ∧ i≠30 ∧ i≠15 ∧ i≠31 ∧ i≠6 ∧ i≠29 := by decide
      obtain ⟨h0i,h16i,h25i,h27i,h28i,h30i,h15i,h31i,h6i,h29i⟩ := htest i hi
      simp [vp,h1i,h15i,h7i,h31i,h6i,h29i,hs i h0i h1i h7i h16i h25i h27i h28i h30i])
  refine lr_weaken body (hp.seq (hc.seq <|
    (sgU_clear body (a := .s 6) (x := o) (by simp [vp])).seq <|
    (sgU_clear body (a := .s 29) (x := Rv) (by simp [vp])).seq <|
    (sgU_clear body (a := .s 25) (x := q) (by simp [vp,hq])).seq <|
    (sgU_clear body (a := .s 27) (x := K*q) (by simp [vp,hKq])).seq <|
    (sgU_clear body (a := .s 28) (x := aT) (by simp [vp,haT])).seq <|
    (sgU_clear body (a := .s 30) (x := a) (by simp [vp,ha])).seq <|
    (sgU_clear body (a := .s 16) (x := E) (by simp [vp,hE])).seq <|
    (sg_compactPark body g (by decide : (SynW.s 15)≠.s 1) (by simp [vp,hg]) (by simp [vp])).seq <|
    sg_compactPark body o (by decide : (SynW.s 31)≠.s 7) (by simp [vp,ho]) (by simp [vp]))) ?_ ?_
  · apply congrArg (synG R)
    funext z
    by_cases hz1 : z=.s 1
    · subst z; simp [vp]
    by_cases hz7 : z=.s 7
    · subst z; simp [vp]
    by_cases hz15 : z=.s 15
    · subst z; simp [vp,h15]
    by_cases hz31 : z=.s 31
    · subst z; simp [vp,h31]
    by_cases hz6 : z=.s 6
    · subst z; simp [vp,h6]
    by_cases hz29 : z=.s 29
    · subst z; simp [vp,h29]
    by_cases hz25 : z=.s 25
    · subst z; simp [vp]
    by_cases hz27 : z=.s 27
    · subst z; simp [vp]
    by_cases hz28 : z=.s 28
    · subst z; simp [vp]
    by_cases hz30 : z=.s 30
    · subst z; simp [vp]
    by_cases hz16 : z=.s 16
    · subst z; simp [vp]
    by_cases hzcf : z=.p .cf
    · subst z; simp [vp]
    by_cases hzw2 : z=.p .w2
    · subst z; simp [vp]
    simp [vp,Function.update_of_ne,hz1,hz7,hz15,hz31,hz6,hz29,hz25,hz27,hz28,hz30,hz16,hzcf,hzw2]
  · simp only [compactTopOriginalAdapterCost]
    omega


private theorem sg_compactTopOriginalFinish (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (rowsSrc : SynW) (hsrc : ∀ i, rowsSrc≠.s i) (hsrcpr : rowsSrc≠.p .pr)
    (d g W a D q E Rv aT K o prepCost : ℕ) (record : List (Fin (A+4)))
    (prep : Pr P (nT SXReg) Q A U) (hdpos : 0<d)
    (hd : (v (.s 0)).length=d) (hg : (v (.s 1)).length=g) (ho : (v (.s 7)).length=o)
    (hRows : (v rowsSrc).length=Rv) (hcf : v (.p .cf)=[]) (hw2 : v (.p .w2)=[])
    (hW : (v (.p .w)).length=W) (hD : (v (.p .D)).length=D)
    (hs : ∀ i : Fin 32, i≠0 → i≠1 → i≠7 → v (.s i)=[])
    (hr : LayRuns body prep (synG R v)
      (synG R (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update v (.s 16) (List.replicate E tick)) (.p .pr) record)
        (.s 30) (List.replicate a tick)) (.s 25) (List.replicate q tick))
        (.s 28) (List.replicate aT tick)) (.s 27) (List.replicate (K*q) tick))) prepCost) :
    LayRuns body (.seq prep (compactTopOriginalAdapter rowsSrc)) (synG R v)
      (synG R (Function.update (Function.update (Function.update v (.p .pr) record) (.p .cf)
        (topRec (topCfg W ((D+1)/2+q+E) a Rv (compactTopRows d Rv a) q aT K o D)).reverse)
        (.p .w2) (List.replicate (W+((D+1)/2+q+E)+D) tick)))
      (prepCost+compactTopOriginalAdapterCost d g W a D q E Rv aT K o) := by
  let vr := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update v (.s 16) (List.replicate E tick)) (.p .pr) record)
      (.s 30) (List.replicate a tick)) (.s 25) (List.replicate q tick))
      (.s 28) (List.replicate aT tick)) (.s 27) (List.replicate (K*q) tick)
  have hc := sg_compactTopOriginalAdapter body R vr rowsSrc hsrc d g W a D q E Rv aT K o
    hdpos (by simp [vr,hd]) (by simp [vr,hg]) (by simp [vr,ho])
    (by simp [vr]) (by simp [vr]) (by simp [vr,hsrc,hsrcpr,hRows])
    (by simp [vr]) (by simp [vr]) (by simp [vr])
    (by simp [vr,hcf]) (by simp [vr,hw2]) (by simp [vr,hW]) (by simp [vr,hD])
    (by intro i h0 h1 h7 h16 h25 h27 h28 h30
        simp [vr,h16,h25,h27,h28,h30,hs i h0 h1 h7])
  refine lr_weaken body (hr.seq hc) ?_ (Nat.le_refl _)
  apply congrArg (synG R)
  funext z
  have h16 := hs 16 (by decide) (by decide) (by decide)
  by_cases hz16 : z=.s 16
  · subst z; simp [vr,h16]
  have h25 := hs 25 (by decide) (by decide) (by decide)
  by_cases hz25 : z=.s 25
  · subst z; simp [vr,h25]
  have h27 := hs 27 (by decide) (by decide) (by decide)
  by_cases hz27 : z=.s 27
  · subst z; simp [vr,h27]
  have h28 := hs 28 (by decide) (by decide) (by decide)
  by_cases hz28 : z=.s 28
  · subst z; simp [vr,h28]
  have h30 := hs 30 (by decide) (by decide) (by decide)
  by_cases hz30 : z=.s 30
  · subst z; simp [vr,h30]
  by_cases hzpr : z=.p .pr
  · subst z; simp [vr]
  by_cases hzcf : z=.p .cf
  · subst z; simp [vr]
  by_cases hzw2 : z=.p .w2
  · subst z; simp [vr]
  simp [vr,Function.update_of_ne,hz16,hz25,hz27,hz28,hz30,hzpr,hzcf,hzw2]

/-- Fixed host program. Outside rows are supplied in a chosen persistent tape;
all derived coordinates, records, padding and precision are computed at runtime. -/
def compactTopOriginal (G F : ℕ) (rowsSrc : SynW) : Pr P (nT SXReg) Q A U :=
  .seq (compactTopRecordSetup G F) (compactTopOriginalAdapter rowsSrc)

def compactTopOriginalCost (G F N d g K D o W Rv : ℕ) : ℕ :=
  let q := CompactGlobalRowPadding.rowAxes NW m d
  let f := frontChunks d g K
  let b := backChunks d g K
  let active := D-q-f-b
  let E := b+synE G F active active
  let a := N-(o+K*(D-q))
  compactTopRecordSetupCost G F N d g K D o+
    compactTopOriginalAdapterCost d g W a D (q+f) E Rv (o+K*(b+active)) K o

/-- From original unary parameters to complete records. Only p.pr, p.cf and
p.w2 change; even noncanonical original guard/offset words are restored literally. -/
theorem sg_compactTopOriginal (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (rowsSrc : SynW) (hsrc : ∀ i, rowsSrc≠.s i)
    (hsrcpr : rowsSrc≠.p .pr) (_hsrccf : rowsSrc≠.p .cf) (_hsrcw2 : rowsSrc≠.p .w2)
    (G F N d g K D o W Rv : ℕ) (hdpos : 0<d) (hk : 1≤K)
    (hN : (v (.p .N)).length=N) (hd : (v (.s 0)).length=d) (hg : (v (.s 1)).length=g)
    (hK : (v (.p .K)).length=K) (hD : (v (.p .D)).length=D) (ho : (v (.s 7)).length=o)
    (hW : (v (.p .w)).length=W) (hRows : (v rowsSrc).length=Rv)
    (hpr : v (.p .pr)=[]) (hcf : v (.p .cf)=[]) (hw2 : v (.p .w2)=[])
    (hs : ∀ i : Fin 32, i≠0 → i≠1 → i≠7 → v (.s i)=[]) :
    let q := CompactGlobalRowPadding.rowAxes NW m d
    let f := frontChunks d g K
    let b := backChunks d g K
    let active := D-q-f-b
    let E := b+synE G F active active
    let a := N-(o+K*(D-q))
    let shift := (D+1)/2+(q+f)+E
    let record := topRec (topPcRec K (compactReservedPcs K 0 o b (o+K*b)
      (CompactGlobalRowPadding.depth m d) active))
    LayRuns body (compactTopOriginal G F rowsSrc) (synG R v)
      (synG R (Function.update (Function.update (Function.update v (.p .pr) record) (.p .cf)
        (topRec (topCfg W shift a Rv (compactTopRows d Rv a) (q+f)
          (o+K*(b+active)) K o D)).reverse)
        (.p .w2) (List.replicate (W+shift+D) tick)))
      (compactTopOriginalCost G F N d g K D o W Rv) := by
  let q := CompactGlobalRowPadding.rowAxes NW m d
  let f := frontChunks d g K
  let b := backChunks d g K
  let active := D-q-f-b
  exact sg_compactTopOriginalFinish body R v rowsSrc hsrc hsrcpr d g W
    (N-(o+K*(D-q))) D (q+f) (b+synE G F active active) Rv (o+K*(b+active)) K o
    (compactTopRecordSetupCost G F N d g K D o)
    (topRec (topPcRec K (compactReservedPcs K 0 o b (o+K*b)
      (CompactGlobalRowPadding.depth m d) active))) (compactTopRecordSetup G F)
    hdpos hd hg ho hRows hcf hw2 hW hD hs
    (sg_compactTopRecordSetup body R v G F N d g K D o hdpos hk hN hd hg hK hD ho hpr hs)

end
end IntegerMultBounds.MathlibTM2.Fast
