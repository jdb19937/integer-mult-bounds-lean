module

public import IntegerMultBounds.MathlibTM2.Fast.CompactTopOriginal

/-! Reusable contracts for the existing top adapter at an arbitrary computed
exponent sum. The program and configuration writer are reused unchanged. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open CompactGadgetReservationCapacity
noncomputable section
variable {Q A : ℕ} {U P : Type}

private theorem sg_compactAdapterPark (body : P → Pr P (nT SXReg) Q A U)
    {R : Fin (nT SXReg) → List (Fin (A+4))} {v : SynW → List (Fin (A+4))}
    {a b : SynW} (x : ℕ) (hab : a≠b) (ha : (v a).length=x) (hb : v b=[]) :
    LayRuns body (moveR (sreg a) (sreg b) id) (synG R v)
      (synG R (Function.update (Function.update v a []) b (v a).reverse)) (2*x+2) :=
  lr_weaken body (sg_moveR body hab) (by simp [hb]) (by simp [ha])

theorem sg_compactTopAdapter (body : P → Pr P (nT SXReg) Q A U)
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
  have hp := (sg_compactAdapterPark body (R := R) (v := v) g (by decide : (SynW.s 1)≠.s 15) hg h15).seq <|
    (sg_compactAdapterPark body o (by decide : (SynW.s 7)≠.s 31) (by simp [ho]) (by simp [h31])).seq <|
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
    (sg_compactAdapterPark body g (by decide : (SynW.s 15)≠.s 1) (by simp [vp,hg]) (by simp [vp])).seq <|
    sg_compactAdapterPark body o (by decide : (SynW.s 31)≠.s 7) (by simp [vp,ho]) (by simp [vp]))) ?_ ?_
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


theorem sg_compactTopAdapterFinish (body : P → Pr P (nT SXReg) Q A U)
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
  have hc := sg_compactTopAdapter body R vr rowsSrc hsrc d g W a D q E Rv aT K o
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

end
end IntegerMultBounds.MathlibTM2.Fast
