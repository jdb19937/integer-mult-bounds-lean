module

public import IntegerMultBounds.MathlibTM2.Fast.CompactTopPlaced
public import IntegerMultBounds.MathlibTM2.Node.CompactTopProcR

/-! Original-input construction of the rounded top configuration. The record setup runs with no
factor term, so its exponent sum is the scale sum `E_R` of the rounded pieces. The guard
`g = K + D + 6`, `K = N + l + 2 + (cG + 1) D` (`N` the address bits, `l` the record bits, `D`
the axes, `cG` a constant), is added to it before the configuration is written, so the shift
field is `s = ⌈D/2⌉ + q + E_R + g` and the working width `W + s + D`. Then the fields `g`,
`s' = E_R + g - 5` and `k = 1` follow (`topCfgR`). -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open CompactGadgetReservationCapacity
noncomputable section
variable {Q A : ℕ} {U P : Type}

/-- The error exponent of the rounded pieces: `N + l + 2 + (cG + 1) D`. -/
def guardKc (cG N l D : ℕ) : ℕ := (cG+1)*D + (l + N + 1 + 1)

/-- The guard of the rounded top: `K + D + 6`. -/
def guardG (cG N l D : ℕ) : ℕ := D + guardKc cG N l D + 6

/-- The guard preparation: `K` on `ly 20`, the guard on `ly 21`, the guard added to the exponent
sum on `s 16` and the cut `E + g - 5` on `ly 22` (spare `s 2`). -/
def compactTopGuardPrep (cG : ℕ) : Pr P (nT SXReg) Q A U :=
  .seq (ucopy (sreg (.p .N)) (sreg (.ly 20)) (sreg (.s 2))) <|
  .seq (ucopy (sreg (.p .lr)) (sreg (.ly 20)) (sreg (.s 2))) <|
  .seq (synPush (sreg (.ly 20)) tick) <| .seq (synPush (sreg (.ly 20)) tick) <|
  .seq (umul (cG+1) (sreg (.p .D)) (sreg (.ly 20)) (sreg (.s 2))) <|
  .seq (ucopy (sreg (.ly 20)) (sreg (.ly 21)) (sreg (.s 2))) <|
  .seq (ucopy (sreg (.p .D)) (sreg (.ly 21)) (sreg (.s 2))) <|
  .seq (synPush (sreg (.ly 21)) tick) <| .seq (synPush (sreg (.ly 21)) tick) <|
  .seq (synPush (sreg (.ly 21)) tick) <| .seq (synPush (sreg (.ly 21)) tick) <|
  .seq (synPush (sreg (.ly 21)) tick) <| .seq (synPush (sreg (.ly 21)) tick) <|
  .seq (ucopy (sreg (.ly 21)) (sreg (.s 16)) (sreg (.s 2))) <|
  .seq (ucopy (sreg (.s 16)) (sreg (.ly 22)) (sreg (.s 2))) <|
  .seq (synPop (sreg (.ly 22))) <| .seq (synPop (sreg (.ly 22))) <|
  .seq (synPop (sreg (.ly 22))) <| .seq (synPop (sreg (.ly 22))) <|
  synPop (sreg (.ly 22))

def compactTopGuardPrepCost (cG N l D E : ℕ) : ℕ :=
  (4*N+4)+((4*l+4)+(1+(1+((4*D+4)+((4*guardKc cG N l D+4)+((4*D+4)+(6+
    ((4*guardG cG N l D+4)+((4*(guardG cG N l D+E)+4)+5)))))))))

theorem sg_compactTopGuardPrep (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (cG N l D E : ℕ) (hN : (v (.p .N)).length=N) (hl : (v (.p .lr)).length=l)
    (hD : (v (.p .D)).length=D) (h2 : v (.s 2)=[]) (hE : v (.s 16)=List.replicate E tick)
    (h20 : v (.ly 20)=[]) (h21 : v (.ly 21)=[]) (h22 : v (.ly 22)=[]) :
    LayRuns body (compactTopGuardPrep cG) (synG R v)
      (synG R (Function.update (Function.update (Function.update (Function.update v (.s 16)
        (List.replicate (guardG cG N l D+E) tick)) (.ly 21)
        (List.replicate (guardG cG N l D) tick)) (.ly 22)
        (List.replicate (guardG cG N l D+E-5) tick)) (.ly 20)
        (List.replicate (guardKc cG N l D) tick)))
      (compactTopGuardPrepCost cG N l D E) := by
  refine lr_weaken body
    ((sgU_copy body (a := .p .N) (b := .ly 20) (t := .s 2) (x := N) (y := 0) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp [hN]) (by simp [h20])).seq <|
    (sgU_copy body (a := .p .lr) (b := .ly 20) (t := .s 2) (x := l) (y := N+0) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp [hl]) (by simp)).seq <|
    (sgU_push body (a := .ly 20) (y := l+(N+0)) (by simp)).seq <|
    (sgU_push body (a := .ly 20) (y := l+(N+0)+1) (by simp)).seq <|
    (sgU_umul body (cG+1) (a := .p .D) (b := .ly 20) (t := .s 2) (x := D) (y := l+(N+0)+1+1)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hD]) (by simp)).seq <|
    (sgU_copy body (a := .ly 20) (b := .ly 21) (t := .s 2) (x := guardKc cG N l D) (y := 0)
      (by decide) (by decide) (by decide) (by simp [h2])
      (by simp [guardKc]) (by simp [h21])).seq <|
    (sgU_copy body (a := .p .D) (b := .ly 21) (t := .s 2) (x := D) (y := guardKc cG N l D+0)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hD]) (by simp)).seq <|
    (sgU_push body (a := .ly 21) (y := D+(guardKc cG N l D+0)) (by simp)).seq <|
    (sgU_push body (a := .ly 21) (y := D+(guardKc cG N l D+0)+1) (by simp)).seq <|
    (sgU_push body (a := .ly 21) (y := D+(guardKc cG N l D+0)+1+1) (by simp)).seq <|
    (sgU_push body (a := .ly 21) (y := D+(guardKc cG N l D+0)+1+1+1) (by simp)).seq <|
    (sgU_push body (a := .ly 21) (y := D+(guardKc cG N l D+0)+1+1+1+1) (by simp)).seq <|
    (sgU_push body (a := .ly 21) (y := D+(guardKc cG N l D+0)+1+1+1+1+1) (by simp)).seq <|
    (sgU_copy body (a := .ly 21) (b := .s 16) (t := .s 2) (x := guardG cG N l D) (y := E)
      (by decide) (by decide) (by decide) (by simp [h2])
      (by simp [guardG]) (by simp [hE])).seq <|
    (sgU_copy body (a := .s 16) (b := .ly 22) (t := .s 2) (x := guardG cG N l D+E) (y := 0)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp) (by simp [h22])).seq <|
    (sgU_pop body (a := .ly 22) (y := guardG cG N l D+E+0) (by simp)).seq <|
    (sgU_pop body (a := .ly 22) (y := guardG cG N l D+E+0-1) (by simp)).seq <|
    (sgU_pop body (a := .ly 22) (y := guardG cG N l D+E+0-1-1) (by simp)).seq <|
    (sgU_pop body (a := .ly 22) (y := guardG cG N l D+E+0-1-1-1) (by simp)).seq <|
    (sgU_pop body (a := .ly 22) (y := guardG cG N l D+E+0-1-1-1-1) (by simp))) ?_ ?_
  · apply congrArg (synG R)
    funext z
    simp only [Function.update_apply]
    split_ifs <;> simp_all [guardG, guardKc]
    all_goals omega
  · simp only [compactTopGuardPrepCost, guardG, guardKc]
    omega

/-- The extra fields of the rounded configuration: the guard (`ly 21`), the cut (`ly 22`) and the
shrink count `1`; the working width gains `K` (`ly 20`) and `G + 4`; `ly 20`–`ly 22` cleared. -/
def compactTopExtraFields (G : ℕ) : Pr P (nT SXReg) Q A U :=
  .seq (synCF (.ly 21)) <| .seq (synCF (.ly 22)) <|
  .seq (.seq (synPush (sreg (.p .cf)) tick) (synPush (sreg (.p .cf)) topSep)) <|
  .seq (ucopy (sreg (.ly 20)) (sreg (.p .w2)) (sreg (.s 2))) <|
  .seq (uclear (sreg (.ly 20))) <| .seq (synPush (sreg (.ly 20)) tick) <|
  .seq (umul (G+m+4) (sreg (.ly 20)) (sreg (.p .w2)) (sreg (.s 2))) <|
  .seq (uclear (sreg (.ly 20))) <|
  .seq (uclear (sreg (.ly 21))) (uclear (sreg (.ly 22)))

def compactTopExtraFieldsCost (Kc g s' : ℕ) : ℕ :=
  (4*g+5)+((4*s'+5)+(2+((4*Kc+4)+((2*Kc+2)+(1+((4*1+4)+((2*1+2)+((2*g+2)+(2*s'+2)))))))))

theorem sg_compactTopExtraFields (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (G : ℕ) (l : List ℕ) (Kc g s' X : ℕ) (h2 : v (.s 2)=[]) (hcf : v (.p .cf)=(topRec l).reverse)
    (h20 : v (.ly 20)=List.replicate Kc tick)
    (h21 : v (.ly 21)=List.replicate g tick) (h22 : v (.ly 22)=List.replicate s' tick)
    (hw2 : v (.p .w2)=List.replicate X tick) :
    LayRuns body (compactTopExtraFields G) (synG R v)
      (synG R (Function.update (Function.update (Function.update (Function.update
        (Function.update v (.p .cf) (topRec (l ++ [g, s', 1])).reverse) (.p .w2)
          (List.replicate (X+Kc+G+m+4) tick)) (.ly 20) []) (.ly 21) []) (.ly 22) []))
      (compactTopExtraFieldsCost Kc g s') := by
  refine lr_weaken body
    ((sg_synCF body (x := .ly 21) (by decide) (by decide) _ l g (by simp [h2]) (by simp [h21])
      (by simp [hcf])).seq <|
    (sg_synCF body (x := .ly 22) (by decide) (by decide) _ (l ++ [g]) s' (by simp [h2])
      (by simp [h22]) (by simp)).seq <|
    (sg_synCF1 body _ (l ++ [g] ++ [s']) (by simp)).seq <|
    (sgU_copy body (a := .ly 20) (b := .p .w2) (t := .s 2) (x := Kc) (y := X) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp [h20]) (by simp [hw2])).seq <|
    (sgU_clear body (a := .ly 20) (x := Kc) (by simp [h20])).seq <|
    (sgU_push body (a := .ly 20) (y := 0) (by simp)).seq <|
    (sgU_umul body (G+m+4) (a := .ly 20) (b := .p .w2) (t := .s 2) (x := 0+1) (y := Kc+X)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp) (by simp)).seq <|
    (sgU_clear body (a := .ly 20) (x := 0+1) (by simp)).seq <|
    (sgU_clear body (a := .ly 21) (x := g) (by simp [h21])).seq <|
    (sgU_clear body (a := .ly 22) (x := s') (by simp [h22]))) ?_
      (by simp [compactTopExtraFieldsCost])
  apply congrArg (synG R)
  funext z
  by_cases hz1 : z = .p .w2
  · subst hz1; simp; ring
  by_cases hz2 : z = .p .cf
  · subst hz2; simp
  by_cases hz3 : z = .ly 20
  · subst hz3; simp
  by_cases hz4 : z = .ly 21
  · subst hz4; simp
  by_cases hz5 : z = .ly 22
  · subst hz5; simp
  simp [Function.update_of_ne, hz1, hz2, hz3, hz4, hz5]

/-- The rounded original-input program: the record setup with no factor term, the guard
preparation, the configuration adapter and the extra fields. -/
def compactTopOriginalR (G cG : ℕ) (rowsSrc : SynW) : Pr P (nT SXReg) Q A U :=
  .seq (compactTopRecordSetup G 0)
    (.seq (compactTopGuardPrep cG) (.seq (compactTopOriginalAdapter rowsSrc)
      (compactTopExtraFields G)))

def compactTopOriginalRCost (G cG N d g K D o W Rv l : ℕ) : ℕ :=
  let q := CompactGlobalRowPadding.rowAxes NW m d
  let f := frontChunks d g K
  let b := backChunks d g K
  let active := D-q-f-b
  let E := b+synE G 0 active active
  let gb := guardG cG N l D
  let a := N-(o+K*(D-q))
  compactTopRecordSetupCost G 0 N d g K D o+
    (compactTopGuardPrepCost cG N l D E+
      (compactTopOriginalAdapterCost d g W a D (q+f) (gb+E) Rv (o+K*(b+active)) K o+
        compactTopExtraFieldsCost (guardKc cG N l D) gb (gb+E-5)))

/-- The rounded configuration after an arbitrary record preparation `prep`. -/
theorem sg_compactTopOriginalRFinish (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (rowsSrc : SynW) (hsrc : ∀ i, rowsSrc≠.s i) (hsrcpr : rowsSrc≠.p .pr)
    (hsrc20 : rowsSrc≠.ly 20) (hsrc21 : rowsSrc≠.ly 21) (hsrc22 : rowsSrc≠.ly 22)
    (G cG N l d g W a D q E Rv aT K o prepCost : ℕ) (record : List (Fin (A+4)))
    (prep : Pr P (nT SXReg) Q A U) (hdpos : 0<d)
    (hN : (v (.p .N)).length=N) (hl : (v (.p .lr)).length=l)
    (hd : (v (.s 0)).length=d) (hg : (v (.s 1)).length=g) (ho : (v (.s 7)).length=o)
    (hRows : (v rowsSrc).length=Rv) (hcf : v (.p .cf)=[]) (hw2 : v (.p .w2)=[])
    (hW : (v (.p .w)).length=W) (hD : (v (.p .D)).length=D)
    (h20 : v (.ly 20)=[]) (h21 : v (.ly 21)=[]) (h22 : v (.ly 22)=[])
    (hs : ∀ i : Fin 32, i≠0 → i≠1 → i≠7 → v (.s i)=[])
    (hr : LayRuns body prep (synG R v)
      (synG R (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update v (.s 16) (List.replicate E tick)) (.p .pr) record)
        (.s 30) (List.replicate a tick)) (.s 25) (List.replicate q tick))
        (.s 28) (List.replicate aT tick)) (.s 27) (List.replicate (K*q) tick))) prepCost) :
    LayRuns body (.seq prep (.seq (compactTopGuardPrep cG)
        (.seq (compactTopOriginalAdapter rowsSrc) (compactTopExtraFields G)))) (synG R v)
      (synG R (Function.update (Function.update (Function.update v (.p .pr) record) (.p .cf)
        (topRec (topCfgR W ((D+1)/2+q+(guardG cG N l D+E)) a Rv (compactTopRows d Rv a) q aT K o D
          (guardG cG N l D) (guardG cG N l D+E-5) 1)).reverse)
        (.p .w2) (List.replicate
          (W+((D+1)/2+q+(guardG cG N l D+E))+D+guardKc cG N l D+G+m+4) tick)))
      (prepCost+(compactTopGuardPrepCost cG N l D E+
        (compactTopOriginalAdapterCost d g W a D q (guardG cG N l D+E) Rv aT K o+
          compactTopExtraFieldsCost (guardKc cG N l D) (guardG cG N l D)
            (guardG cG N l D+E-5)))) := by
  let gb := guardG cG N l D
  let Kc := guardKc cG N l D
  let vr := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update v (.s 16) (List.replicate E tick)) (.p .pr) record)
      (.s 30) (List.replicate a tick)) (.s 25) (List.replicate q tick))
      (.s 28) (List.replicate aT tick)) (.s 27) (List.replicate (K*q) tick)
  have hp := sg_compactTopGuardPrep body R vr cG N l D E (by simp [vr, hN])
    (by simp [vr, hl]) (by simp [vr, hD]) (by simp [vr, hs 2]) (by simp [vr])
    (by simp [vr, h20]) (by simp [vr, h21]) (by simp [vr, h22])
  let v₂ := Function.update (Function.update (Function.update (Function.update vr (.s 16)
    (List.replicate (gb+E) tick)) (.ly 21) (List.replicate gb tick)) (.ly 22)
    (List.replicate (gb+E-5) tick)) (.ly 20) (List.replicate Kc tick)
  have ha := sg_compactTopOriginalAdapter body R v₂ rowsSrc hsrc d g W a D q (gb+E) Rv aT K o hdpos
    (by simp [v₂, vr, hd]) (by simp [v₂, vr, hg]) (by simp [v₂, vr, ho])
    (by simp [v₂, vr]) (by simp [v₂, vr])
    (by simp [v₂, vr, hsrc, hsrcpr, hsrc20, hsrc21, hsrc22, hRows])
    (by simp [v₂, vr]) (by simp [v₂, vr]) (by simp [v₂, vr])
    (by simp [v₂, vr, hcf]) (by simp [v₂, vr, hw2]) (by simp [v₂, vr, hW])
    (by simp [v₂, vr, hD])
    (by intro i h0 h1 h7 h16 h25 h27 h28 h30
        simp [v₂, vr, h16, h25, h27, h28, h30, hs i h0 h1 h7])
  let v₃ := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update v₂ (.s 16) []) (.s 25) [])
      (.s 27) []) (.s 28) []) (.s 30) []) (.p .cf)
      (topRec (topCfg W ((D+1)/2+q+(gb+E)) a Rv (compactTopRows d Rv a) q aT K o D)).reverse)
      (.p .w2) (List.replicate (W+((D+1)/2+q+(gb+E))+D) tick)
  have he := sg_compactTopExtraFields body R v₃ G
    (topCfg W ((D+1)/2+q+(gb+E)) a Rv (compactTopRows d Rv a) q aT K o D)
    Kc gb (gb+E-5) (W+((D+1)/2+q+(gb+E))+D)
    (by simp [v₃, v₂, vr, hs 2]) (by simp [v₃]) (by simp [v₃, v₂, vr])
    (by simp [v₃, v₂, vr]) (by simp [v₃, v₂, vr]) (by simp [v₃])
  refine lr_weaken body (hr.seq (hp.seq (ha.seq he))) ?_ (Nat.le_refl _)
  apply congrArg (synG R)
  funext z
  have h16 := hs 16 (by decide) (by decide) (by decide)
  have h25 := hs 25 (by decide) (by decide) (by decide)
  have h27 := hs 27 (by decide) (by decide) (by decide)
  have h28 := hs 28 (by decide) (by decide) (by decide)
  have h30 := hs 30 (by decide) (by decide) (by decide)
  by_cases hz1 : z=.p .pr
  · subst z; simp [v₃, v₂, vr]
  by_cases hz2 : z=.p .cf
  · subst z; simp [v₃, topCfgR, gb]
  by_cases hz3 : z=.p .w2
  · subst z; simp [v₃, gb, Kc]
  by_cases hz4 : z=.s 16
  · subst z; simp [v₃, h16]
  by_cases hz5 : z=.s 25
  · subst z; simp [v₃, v₂, vr, h25]
  by_cases hz6 : z=.s 27
  · subst z; simp [v₃, v₂, vr, h27]
  by_cases hz7 : z=.s 28
  · subst z; simp [v₃, v₂, vr, h28]
  by_cases hz8 : z=.s 30
  · subst z; simp [v₃, v₂, vr, h30]
  by_cases hz9 : z=.ly 20
  · subst z; simp [h20]
  by_cases hz10 : z=.ly 21
  · subst z; simp [h21]
  by_cases hz11 : z=.ly 22
  · subst z; simp [h22]
  simp [v₃, v₂, vr, Function.update_of_ne, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hz9, hz10,
    hz11]

/-- **The rounded configuration.** From original unary parameters, the record of the pieces on
`p.pr`, the configuration `topCfgR W s a Rv R₂ q aT K o D g s' 1` on `p.cf`, `s = ⌈D/2⌉ + q +
E_R + g`, `g = guardG`, `s' = E_R + g - 5`, and the working width `W + s + D + Kc + G + 4` on
`p.w2`, `Kc = guardKc`. -/
theorem sg_compactTopOriginalR (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (rowsSrc : SynW) (hsrc : ∀ i, rowsSrc≠.s i)
    (hsrcpr : rowsSrc≠.p .pr) (hsrc20 : rowsSrc≠.ly 20) (hsrc21 : rowsSrc≠.ly 21)
    (hsrc22 : rowsSrc≠.ly 22)
    (G cG N d g K D o W Rv l : ℕ) (hdpos : 0<d) (hk : 1≤K)
    (hN : (v (.p .N)).length=N) (hd : (v (.s 0)).length=d) (hg : (v (.s 1)).length=g)
    (hK : (v (.p .K)).length=K) (hD : (v (.p .D)).length=D) (ho : (v (.s 7)).length=o)
    (hW : (v (.p .w)).length=W) (hRows : (v rowsSrc).length=Rv) (hl : (v (.p .lr)).length=l)
    (hpr : v (.p .pr)=[]) (hcf : v (.p .cf)=[]) (hw2 : v (.p .w2)=[])
    (h20 : v (.ly 20)=[]) (h21 : v (.ly 21)=[]) (h22 : v (.ly 22)=[])
    (hs : ∀ i : Fin 32, i≠0 → i≠1 → i≠7 → v (.s i)=[]) :
    let q := CompactGlobalRowPadding.rowAxes NW m d
    let f := frontChunks d g K
    let b := backChunks d g K
    let active := D-q-f-b
    let E := b+synE G 0 active active
    let gb := guardG cG N l D
    let a := N-(o+K*(D-q))
    let shift := (D+1)/2+(q+f)+(gb+E)
    let record := topRec (topPcRec K (compactReservedPcs K 0 o b (o+K*b)
      (CompactGlobalRowPadding.depth m d) active))
    LayRuns body (compactTopOriginalR G cG rowsSrc) (synG R v)
      (synG R (Function.update (Function.update (Function.update v (.p .pr) record) (.p .cf)
        (topRec (topCfgR W shift a Rv (compactTopRows d Rv a) (q+f)
          (o+K*(b+active)) K o D gb (gb+E-5) 1)).reverse)
        (.p .w2) (List.replicate (W+shift+D+guardKc cG N l D+G+m+4) tick)))
      (compactTopOriginalRCost G cG N d g K D o W Rv l) := by
  let q := CompactGlobalRowPadding.rowAxes NW m d
  let f := frontChunks d g K
  let b := backChunks d g K
  let active := D-q-f-b
  exact sg_compactTopOriginalRFinish body R v rowsSrc hsrc hsrcpr hsrc20 hsrc21 hsrc22 G cG N l
    d g W (N-(o+K*(D-q))) D (q+f) (b+synE G 0 active active) Rv (o+K*(b+active)) K o
    (compactTopRecordSetupCost G 0 N d g K D o)
    (topRec (topPcRec K (compactReservedPcs K 0 o b (o+K*b)
      (CompactGlobalRowPadding.depth m d) active))) (compactTopRecordSetup G 0)
    hdpos hN hl hd hg ho hRows hcf hw2 hW hD h20 h21 h22 hs
    (sg_compactTopRecordSetup body R v G 0 N d g K D o hdpos hk hN hd hg hK hD ho hpr hs)

/-- The rounded original-input program on the compact bank. -/
def compactTopPlacedR (G cG : ℕ) (rowsSrc : SynW) : Pr P (nT CompactHostBReg) Q A U :=
  embProg compactLegacyReg (fun f : Empty => f.elim)
    (compactTopOriginalR (P:=Empty) G cG rowsSrc)

theorem compactTopPlacedR_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (rowsSrc : SynW) (hsrc : ∀ i, rowsSrc≠.s i)
    (hsrcpr : rowsSrc≠.p .pr) (hsrc20 : rowsSrc≠.ly 20) (hsrc21 : rowsSrc≠.ly 21)
    (hsrc22 : rowsSrc≠.ly 22)
    (G cG N d g K D o W Rv l : ℕ) (hdpos : 0<d) (hk : 1≤K)
    (hN : (v (.p .N)).length=N) (hd : (v (.s 0)).length=d) (hg : (v (.s 1)).length=g)
    (hK : (v (.p .K)).length=K) (hD : (v (.p .D)).length=D) (ho : (v (.s 7)).length=o)
    (hW : (v (.p .w)).length=W) (hRows : (v rowsSrc).length=Rv) (hl : (v (.p .lr)).length=l)
    (hpr : v (.p .pr)=[]) (hcf : v (.p .cf)=[]) (hw2 : v (.p .w2)=[])
    (h20 : v (.ly 20)=[]) (h21 : v (.ly 21)=[]) (h22 : v (.ly 22)=[])
    (hs : ∀ i : Fin 32, i≠0 → i≠1 → i≠7 → v (.s i)=[]) :
    let q := CompactGlobalRowPadding.rowAxes NW m d
    let f := frontChunks d g K
    let b := backChunks d g K
    let active := D-q-f-b
    let E := b+synE G 0 active active
    let gb := guardG cG N l D
    let a := N-(o+K*(D-q))
    let shift := (D+1)/2+(q+f)+(gb+E)
    let record := topRec (topPcRec K (compactReservedPcs K 0 o b (o+K*b)
      (CompactGlobalRowPadding.depth m d) active))
    CompactPlacedRuns body (compactTopPlacedR G cG rowsSrc) (synG R v)
      (synG R (Function.update (Function.update (Function.update v (.p .pr) record) (.p .cf)
        (topRec (topCfgR W shift a Rv (compactTopRows d Rv a) (q+f)
          (o+K*(b+active)) K o D gb (gb+E-5) 1)).reverse)
        (.p .w2) (List.replicate (W+shift+D+guardKc cG N l D+G+m+4) tick)))
      (compactTopOriginalRCost G cG N d g K D o W Rv l) := by
  dsimp only
  intro vbig S hL hR
  exact compactEmptySetup_exec compactLegacyReg compactLegacyReg_injective body
    (sg_compactTopOriginalR (fun f : Empty => f.elim) R v rowsSrc hsrc hsrcpr hsrc20 hsrc21 hsrc22
      G cG N d g K D o W Rv l hdpos hk hN hd hg hK hD ho hW hRows hl hpr hcf hw2 h20 h21 h22 hs)
    vbig S hL hR

end
end IntegerMultBounds.MathlibTM2.Fast
