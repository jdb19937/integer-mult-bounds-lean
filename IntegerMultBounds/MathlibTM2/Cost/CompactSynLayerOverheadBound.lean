module
public import IntegerMultBounds.MathlibTM2.Cost.CompactTopOriginalCompleteBound
public import IntegerMultBounds.MathlibTM2.Cost.CompactTopRecordBound
public import IntegerMultBounds.MathlibTM2.Cost.MatchSynPcs
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepCost

/-! Complete actual non-transform overhead of a compact chunk round. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast CompactGadgetReservationCapacity
noncomputable section

theorem compactSynChunkSourceCost_poly {h b K D B : ℕ}
    (hB : 1≤B) (hh : h≤B) (hb : b≤B) (hK : K≤B) (hD : D≤B) :
    compactSynChunkSourceCost h b K D≤256*B^3 := by
  have hc := mrO_chunkA_le hB hh hb hK hD
  have hx : (h-b)/K≤B := (Nat.div_le_self _ _).trans (by omega)
  have hp : K*((h-b)/K*D)≤B^3 := by
    have := Nat.mul_le_mul hK (Nat.mul_le_mul hx hD)
    nlinarith only [this]
  have h1 : 1≤B^3 := Nat.one_le_pow _ _ hB
  unfold compactSynChunkSourceCost
  omega

theorem compactBasisRefreshCost_poly {d g K D o r B : ℕ}
    (hB : 1≤B) (hd : d≤B) (hg : g≤B) (hK : K≤B) (hD : D≤B)
    (ho : o≤B) (hdg : d*g≤B)
    (hq : CompactGlobalRowPadding.rowAxes NW m d≤B)
    (hf : frontChunks d g K≤B) (hb : backChunks d g K≤B) :
    compactBasisRefreshCost d g K D o r≤4096*B^2+4*r := by
  have hrow := compactRowReserveCost_poly hB hd
  have hcounts := compactReserveCountsCost_poly hB hd hg hK hD hq ho hdg hf hb
  have hdq : D-CompactGlobalRowPadding.rowAxes NW m d≤B := by omega
  have hm := mrO_mulR_le hB hK hdq
  have hB2 : B≤B^2 := Nat.le_self_pow (by decide) _
  unfold compactBasisRefreshCost compactBasisCountsCost compactBasisCountsAfterCost
  dsimp only
  nlinarith only [hrow,hcounts,hm,hB2,hB,hd,hg,hD,ho,hq,hf,hb,hdq]

private theorem compactCleanupVector (x0 x1 x2 x3 x4 x5 x6 : ℕ) :
    compactClear7Cost (compactZeroTail ![x0,x1,x2,x3,x4,x5,x6]) =
    (2*x0+2)+(2*x1+2)+(2*x2+2)+(2*x3+2)+(2*x4+2)+(2*0+2)+(2*0+2) := rfl

private theorem compactCleanupPoly (q f back d g K D o r B : ℕ)
    (hB : 1≤B) (hK : K≤B) (hD : D≤B) (ho : o≤B) (hb : back≤B) :
    compactClear7Cost (compactZeroTail ![o,K*back,D-q-f-back,K*(D-q),r,d,g])≤32*B^2+2*r := by
  have ha : D-q-f-back≤B := by omega
  have hdq : D-q≤B := by omega
  have hkb := Nat.mul_le_mul hK hb
  have hkd := Nat.mul_le_mul hK hdq
  have hB2 : B≤B^2 := Nat.le_self_pow (by decide) _
  rw [compactCleanupVector]
  nlinarith only [ha,hkb,hkd,hB2,hB,ho]

theorem compactBasisCleanupCost_poly {d g K D o r B : ℕ}
    (hB : 1≤B) (hK : K≤B) (hD : D≤B) (ho : o≤B)
    (hb : backChunks d g K≤B) :
    compactClear7Cost (compactZeroTail (compactBasisSetupValues d g K D o r))≤32*B^2+2*r := by
  have hvalues : compactBasisSetupValues d g K D o r =
      ![o,K*backChunks d g K,
        D-CompactGlobalRowPadding.rowAxes NW m d-frontChunks d g K-backChunks d g K,
        K*(D-CompactGlobalRowPadding.rowAxes NW m d),r,d,g] := rfl
  have heq := congrArg (fun values => compactClear7Cost (compactZeroTail values)) hvalues
  exact heq.le.trans (compactCleanupPoly (CompactGlobalRowPadding.rowAxes NW m d)
    (frontChunks d g K) (backChunks d g K) d g K D o r B hB hK hD ho hb)

/-- The actual reserved record list has at most one more record than selected axes. -/
theorem compactTopPcs_length_axes (d g K D o R₂ : ℕ) :
    (compactTopPcs d g K D o R₂).length≤1+D := by
  let active := compactReservationActive d g K D
  let J := CompactGlobalRowPadding.depth m d
  have ha : active≤D := by dsimp [active,compactReservationActive]; omega
  have hlen := mrP_length_synPcs_le K 0 active (o+K*backChunks d g K) J active
  have hj := synJ_le active active
  have hback : (compactReservedPcs K 0 o (backChunks d g K)
      (o+K*backChunks d g K) J active).length≤
      1+(synPcs K 0 active (o+K*backChunks d g K) J active).length := by
    unfold compactReservedPcs
    split_ifs <;> simp only [List.length_append,List.length_nil,List.length_cons] <;> omega
  unfold compactTopPcs
  rw [List.length_map]
  exact hback.trans (Nat.add_le_add_left (hlen.trans (hj.trans ha)) 1)

private theorem compactShiftPoly (D q E B : ℕ) (hB : 1≤B)
    (hD : D≤B) (hq : q≤B) (hE : E≤B) : (D+1)/2+q+E≤4*B := by
  have := Nat.div_le_self (D+1) 2
  omega

private theorem compactWorkingPoly (W shift D B : ℕ) (hW : W≤B)
    (hs : shift≤4*B) (hD : D≤B) : W+shift+D≤6*B := by omega

private theorem compactRecordPoly (pr count n D B : ℕ) (hB : 1≤B)
    (hD : D≤B) (hn : n≤B) (hc : count≤1+D) (hp : pr≤count*(4*n+4)) :
    pr≤16*B^2 := by
  have hl : count≤2*B := by omega
  have hx := Nat.mul_le_mul hl (show 4*n+4≤8*B by omega)
  nlinarith only [hp,hx]

private theorem compactCfgLenPoly (W shift a R₂ q aT K o D B : ℕ)
    (hB : 1≤B) (hW : W≤B) (hs : shift≤4*B) (ha : a≤B)
    (hq : q≤B) (haT : aT≤B) (hKq : K*q≤B) (ho : o≤B) (hD : D≤B) :
    topRecLen (topCfg W shift a 1 R₂ q aT K o D)≤32*B+R₂ := by
  simp only [topCfg,topRecLen,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

private theorem compactRoundOverhead_split (G F N d g K D o W r h b ρ working pr cfg stash : ℕ) :
    compactSynLayerRoundOverhead G F N d g K D o W r h b ρ working pr cfg stash =
    compactSynChunkSourceCost h b K D+compactTopOriginalCost G F N d g K D o W 1+
    compactBasisRefreshCost d g K D o r+
    compactClear7Cost (compactZeroTail (compactBasisSetupValues d g K D o r))+
    synRestUpCost N r working K ρ pr+synRestDownCost N r working K ρ pr+
    2*stash+6*cfg+6*d+6*g+2*o+36 := by
  unfold compactSynLayerRoundOverhead compactSynLayerPrepareCost
    compactSynLayerParkCost compactSynLayerUnparkCost
  ring

private theorem compactOverheadCombine (B T V stash d g o working r rows stream
    source original refresh cleanup up down pr cfg : ℕ)
    (hB : 1≤B) (h1 : B≤T) (h2 : B^2≤T) (h3 : B^3≤T)
    (hd : d≤B) (hg : g≤B) (ho : o≤B) (hw : working≤6*B)
    (hr : r≤V) (hrows : rows≤V) (hstream : stream≤V)
    (hs : source≤256*B^3) (horig : original≤131072*T+8192*V)
    (href : refresh≤4096*B^2+4*r) (hclean : cleanup≤32*B^2+2*r)
    (hup : up≤60*stream+30*working+4*pr+100*B^2)
    (hdown : down≤8*stream+10*working+2*pr+50*B^2)
    (hpr : pr≤16*B^2) (hcfg : cfg≤32*B+rows) :
    source+original+refresh+cleanup+up+down+2*stash+6*cfg+6*d+6*g+2*o+36≤
      262144*T+16384*V+2*stash := by omega

/-- Full actual round overhead. Record lengths are derived from the actual
pieces and configuration; stash cost remains explicit and is charged twice. -/
theorem compactSynLayerRoundOverhead_complete (ds : ComplexFramedExecution.Directions)
    (G F N d g K D o W r h b ρ stash B : ℕ) :
    let qrow := CompactGlobalRowPadding.rowAxes NW m d
    let f := frontChunks d g K
    let back := backChunks d g K
    let active := D-qrow-f-back
    let E := back+synE G F active active
    let n := o+K*(D-qrow)
    let a := N-n
    let q := qrow+f
    let aT := o+K*(back+active)
    let shift := (D+1)/2+q+E
    let working := W+shift+D
    let R₂ := compactTopRows d 1 a
    let pcs := compactTopPcs d g K D o R₂
    let cfg := topCfg W shift a 1 R₂ q aT K o D
    let V := R₂*2^n*(r*working)
    ∀ (_hB : 1≤B) (_hF : F+1≤m^5) (_hdpos : 0<d)
      (_hKpos : 0<K) (_hr : 0<r) (_hWpos : 0<W)
      (_hN : N≤B) (_hd : d≤B) (_hg : g≤B) (_hK : K≤B) (_hD : D≤B)
      (_ho : o≤B) (_hW : W≤B) (_hdg : d*g≤B) (_hh : h≤B) (_hb : b≤B) (_hρ : ρ<K)
      (_hqrow : qrow≤B) (_hf : f≤B) (_hback : back≤B) (_hoffset : o+K*back≤B)
      (_hE : E≤B) (_hq : q≤B) (_haT : aT≤B) (_hKq : K*q≤B)
      (_hdivisor : NW^CompactGlobalRowPadding.depth m d≤B)
      (_ha : qrow*K≤a) (_hn : qrow*K+3≤n) (_hnN : n≤N) (_hBV : B≤V)
      (_hpcs : ∀ pc∈pcs,pc.Ok ds K n working R₂),
    compactSynLayerRoundOverhead G F N d g K D o W r h b ρ working
      (topRecLen (topPcRec K pcs)) (topRecLen cfg) stash≤
      262144*((G+m+1)*B^7)+16384*V+2*stash := by
  dsimp only
  intro hB hF hdpos hKpos hr hWpos hN hd hg hK hD ho hW hdg hh hb hρ
    hqrow hf hback hoffset hE hq haT hKq hdivisor ha hn hnN hBV hpcs
  let qrow := CompactGlobalRowPadding.rowAxes NW m d
  let f := frontChunks d g K
  let back := backChunks d g K
  let active := D-qrow-f-back
  let E := back+synE G F active active
  let n := o+K*(D-qrow)
  let a := N-n
  let q := qrow+f
  let aT := o+K*(back+active)
  let shift := (D+1)/2+q+E
  let working := W+shift+D
  let R₂ := compactTopRows d 1 a
  let pcs := compactTopPcs d g K D o R₂
  let cfg := topCfg W shift a 1 R₂ q aT K o D
  let V := R₂*2^n*(r*working)
  change E≤B at hE
  change q≤B at hq
  change aT≤B at haT
  change K*q≤B at hKq
  change qrow*K≤a at ha
  change qrow*K+3≤n at hn
  change B≤V at hBV
  change ∀ pc∈pcs,pc.Ok ds K n working R₂ at hpcs
  have hw : 0<working := hWpos.trans_le ((Nat.le_add_right W shift).trans (Nat.le_add_right (W+shift) D))
  have hV : 1≤V := hB.trans hBV
  have haB : a≤B := (Nat.sub_le _ _).trans hN
  have hnB : n≤B := hnN.trans hN
  have hshift : shift≤4*B := compactShiftPoly D q E B hB hD hq hE
  have hworking : working≤6*B := compactWorkingPoly W shift D B hW hshift hD
  have hstock : 2^a≤R₂ := by
    simpa only [Nat.one_mul] using (compactTopRows_bounds hKpos (by decide : 0<1) ha).1
  have hR₂pos : 0<R₂ := (pow_pos (by decide : 0<2) a).trans_le hstock
  have hrowsV : R₂≤V := by
    exact (Nat.le_mul_of_pos_right _ (pow_pos (by decide : 0<2) n)).trans
      (Nat.le_mul_of_pos_right _ (Nat.mul_pos hr hw))
  have hrV : r≤V := by
    exact (Nat.le_mul_of_pos_right r hw).trans
      (Nat.le_mul_of_pos_left _ (Nat.mul_pos hR₂pos (pow_pos (by decide : 0<2) n)))
  have hstream : 2^N*(r*working)≤V := by
    have hpow : 2^N≤2^a*2^n := by
      change 2^N≤2^(N-n)*2^n
      rw [←pow_add,Nat.sub_add_cancel hnN]
    exact (Nat.mul_le_mul_right _ hpow).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hstock))
  have horiginal := compactTopOriginalCost_complete G F N d g K D o W 1 r working B
    hB hF hdpos hKpos (by decide) hr hw hN hd hg hK hD ho hW hB hdg
    hqrow hf hback hoffset hE hq haT hKq hdivisor ha hn hBV
  change compactTopOriginalCost G F N d g K D o W 1≤131072*((G+m+1)*B^7)+8192*V at horiginal
  have hsource := compactSynChunkSourceCost_poly hB hh hb hK hD
  have hrefresh := compactBasisRefreshCost_poly (r:=r) hB hd hg hK hD ho hdg hqrow hf hback
  have hcleanup := compactBasisCleanupCost_poly (r:=r) hB hK hD ho hback
  have hup := mrO_restUp_le (r:=r) (W:=working) (prl:=topRecLen (topPcRec K pcs))
    hB hw hN hK (hρ.le.trans hK)
  have hdown := mrO_restDown_le (r:=r) (W:=working) (prl:=topRecLen (topPcRec K pcs))
    hB hN hK (hρ.le.trans hK)
  have hlen := compactTopPcs_length_axes d g K D o R₂
  have hrec := compactTopPcRecLen_control pcs hKpos hpcs
  have hpr := compactRecordPoly (topRecLen (topPcRec K pcs)) pcs.length n D B hB hD hnB hlen hrec
  have hcfg := compactCfgLenPoly W shift a R₂ q aT K o D B hB hW hshift haB hq haT hKq ho hD
  have h2 : B^2≤(G+m+1)*B^7 :=
    (Nat.pow_le_pow_right hB (by decide : 2≤7)).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos (G+m)))
  have h3 : B^3≤(G+m+1)*B^7 :=
    (Nat.pow_le_pow_right hB (by decide : 3≤7)).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos (G+m)))
  have h1 : B≤(G+m+1)*B^7 := (Nat.le_self_pow (by decide : 2≠0) B).trans h2
  have htotal := compactOverheadCombine B ((G+m+1)*B^7) V stash d g o working r R₂
    (2^N*(r*working)) _ _ _ _ _ _ (topRecLen (topPcRec K pcs)) (topRecLen cfg)
    hB h1 h2 h3 hd hg ho hworking hrV hrowsV hstream hsource horiginal hrefresh
    hcleanup hup hdown hpr hcfg
  change compactSynLayerRoundOverhead G F N d g K D o W r h b ρ working
    (topRecLen (topPcRec K pcs)) (topRecLen cfg) stash≤
      262144*((G+m+1)*B^7)+16384*V+2*stash
  exact (compactRoundOverhead_split G F N d g K D o W r h b ρ working
    (topRecLen (topPcRec K pcs)) (topRecLen cfg) stash).le.trans htotal

end
end IntegerMultBounds.MathlibTM2.Cost
