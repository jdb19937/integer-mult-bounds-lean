module
public import IntegerMultBounds.MathlibTM2.Cost.CompactSynLayerOverheadBound
public import IntegerMultBounds.MathlibTM2.Cost.CompactRuntimePolynomial
public import IntegerMultBounds.MathlibTM2.Cost.CompactTopBoundR
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepPrepR

/-! Complete non-transform overhead of a rounded compact chunk round: the setup from the original
unary inputs now also prepares the guard fields, the configuration has the three fields
`[g, s', k]` more, and the working width is a parameter. The bound has the shape of
`compactSynLayerRoundOverhead_complete`. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast CompactGadgetReservationCapacity Filter
noncomputable section

/-- The rounded setup from the original unary inputs. -/
theorem compactTopOriginalRCost_complete (G cG N d g K D o W r w l B : ℕ) :
    let qrow := CompactGlobalRowPadding.rowAxes NW m d
    let f := frontChunks d g K
    let b := backChunks d g K
    let active := D-qrow-f-b
    let E := b+synE G 0 active active
    let n := o+K*(D-qrow)
    let a := N-n
    let q := qrow+f
    let aT := o+K*(b+active)
    let gb := guardG cG N l D
    let V := compactTopRows d 1 a*2^n*(r*w)
    ∀ (_hB : 1≤B) (_hdpos : 0<d)
      (_hKpos : 0<K) (_hr : 0<r) (_hw : 0<w)
      (_hN : N≤B) (_hd : d≤B) (_hg : g≤B) (_hK : K≤B) (_hD : D≤B)
      (_ho : o≤B) (_hW : W≤B) (_hdg : d*g≤B) (_hl : l≤B)
      (_hqrow : qrow≤B) (_hf : f≤B) (_hb : b≤B) (_hoffset : o+K*b≤B)
      (_hE : gb+E≤B) (_hq : q≤B) (_haT : aT≤B) (_hKq : K*q≤B)
      (_hdivisor : NW^CompactGlobalRowPadding.depth m d≤B)
      (_ha : qrow*K≤a) (_hn : qrow*K+3≤n) (_hBV : B≤V),
    compactTopOriginalRCost G cG N d g K D o W 1 l≤
      131072*((G+m+1)*B^7)+8192*V := by
  dsimp only
  intro hB hdpos hKpos hr hw hN hd hg hK hD ho hW hdg hl
    hqrow hf hb hoffset hE hq haT hKq hdivisor ha hn hBV
  let qrow := CompactGlobalRowPadding.rowAxes NW m d
  let f := frontChunks d g K
  let b := backChunks d g K
  let active := D-qrow-f-b
  let E := b+synE G 0 active active
  let n := o+K*(D-qrow)
  let a := N-n
  let q := qrow+f
  let aT := o+K*(b+active)
  let gb := guardG cG N l D
  let V := compactTopRows d 1 a*2^n*(r*w)
  change gb+E≤B at hE
  have hV : 1≤V := hB.trans hBV
  have haB : a≤B := (Nat.sub_le _ _).trans hN
  have hrows : compactTopRows d 1 a≤V := by
    calc
      compactTopRows d 1 a≤compactTopRows d 1 a*2^n :=
        Nat.le_mul_of_pos_right _ (pow_pos (by decide : 0<2) n)
      _ ≤ V := Nat.le_mul_of_pos_right _ (Nat.mul_pos hr hw)
  have hdivision := compactTopOriginal_division_volume d K 1 a n r w hKpos (by decide) hr hw ha hn
  have hadapter := compactTopOriginalAdapterCost_volume d g W a D q (gb+E) 1 aT K o V
    hV (hg.trans hBV) (hW.trans hBV) (haB.trans hBV) (hD.trans hBV)
    (hq.trans hBV) (hE.trans hBV) hV hrows
    (haT.trans hBV) (hKq.trans hBV) (ho.trans hBV) hdivision
  have hsetup := compactTopRecordSetupCost_poly G (F:=0) (Nat.one_le_pow _ _ (by decide)) hB hN hd hg
    hK hD ho hdg hqrow hf hb hoffset
  have hdiv := compactTopConfigDivisorCost_poly hdpos hB hd hdivisor
  have h2 : B^2≤(G+m+1)*B^7 :=
    (Nat.pow_le_pow_right hB (by decide : 2≤7)).trans
      (Nat.le_mul_of_pos_left _ (by omega))
  have hB2 : B≤B^2 := Nat.le_self_pow (by decide) _
  have hKc : guardKc cG N l D≤gb := by
    change guardKc cG N l D≤guardG cG N l D
    unfold guardG; omega
  have hprep : compactTopGuardPrepCost cG N l D E≤64*B+64 := by
    unfold compactTopGuardPrepCost
    change _+((4*l+4)+(1+(1+((4*D+4)+((4*guardKc cG N l D+4)+((4*D+4)+(6+
      ((4*gb+4)+((4*(gb+E)+4)+5)))))))))≤_
    omega
  have hextra : compactTopExtraFieldsCost (guardKc cG N l D) gb (gb+E-5)≤32*B+32 := by
    unfold compactTopExtraFieldsCost
    omega
  change compactTopRecordSetupCost G 0 N d g K D o+
    (compactTopGuardPrepCost cG N l D E+
      (compactTopOriginalAdapterCost d g W a D q (gb+E) 1 aT K o+
        compactTopExtraFieldsCost (guardKc cG N l D) gb (gb+E-5)))≤
      131072*((G+m+1)*B^7)+8192*V
  omega

private theorem cfgLenPolyR (W s a R₂ q aT K o D gb s' B : ℕ)
    (hB : 1≤B) (hW : W≤B) (hs : s≤4*B) (ha : a≤B)
    (hq : q≤B) (haT : aT≤B) (hKq : K*q≤B) (ho : o≤B) (hD : D≤B) (hgb : gb≤B) (hs' : s'≤B) :
    topRecLen (topCfgR W s a 1 R₂ q aT K o D gb s' 1)≤40*B+R₂ := by
  simp only [topCfgR,topCfg,topRecLen,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    List.cons_append,List.nil_append]
  omega

private theorem recordPolyR (pr count n D B : ℕ) (hB : 1≤B)
    (hD : D≤B) (hn : n≤B) (hc : count≤1+D) (hp : pr≤count*(4*n+4)) :
    pr≤16*B^2 := by
  have hl : count≤2*B := by omega
  have hx := Nat.mul_le_mul hl (show 4*n+4≤8*B by omega)
  nlinarith only [hp,hx]

private theorem roundOverheadR_split (G cG N d g K D o W r h b l ρ working pr cfg stash : ℕ) :
    compactSynLayerRoundOverheadR G cG N d g K D o W r h b l ρ working pr cfg stash =
    compactSynChunkSourceCost h b K D+compactTopOriginalRCost G cG N d g K D o W 1 l+
    compactBasisRefreshCost d g K D o r+
    compactClear7Cost (compactZeroTail (compactBasisSetupValues d g K D o r))+
    synRestUpCost N r working K ρ pr+synRestDownCost N r working K ρ pr+
    2*stash+6*cfg+6*d+6*g+2*o+39 := by
  unfold compactSynLayerRoundOverheadR compactSynLayerPrepareRCost
    compactSynLayerParkCost compactSynLayerUnparkCostR
  ring

private theorem overheadCombineR (B T V stash d g o working r rows stream
    source original refresh cleanup up down pr cfg : ℕ)
    (hB : 1≤B) (h1 : B≤T) (h2 : B^2≤T) (h3 : B^3≤T)
    (hd : d≤B) (hg : g≤B) (ho : o≤B) (hw : working≤8*B)
    (hr : r≤V) (hrows : rows≤V) (hstream : stream≤V)
    (hs : source≤256*B^3) (horig : original≤131072*T+8192*V)
    (href : refresh≤4096*B^2+4*r) (hclean : cleanup≤32*B^2+2*r)
    (hup : up≤60*stream+30*working+4*pr+100*B^2)
    (hdown : down≤8*stream+10*working+2*pr+50*B^2)
    (hpr : pr≤16*B^2) (hcfg : cfg≤40*B+rows) :
    source+original+refresh+cleanup+up+down+2*stash+6*cfg+6*d+6*g+2*o+39≤
      262144*T+16384*V+2*stash := by omega

/-- **Full rounded round overhead.** The fields of the rounded configuration, the guard and the
working width are bounded by the scalar budget `B`; the record lengths come from the actual
pieces and configuration. -/
theorem compactSynLayerRoundOverheadR_complete
    (G cG N d g K D o W r h b l ρ working stash B : ℕ) :
    let qrow := CompactGlobalRowPadding.rowAxes NW m d
    let f := frontChunks d g K
    let back := backChunks d g K
    let active := D-qrow-f-back
    let E := back+synE G 0 active active
    let n := o+K*(D-qrow)
    let a := N-n
    let q := qrow+f
    let aT := o+K*(back+active)
    let gb := guardG cG N l D
    let s := (D+1)/2+q+(gb+E)
    let s' := gb+E-5
    let R₂ := compactTopRows d 1 a
    let pcs := compactTopPcs d g K D o R₂
    let cfg := topCfgR W s a 1 R₂ q aT K o D gb s' 1
    let V := R₂*2^n*(r*working)
    ∀ (_hB : 1≤B) (_hdpos : 0<d)
      (_hKpos : 0<K) (_hr : 0<r) (_hwpos : 0<working)
      (_hN : N≤B) (_hd : d≤B) (_hg : g≤B) (_hK : K≤B) (_hD : D≤B)
      (_ho : o≤B) (_hW : W≤B) (_hdg : d*g≤B) (_hh : h≤B) (_hb : b≤B) (_hl : l≤B) (_hρ : ρ<K)
      (_hqrow : qrow≤B) (_hf : f≤B) (_hback : back≤B) (_hoffset : o+K*back≤B)
      (_hE : gb+E≤B) (_hq : q≤B) (_haT : aT≤B) (_hKq : K*q≤B) (_hworking : working≤8*B)
      (_hdivisor : NW^CompactGlobalRowPadding.depth m d≤B)
      (_ha : qrow*K≤a) (_hn : qrow*K+3≤n) (_hnN : n≤N) (_hBV : B≤V)
      (_hpcs : ∀ pc∈pcs,pc.OkR K n R₂),
    compactSynLayerRoundOverheadR G cG N d g K D o W r h b l ρ working
      (topRecLen (topPcRec K pcs)) (topRecLen cfg) stash≤
      262144*((G+m+1)*B^7)+16384*V+2*stash := by
  dsimp only
  intro hB hdpos hKpos hr hw hN hd hg hK hD ho hW hdg hh hb hl hρ
    hqrow hf hback hoffset hE hq haT hKq hworking hdivisor ha hn hnN hBV hpcs
  let qrow := CompactGlobalRowPadding.rowAxes NW m d
  let f := frontChunks d g K
  let back := backChunks d g K
  let active := D-qrow-f-back
  let E := back+synE G 0 active active
  let n := o+K*(D-qrow)
  let a := N-n
  let q := qrow+f
  let aT := o+K*(back+active)
  let gb := guardG cG N l D
  let s := (D+1)/2+q+(gb+E)
  let s' := gb+E-5
  let R₂ := compactTopRows d 1 a
  let pcs := compactTopPcs d g K D o R₂
  let cfg := topCfgR W s a 1 R₂ q aT K o D gb s' 1
  let V := R₂*2^n*(r*working)
  change gb+E≤B at hE
  change q≤B at hq
  change aT≤B at haT
  change K*q≤B at hKq
  change qrow*K≤a at ha
  change qrow*K+3≤n at hn
  change B≤V at hBV
  change ∀ pc∈pcs,pc.OkR K n R₂ at hpcs
  have haB : a≤B := (Nat.sub_le _ _).trans hN
  have hnB : n≤B := hnN.trans hN
  have hshift : s≤4*B := by
    have := Nat.div_le_self (D+1) 2
    change (D+1)/2+q+(gb+E)≤4*B
    omega
  have hstock : 2^a≤R₂ := by
    simpa only [Nat.one_mul] using (compactTopRows_bounds hKpos (by decide : 0<1) ha).1
  have hR₂pos : 0<R₂ := (pow_pos (by decide : 0<2) a).trans_le hstock
  have hrowsV : R₂≤V :=
    (Nat.le_mul_of_pos_right _ (pow_pos (by decide : 0<2) n)).trans
      (Nat.le_mul_of_pos_right _ (Nat.mul_pos hr hw))
  have hrV : r≤V :=
    (Nat.le_mul_of_pos_right r hw).trans
      (Nat.le_mul_of_pos_left _ (Nat.mul_pos hR₂pos (pow_pos (by decide : 0<2) n)))
  have hstream : 2^N*(r*working)≤V := by
    have hpow : 2^N≤2^a*2^n := by
      change 2^N≤2^(N-n)*2^n
      rw [←pow_add,Nat.sub_add_cancel hnN]
    exact (Nat.mul_le_mul_right _ hpow).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hstock))
  have horiginal := compactTopOriginalRCost_complete G cG N d g K D o W r working l B
    hB hdpos hKpos hr hw hN hd hg hK hD ho hW hdg hl
    hqrow hf hback hoffset hE hq haT hKq hdivisor ha hn hBV
  change compactTopOriginalRCost G cG N d g K D o W 1 l≤131072*((G+m+1)*B^7)+8192*V at horiginal
  have hsource := compactSynChunkSourceCost_poly hB hh hb hK hD
  have hrefresh := compactBasisRefreshCost_poly (r:=r) hB hd hg hK hD ho hdg hqrow hf hback
  have hcleanup := compactBasisCleanupCost_poly (r:=r) hB hK hD ho hback
  have hup := mrO_restUp_le (r:=r) (W:=working) (prl:=topRecLen (topPcRec K pcs))
    hB hw hN hK (hρ.le.trans hK)
  have hdown := mrO_restDown_le (r:=r) (W:=working) (prl:=topRecLen (topPcRec K pcs))
    hB hN hK (hρ.le.trans hK)
  have hlen := compactTopPcs_length_axes d g K D o R₂
  have hrec := compactTopPcRecLenR_control pcs hKpos hpcs
  have hpr := recordPolyR (topRecLen (topPcRec K pcs)) pcs.length n D B hB hD hnB hlen hrec
  have hcfg := cfgLenPolyR W s a R₂ q aT K o D gb s' B hB hW hshift haB hq haT hKq ho hD
    (by omega) (by change gb+E-5≤B; omega)
  have h2 : B^2≤(G+m+1)*B^7 :=
    (Nat.pow_le_pow_right hB (by decide : 2≤7)).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos (G+m)))
  have h3 : B^3≤(G+m+1)*B^7 :=
    (Nat.pow_le_pow_right hB (by decide : 3≤7)).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos (G+m)))
  have h1 : B≤(G+m+1)*B^7 := (Nat.le_self_pow (by decide : 2≠0) B).trans h2
  have htotal := overheadCombineR B ((G+m+1)*B^7) V stash d g o working r R₂
    (2^N*(r*working)) _ _ _ _ _ _ (topRecLen (topPcRec K pcs)) (topRecLen cfg)
    hB h1 h2 h3 hd hg ho hworking hrV hrowsV hstream hsource horiginal hrefresh
    hcleanup hup hdown hpr hcfg
  exact (roundOverheadR_split G cG N d g K D o W r h b l ρ working
    (topRecLen (topPcRec K pcs)) (topRecLen cfg) stash).le.trans htotal

/-- Fixed polynomial scalar budgets make the rounded round overhead linear in the padded working
volume, with its two stash passes still explicit. -/
theorem compactSynLayerRoundOverheadR_eventually (G c e : ℕ) : ∀ᶠ M : ℕ in atTop,
    ∀ cG N d g K D o W r h b l ρ working stash B : ℕ,
    let qrow := CompactGlobalRowPadding.rowAxes NW m d
    let f := frontChunks d g K
    let back := backChunks d g K
    let active := D-qrow-f-back
    let E := back+synE G 0 active active
    let n := o+K*(D-qrow)
    let a := N-n
    let q := qrow+f
    let aT := o+K*(back+active)
    let gb := guardG cG N l D
    let s := (D+1)/2+q+(gb+E)
    let s' := gb+E-5
    let R₂ := compactTopRows d 1 a
    let pcs := compactTopPcs d g K D o R₂
    let cfg := topCfgR W s a 1 R₂ q aT K o D gb s' 1
    let V := R₂*2^n*(r*working)
    ∀ (_hB : 1≤B) (_hdpos : 0<d)
      (_hKpos : 0<K) (_hr : 0<r) (_hwpos : 0<working)
      (_hN : N≤B) (_hd : d≤B) (_hg : g≤B) (_hK : K≤B) (_hD : D≤B)
      (_ho : o≤B) (_hW : W≤B) (_hdg : d*g≤B) (_hh : h≤B) (_hb : b≤B) (_hl : l≤B) (_hρ : ρ<K)
      (_hqrow : qrow≤B) (_hf : f≤B) (_hback : back≤B) (_hoffset : o+K*back≤B)
      (_hE : gb+E≤B) (_hq : q≤B) (_haT : aT≤B) (_hKq : K*q≤B) (_hworking : working≤8*B)
      (_hdivisor : NW^CompactGlobalRowPadding.depth m d≤B)
      (_ha : qrow*K≤a) (_hn : qrow*K+3≤n) (_hnN : n≤N)
      (_hpoly : B≤2^c*(Mult.Sizes.p M+1)^e) (_hrun : Mult.Sizes.r M≤r)
      (_hpcs : ∀ pc∈pcs,pc.OkR K n R₂),
    compactSynLayerRoundOverheadR G cG N d g K D o W r h b l ρ working
      (topRecLen (topPcRec K pcs)) (topRecLen cfg) stash≤
      32768*V+2*stash := by
  filter_upwards [compactRuntime_eventually_setup_volume (262144*(G+m+1)) c e 7 14,
    compactRuntime_eventually_polynomial c e] with M habs hscalar
  intro cG N d g K D o W r h b l ρ working stash B
  dsimp only
  intro hB hdpos hKpos hr hw hN hd hg hK hD ho hW hdg hh hb hl hρ
    hqrow hf hback hoffset hE hq haT hKq hworking hdivisor ha hn hnN hpoly hrun hpcs
  have hrows : 0<compactTopRows d 1 (N-(o+K*(D-CompactGlobalRowPadding.rowAxes NW m d))) :=
    compactTopRows_positive hKpos (by decide : 0<1) ha
  have hrV : r≤compactTopRows d 1 (N-(o+K*(D-CompactGlobalRowPadding.rowAxes NW m d)))*
      2^(o+K*(D-CompactGlobalRowPadding.rowAxes NW m d))*(r*working) :=
    (Nat.le_mul_of_pos_right r hw).trans
      (Nat.le_mul_of_pos_left _ (Nat.mul_pos hrows (pow_pos (by decide : 0<2) _)))
  have hBV := hpoly.trans (hscalar.trans (hrun.trans hrV))
  have hbound := compactSynLayerRoundOverheadR_complete G cG N d g K D o W r h b l ρ working
    stash B hB hdpos hKpos hr hw hN hd hg hK hD ho hW hdg hh hb hl hρ
    hqrow hf hback hoffset hE hq haT hKq hworking hdivisor ha hn hnN hBV hpcs
  have hpay := habs B _ hpoly (hrun.trans hrV)
  have hpay' : 262144*((G+m+1)*B^7)+16384*(compactTopRows d 1
      (N-(o+K*(D-CompactGlobalRowPadding.rowAxes NW m d)))*
      2^(o+K*(D-CompactGlobalRowPadding.rowAxes NW m d))*(r*working))≤
      32768*(compactTopRows d 1 (N-(o+K*(D-CompactGlobalRowPadding.rowAxes NW m d)))*
      2^(o+K*(D-CompactGlobalRowPadding.rowAxes NW m d))*(r*working)) := by
    norm_num only [Nat.mul_assoc] at hpay ⊢
    exact hpay
  exact hbound.trans (Nat.add_le_add_right hpay' (2*stash))

end
end IntegerMultBounds.MathlibTM2.Cost
