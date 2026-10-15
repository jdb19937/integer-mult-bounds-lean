module
public import IntegerMultBounds.MathlibTM2.Cost.CompactTopRecordSetupBound
public import IntegerMultBounds.MathlibTM2.Cost.CompactTopOriginalGeometry

/-! Complete polynomial-plus-volume cost of setup from original unary inputs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast CompactGadgetReservationCapacity
noncomputable section

/-- Actual record construction, coordinate setup, divisor construction and
adapter serialization. The division budget is derived from reserved address bits. -/
theorem compactTopOriginalCost_complete (G F N d g K D o W R r w B : ℕ) :
    let qrow := CompactGlobalRowPadding.rowAxes NW m d
    let f := frontChunks d g K
    let b := backChunks d g K
    let active := D-qrow-f-b
    let E := b+synE G F active active
    let n := o+K*(D-qrow)
    let a := N-n
    let q := qrow+f
    let aT := o+K*(b+active)
    let V := compactTopRows d R a*2^n*(r*w)
    ∀ (_hB : 1≤B) (_hF : F+1≤m^5) (_hdpos : 0<d)
      (_hKpos : 0<K) (_hRpos : 0<R) (_hr : 0<r) (_hw : 0<w)
      (_hN : N≤B) (_hd : d≤B) (_hg : g≤B) (_hK : K≤B) (_hD : D≤B)
      (_ho : o≤B) (_hW : W≤B) (_hR : R≤B) (_hdg : d*g≤B)
      (_hqrow : qrow≤B) (_hf : f≤B) (_hb : b≤B) (_hoffset : o+K*b≤B)
      (_hE : E≤B) (_hq : q≤B) (_haT : aT≤B) (_hKq : K*q≤B)
      (_hdivisor : NW^CompactGlobalRowPadding.depth m d≤B)
      (_ha : qrow*K≤a) (_hn : qrow*K+3≤n) (_hBV : B≤V),
    compactTopOriginalCost G F N d g K D o W R≤
      131072*((G+m+1)*B^7)+8192*V := by
  dsimp only
  intro hB hF hdpos hKpos hRpos hr hw hN hd hg hK hD ho hW hR hdg
    hqrow hf hb hoffset hE hq haT hKq hdivisor ha hn hBV
  let qrow := CompactGlobalRowPadding.rowAxes NW m d
  let f := frontChunks d g K
  let b := backChunks d g K
  let active := D-qrow-f-b
  let E := b+synE G F active active
  let n := o+K*(D-qrow)
  let a := N-n
  let q := qrow+f
  let aT := o+K*(b+active)
  let V := compactTopRows d R a*2^n*(r*w)
  have hV : 1≤V := hB.trans hBV
  have haB : a≤B := (Nat.sub_le _ _).trans hN
  have hrows : compactTopRows d R a≤V := by
    calc
      compactTopRows d R a≤compactTopRows d R a*2^n :=
        Nat.le_mul_of_pos_right _ (pow_pos (by decide : 0<2) n)
      _ ≤ V := Nat.le_mul_of_pos_right _ (Nat.mul_pos hr hw)
  have hdivision := compactTopOriginal_division_volume d K R a n r w hKpos hRpos hr hw ha hn
  have hadapter := compactTopOriginalAdapterCost_volume d g W a D q E R aT K o V
    hV (hg.trans hBV) (hW.trans hBV) (haB.trans hBV) (hD.trans hBV)
    (hq.trans hBV) (hE.trans hBV) (hR.trans hBV) hrows
    (haT.trans hBV) (hKq.trans hBV) (ho.trans hBV) hdivision
  have hsetup := compactTopRecordSetupCost_poly G hF hB hN hd hg hK hD ho hdg
    hqrow hf hb hoffset
  have hdiv := compactTopConfigDivisorCost_poly hdpos hB hd hdivisor
  have h2 : B^2≤(G+m+1)*B^7 :=
    (Nat.pow_le_pow_right hB (by decide : 2≤7)).trans
      (Nat.le_mul_of_pos_left _ (by omega))
  change compactTopRecordSetupCost G F N d g K D o+
    compactTopOriginalAdapterCost d g W a D q E R aT K o≤
      131072*((G+m+1)*B^7)+8192*V
  omega

end
end IntegerMultBounds.MathlibTM2.Cost
