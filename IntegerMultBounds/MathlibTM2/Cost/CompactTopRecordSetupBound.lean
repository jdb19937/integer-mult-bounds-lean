module
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopSetup
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopConfigDivisor
import IntegerMultBounds.MathlibTM2.Cost.MatchSynOver
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Scalar polynomial bounds for actual original-input record and coordinate setup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast CompactGadgetReservationCapacity
noncomputable section

theorem compactRowReserveCost_poly {d B : ℕ} (hB : 1≤B) (hd : d≤B) :
    compactRowReserveCost d≤256*B^2 := by
  have hc := mrO_cnt_le m (2*d-1) (2*d-1)
  have hj := synJ_le (2*d-1) (2*d-1)
  have ht : 2*d-1≤2*B := by omega
  have ht2 := Nat.mul_le_mul ht ht
  have hB2 : B≤B^2 := Nat.le_self_pow (by decide) _
  unfold compactRowReserveCost
  nlinarith only [hc,hj,ht,ht2,hB2,hB,hd]

theorem compactCeilCost_poly {x K B : ℕ} (hB : 1≤B) (hx : x≤2*B) (hK : K≤B) :
    compactCeilCost x K≤512*B^2 := by
  have ht : x+K-1≤3*B := by omega
  have hc := mrO_divMod_le (Z:=3*B) (by omega) ht (by omega : K≤3*B)
  have hm := Nat.mod_le (x+K-1) K
  have hB2 : B≤B^2 := Nat.le_self_pow (by decide) _
  unfold compactCeilCost
  nlinarith only [hc,hm,ht,hB2,hB,hx,hK]

theorem compactReserveCountsCost_poly {d g K D q o B : ℕ}
    (hB : 1≤B) (hd : d≤B) (hg : g≤B) (hK : K≤B) (hD : D≤B)
    (hq : q≤B) (ho : o≤B) (hdg : d*g≤B)
    (hf : frontChunks d g K≤B) (hb : backChunks d g K≤B) :
    compactReserveCountsCost d g K D q o≤2048*B^2 := by
  have hm := mrO_mulR_le hB hd hg
  have hmb := mrO_mulR_le hB hK hb
  have hc := compactCeilCost_poly hB (show 2*(d*g)≤2*B by omega) hK
  have hc' := compactCeilCost_poly hB (show d*g≤2*B by omega) hK
  have hB2 : B≤B^2 := Nat.le_self_pow (by decide) _
  unfold compactReserveCountsCost
  nlinarith only [hm,hmb,hc,hc',hB2,hB,hD,hq,ho,hdg,hf,hb]

theorem compactBackPieceCost_poly {K b o B : ℕ}
    (hB : 1≤B) (hK : K≤B) (hb : b≤B) (ho : o≤B) :
    compactBackPieceCost K b o≤128*B^2 := by
  have hm := mrO_mulR_le hB hK hb
  have hkb := Nat.mul_le_mul hK hb
  have hB2 : B≤B^2 := Nat.le_self_pow (by decide) _
  unfold compactBackPieceCost
  nlinarith only [hm,hkb,hB2,hB,hb,ho]

theorem compactTopCoordinatesCost_poly {N D K q f b active o B : ℕ}
    (hB : 1≤B) (hN : N≤B) (hD : D≤B) (hK : K≤B) (hq : q≤B)
    (hf : f≤B) (hb : b≤B) (ha : active≤B) (ho : o≤B) :
    compactTopCoordinatesCost N D K q f b active o≤1024*B^2 := by
  have hdq : D-q≤B := by omega
  have hm := mrO_mulR_le hB hK hdq
  have hm' := mrO_mulR_le (Z:=2*B) (by omega) (by omega : K≤2*B)
    (by omega : active+b≤2*B)
  have hm'' := mrO_mulR_le (Z:=2*B) (by omega) (by omega : K≤2*B)
    (by omega : f+q≤2*B)
  have hkd := Nat.mul_le_mul hK hdq
  have hB2 : B≤B^2 := Nat.le_self_pow (by decide) _
  unfold compactTopCoordinatesCost
  nlinarith only [hm,hm',hm'',hkd,hB2,hB,hN,hD,hq,hf,hb,ha,ho,hdq]

/-- Actual descriptor construction, with a common scalar budget rather than a cost oracle. -/
theorem compactReservedPiecesCost_poly (G : ℕ) {F K b o offset active B : ℕ}
    (hF : F+1≤m^5) (hB : 1≤B) (hK : K≤B) (hb : b≤B)
    (ho : o≤B) (hoffset : offset≤B) (ha : active≤B) :
    compactReservedPiecesCost G F K b o offset active≤1024*((G+m+1)*B^7) := by
  have hd := mrO_digits_le G hF hB hK hoffset ha
  have hj := (synJ_le active active).trans ha
  have hback := compactBackPieceCost_poly hB hK hb ho
  have h2 : B^2≤(G+m+1)*B^7 :=
    (Nat.pow_le_pow_right hB (by decide : 2≤7)).trans
      (Nat.le_mul_of_pos_left _ (by omega))
  have h1 : B≤(G+m+1)*B^7 := (Nat.le_self_pow (by decide : 2≠0) B).trans h2
  unfold compactReservedPiecesCost
  split_ifs <;> omega

/-- Original-input record setup, including both reservation scans and all top
coordinate arithmetic. Every premise bounds a scalar, never an execution cost. -/
theorem compactTopRecordSetupCost_poly (G : ℕ) {F N d g K D o B : ℕ}
    (hF : F+1≤m^5) (hB : 1≤B) (hN : N≤B) (hd : d≤B) (hg : g≤B)
    (hK : K≤B) (hD : D≤B) (ho : o≤B) (hdg : d*g≤B)
    (hq : CompactGlobalRowPadding.rowAxes NW m d≤B)
    (hf : frontChunks d g K≤B) (hb : backChunks d g K≤B)
    (hoffset : o+K*backChunks d g K≤B) :
    compactTopRecordSetupCost G F N d g K D o≤65536*((G+m+1)*B^7) := by
  have ha : D-CompactGlobalRowPadding.rowAxes NW m d-frontChunks d g K-backChunks d g K≤B := by omega
  have hrow := compactRowReserveCost_poly hB hd
  have hcounts := compactReserveCountsCost_poly hB hd hg hK hD hq ho hdg hf hb
  have hcoords := compactTopCoordinatesCost_poly hB hN hD hK hq hf hb ha ho
  have hpieces := compactReservedPiecesCost_poly G hF hB hK hb ho hoffset ha
  have h2 : B^2≤(G+m+1)*B^7 :=
    (Nat.pow_le_pow_right hB (by decide : 2≤7)).trans
      (Nat.le_mul_of_pos_left _ (by omega))
  have h1 : B≤(G+m+1)*B^7 := (Nat.le_self_pow (by decide : 2≠0) B).trans h2
  unfold compactTopRecordSetupCost compactSynRootCost compactSynRecCost
    compactTopSetupCost compactTopSetupAfterCost
  dsimp only
  omega

/-- The actual global row divisor is constructed with quadratic scalar cost. -/
theorem compactTopConfigDivisorCost_poly {d B : ℕ} (hdpos : 0<d)
    (hB : 1≤B) (hd : d≤B) (hp : NW^CompactGlobalRowPadding.depth m d≤B) :
    compactTopConfigDivisorCost d≤256*B^2 := by
  have hj := synJ_le (d-1) (d-1)
  have hjB : synJ (d-1) (d-1)≤B := by omega
  have ht : ∀ j∈Finset.range (synJ (d-1) (d-1)),8*(NW^j*1)+8+3≤8*B+11 := by
    intro j hj
    have he : j≤CompactGlobalRowPadding.depth m d := by
      rw [←compactTopConfigDepth d hdpos]
      exact (Finset.mem_range.mp hj).le
    have hpj := (Nat.pow_le_pow_right NW_pos he).trans hp
    omega
  have hs := Finset.sum_le_card_nsmul _ _ _ ht
  rw [Finset.card_range,smul_eq_mul] at hs
  have hs' := hs.trans (Nat.mul_le_mul_right (8*B+11) hjB)
  have hc := mrO_cnt_le m (d-1) (d-1)
  have hdb : d-1≤B := by omega
  have hdb2 := Nat.mul_le_mul hdb hdb
  have hB2 : B≤B^2 := Nat.le_self_pow (by decide) _
  unfold compactTopConfigDivisorCost
  nlinarith only [hs',hc,hjB,hdb,hdb2,hB2,hB,hd]

end
end IntegerMultBounds.MathlibTM2.Cost
