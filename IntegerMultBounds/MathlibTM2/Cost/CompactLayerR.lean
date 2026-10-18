module

public import IntegerMultBounds.MathlibTM2.Cost.CompactLayerBound
public import IntegerMultBounds.MathlibTM2.Node.CompactLayerProcR
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! The rounded compact layer obeys the scalar recurrence `compactLayerMajorant` of the exact
layer: the node drops the exponent program and the `Tc` terms, and each factor pays the
truncation of its child (`truncCost`, linear in the wire volume) instead of the `Tc` shift. So
every closed bound of the exact layer holds for the rounded one (`compactLayerCostR_closed`),
with the scale hypothesis `expSeq G 0 u i ≤ w` in place of the compounding `expZ u ds i ≤ w`. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open CompactGadgetReservationShape (Shape)
noncomputable section

/-- Node assembly of the rounded layer, independent of its factors and exact instructions. -/
theorem compactNodeCostR_linear (ds : ComplexFramedExecution.Directions)
    {u K ρ R₀ n r w j a₀ M B cf cm : ℕ}
    (hu : 1≤u) (hr : 1≤r) (hw : 1≤w) (hR₀ : 1≤R₀) (hρ : ρ<K)
    (hfit : a₀+K*bits u (j+1)≤n)
    (hcf : cf≤M+2*B+400*NW*(rowsAt R₀ j*2^n*(r*w)+rowsAt R₀ j*2^n*n))
    (hcm : cm≤2*B+692*(NW*(rowsAt R₀ j*2^n*(r*w)+rowsAt R₀ j*2^n*n))) :
    nodeCostR ds u j K ρ a₀ (rowsAt R₀ j) n r w cf cm+4 ≤
      factorCount (program ds)*M+2*lcBas ds*B+
        lcLin ds*(NW*(rowsAt R₀ j*2^n*(r*w)+rowsAt R₀ j*2^n*n)) := by
  have hF : LcFacts u K a₀ (rowsAt R₀ j) n r w j :=
    lcFacts_of hu hr hw (rowsAt_pos hR₀ j) hρ hfit
  obtain ⟨hX1, hXV, hXW⟩ := lc_X_ge hF.hV1
  have hgate := lc_gate_le hF.hPr hF.hV1
  have hNWR : NW * rowsAt R₀ j ≤
      NW * (rowsAt R₀ j * 2 ^ n * (r * w) + rowsAt R₀ j * 2 ^ n * n) :=
    Nat.mul_le_mul_left NW (hF.hRV.trans (Nat.le_add_right _ _))
  have hNWV : NW * (rowsAt R₀ j * 2 ^ n * (r * w)) ≤
      NW * (rowsAt R₀ j * 2 ^ n * (r * w) + rowsAt R₀ j * 2 ^ n * n) :=
    Nat.mul_le_mul_left NW (Nat.le_add_right _ _)
  have hNW1 : NW ≤ NW * (rowsAt R₀ j * 2 ^ n * (r * w) + rowsAt R₀ j * 2 ^ n * n) :=
    Nat.le_mul_of_pos_right _ (by have := hF.hV1; omega)
  have hV : rowsAt R₀ j * 2 ^ n * r * w = rowsAt R₀ j * 2 ^ n * (r * w) := by ring
  have h2 := Nat.mul_le_mul_left (gateCount (program ds)) hgate
  have hN : nodeCostR ds u j K ρ a₀ (rowsAt R₀ j) n r w cf cm+4 ≤
      factorCount (program ds)*cf+monoCount (program ds)*cm+
        (100*gateCount (program ds)+500)*(NW*(rowsAt R₀ j*2^n*(r*w)+rowsAt R₀ j*2^n*n)) := by
    unfold nodeCostR
    rw [hV]
    generalize factorCount (program ds) = F at *
    generalize gateCount (program ds) = G at *
    generalize monoCount (program ds) = Mo at *
    generalize rowsAt R₀ j * 2 ^ n * (r * w) = V at *
    generalize rowsAt R₀ j * 2 ^ n * n = Wn at *
    have := Nat.zero_le (G * (NW * (V + Wn)))
    nlinarith
  rw [Nat.mul_assoc 400 NW] at hcf
  unfold lcLin lcBas
  exact lc_assemble hN hcf hcm

lemma four_le_NW : 4 ≤ NW := by rw [NW_eq]; norm_num

/-- The truncation of a child result is linear in the wire volume. -/
theorem truncCost_linear {G u j K a₀ R n r w : ℕ} (hF : LcFacts u K a₀ R n r w j)
    (hs : ∀ i≤j, expSeq G 0 u i≤w) :
    truncCost G u j R n r w ≤ 200*(R*2^n*(r*w)) := by
  have hE : expCost G 0 u j ≤ 4*u+2*j+8+j*(8*w+12) := lc_expCost_le fun i hi => hs i hi.le
  have hsj := hs j le_rfl
  have hV1 := hF.hV1
  have hPr := hF.hPr
  have hwV := hF.hwV
  have hjw := hF.hjw
  have hun := hF.hun
  have hjle := hF.hjle
  have hnV : n≤R*2^n*(r*w) :=
    (Nat.lt_two_pow_self.le.trans (Nat.le_mul_of_pos_left _ hF.hR)).trans hF.hPV
  have hsub : w - expSeq G 0 u j ≤ w := Nat.sub_le _ _
  have hVs : R*2^n*r*(w - expSeq G 0 u j) ≤ R*2^n*(r*w) := by
    calc R*2^n*r*(w - expSeq G 0 u j) ≤ R*2^n*r*w := Nat.mul_le_mul_left _ hsub
      _ = R*2^n*(r*w) := by ring
  have hVw : R*2^n*r*w = R*2^n*(r*w) := by ring
  have hVs' : R*2^n*r*expSeq G 0 u j ≤ R*2^n*(r*w) := by
    calc R*2^n*r*expSeq G 0 u j ≤ R*2^n*r*w := Nat.mul_le_mul_left _ hsj
      _ = R*2^n*(r*w) := by ring
  unfold truncCost topShiftCost topShiftWordCost topWidenCost
  generalize expSeq G 0 u j = s at *
  generalize R*2^n*(r*w) = V at *
  generalize R*2^n*r = P at *
  obtain ⟨t, rfl⟩ : ∃ t, w = t + s := ⟨w - s, by omega⟩
  have e1 : t + s - s = t := by omega
  have e3 : t + s - t = s := by omega
  simp only [e1, e3, Nat.sub_self, mul_zero] at *
  ring_nf at *
  nlinarith

/-- The rounded factor framing is linear in wire volume; the child execution keeps coefficient
one and its truncation is paid by the volume. -/
theorem compactFactorCostR_linear (ds : ComplexFramedExecution.Directions)
    {j u K ρ a₀ R₀ n r w : ℕ} (g : ZMod 4 × BinaryWalsh.Address m) (cc B : ℕ)
    (basisBound : Fin m → ℕ)
    (hu : 1 ≤ u) (hr : 1 ≤ r) (hw : 1 ≤ w) (hR₀ : 1 ≤ R₀) (hρ : ρ < K)
    (hfit : a₀ + K * bits u (j + 1) ≤ n) (hs : ∀ i ≤ j, expSeq (gateCount (program ds)) 0 u i ≤ w)
    (hB : ∀ s,basisBound s≤B) :
    compactFactorCostR j u K R₀ n r w g
      (cc + truncCost (gateCount (program ds)) u j (rowsAt R₀ j) n r w) basisBound ≤
      cc + 2*B + 400*NW*(rowsAt R₀ j*2^n*(r*w)) := by
  have hF : LcFacts u K a₀ (rowsAt R₀ j) n r w j :=
    lcFacts_of hu hr hw (rowsAt_pos hR₀ j) hρ hfit
  have hT := truncCost_linear hF hs
  unfold compactFactorCostR
  rw [show 400*NW*(rowsAt R₀ j*2^n*(r*w)) = 400*(NW*(rowsAt R₀ j*2^n*(r*w))) by ring]
  have hNW : 1 ≤ NW := one_le_NW
  have hV1 := hF.hV1
  have hnV : n≤rowsAt R₀ j*2^n*(r*w) :=
    (Nat.lt_two_pow_self.le.trans (Nat.le_mul_of_pos_left _ hF.hR)).trans hF.hPV
  have hRV := hF.hRV
  have hPr := hF.hPr
  have hwV := hF.hwV
  have hLc := hF.hLc
  have hNWV : ∀ x, x ≤ rowsAt R₀ j * 2 ^ n * (r * w) → NW * x ≤ NW * (rowsAt R₀ j * 2 ^ n * (r * w)) :=
    fun x hx => Nat.mul_le_mul_left _ hx
  have hNWV1 : NW ≤ NW * (rowsAt R₀ j * 2 ^ n * (r * w)) := Nat.le_mul_of_pos_right _ hV1
  have hVNW : 4 * (rowsAt R₀ j * 2 ^ n * (r * w)) ≤ NW * (rowsAt R₀ j * 2 ^ n * (r * w)) :=
    Nat.mul_le_mul_right _ four_le_NW
  have hVw : rowsAt R₀ j * 2 ^ n * r * w = rowsAt R₀ j * 2 ^ n * (r * w) := by ring
  have hconj : conjCost (rowsAt R₀ j) n r w ≤ 17 * (rowsAt R₀ j * 2 ^ n * (r * w)) := by
    unfold conjCost
    have : rowsAt R₀ j * 2 ^ n * r * (5 * w + 6) = 5 * (rowsAt R₀ j * 2 ^ n * r * w) + 6 * (rowsAt R₀ j * 2 ^ n * r) := by ring
    omega
  have hshift : shiftCost NB (rowsAt R₀ j) n r w 0 ≤ 60 * (NW * (rowsAt R₀ j * 2 ^ n * (r * w))) := by
    unfold shiftCost
    have : rowsAt R₀ j * 2 ^ n * r * (6 * w + 4 * 0 + 14) = 6 * (rowsAt R₀ j * 2 ^ n * r * w) + 14 * (rowsAt R₀ j * 2 ^ n * r) := by
      ring
    have h1 : NB * (rowsAt R₀ j * 2 ^ n * r * (6 * w + 4 * 0 + 14) + 4) ≤ NB * (24 * (rowsAt R₀ j * 2 ^ n * (r * w))) :=
      Nat.mul_le_mul_left _ (by omega)
    have h1' := lc_NB_mul (24 * (rowsAt R₀ j * 2 ^ n * (r * w)))
    have h2 : NW * (24 * (rowsAt R₀ j * 2 ^ n * (r * w))) = 24 * (NW * (rowsAt R₀ j * 2 ^ n * (r * w))) := by ring
    omega
  split_ifs with hpiv
  · set s : Fin m := Fin.find _ hpiv
    have hs' : (s : ℕ) * (K * bits u j) ≤ n := by
      have : (s : ℕ) * (K * bits u j) ≤ m * (K * bits u j) := Nat.mul_le_mul_right _ s.2.le
      have h' : m * (K * bits u j) = K * bits u (j + 1) := by
        rw [show bits u (j + 1) = m * bits u j from rfl]; ring
      have := hF.hKk
      omega
    have hb := hB s
    have hchild : childCostR (rowsAt R₀ j * 2 ^ n * (r * w)) (K * bits u j) s
        (cc + truncCost (gateCount (program ds)) u j (rowsAt R₀ j) n r w) ≤
        cc + truncCost (gateCount (program ds)) u j (rowsAt R₀ j) n r w + 80 * (NW * (rowsAt R₀ j * 2 ^ n * (r * w))) := by
      unfold childCostR callCostR
      have h1 : NB * (2 * (rowsAt R₀ j * 2 ^ n * (r * w)) + 2) ≤ 8 * (NW * (rowsAt R₀ j * 2 ^ n * (r * w))) := by
        have : NW * (2 * (rowsAt R₀ j * 2 ^ n * (r * w)) + 2) = 2 * (NW * (rowsAt R₀ j * 2 ^ n * (r * w))) + 2 * NW := by
          ring
        have := lc_NB_mul (2 * (rowsAt R₀ j * 2 ^ n * (r * w)) + 2)
        omega
      have h2 : NB * (4 * (rowsAt R₀ j * 2 ^ n * (r * w)) + 5) ≤ 18 * (NW * (rowsAt R₀ j * 2 ^ n * (r * w))) := by
        have : NW * (4 * (rowsAt R₀ j * 2 ^ n * (r * w)) + 5) = 4 * (NW * (rowsAt R₀ j * 2 ^ n * (r * w))) + 5 * NW := by
          ring
        have := lc_NB_mul (4 * (rowsAt R₀ j * 2 ^ n * (r * w)) + 5)
        omega
      omega
    have hk1 : K * bits u (j + 1) ≤ rowsAt R₀ j * 2 ^ n * (r * w) := hF.hKk.trans hnV
    have hR1 : NW * rowsAt R₀ j ≤ NW * (rowsAt R₀ j * 2 ^ n * (r * w)) := hNWV _ hRV
    omega
  · omega

/-- **The rounded layer obeys the scalar recurrence of the exact layer.** -/
theorem compactLayerCostR_majorant (ds : ComplexFramedExecution.Directions)
    {u K ρ R₀ n o r w : ℕ} (budget : CompactBasisBudget) (B : ℕ → ℕ)
    (hu : 1≤u) (hr : 1≤r) (hw : 1≤w) (hR₀ : 1≤R₀) (hρ : ρ<K)
    (hB : ∀ j a vv x,budget j a vv x≤B j) :
    ∀ j, (∀ i<j,expSeq (gateCount (program ds)) 0 u i≤w) → ∀ a,
      (o+a)+K*bits u j≤o+n →
      compactLayerCostR ds u K ρ R₀ n o r w budget j a ≤
        compactLayerMajorant ds u R₀ (o+n) r w B j := by
  intro j
  induction j with
  | zero =>
      intro _ a hfit
      exact lc_leaf_nat 0 ds hu hr hw hR₀ hρ hfit
  | succ j ih =>
      intro hs a hfit
      have hM : ∀ z<m,compactLayerCostR ds u K ρ R₀ n o r w budget j
          (a+z*(K*bits u j))≤compactLayerMajorant ds u R₀ (o+n) r w B j := by
        intro z hz
        apply ih (fun i hi => hs i (by omega))
        have hm : (z+1)*(K*bits u j)≤m*(K*bits u j) := Nat.mul_le_mul_right _ (by omega)
        have he : K*bits u (j+1)=m*(K*bits u j) := by rw [bits]; ring
        rw [he] at hfit
        nlinarith only [hfit,hm]
      have hcf : facMax ds (fun _ g => compactFactorCostR j u K R₀ (o+n) r w g
          (compactLayerCostR ds u K ρ R₀ n o r w budget j (a+pivotOf g.2*(K*bits u j)) +
            truncCost (gateCount (program ds)) u j (rowsAt R₀ j) (o+n) r w)
          (budget j a g.2)) ≤
          compactLayerMajorant ds u R₀ (o+n) r w B j+2*B j+
            400*NW*(rowsAt R₀ j*2^(o+n)*(r*w)+rowsAt R₀ j*2^(o+n)*(o+n)) := by
        apply lc_facMax_le
        intro fw g _
        have hf := compactFactorCostR_linear ds (a₀ := o+a) (ρ := ρ) g
          (compactLayerCostR ds u K ρ R₀ n o r w budget j (a+pivotOf g.2*(K*bits u j))) (B j)
          (budget j a g.2) hu hr hw hR₀ hρ hfit (fun i hi => hs i (by omega)) (hB j a g.2)
        have hc := hM (pivotOf g.2) (lc_pivotOf_lt g.2)
        have hextra := Nat.mul_le_mul_left (400*NW)
          (Nat.le_add_right (rowsAt R₀ j*2^(o+n)*(r*w)) (rowsAt R₀ j*2^(o+n)*(o+n)))
        omega
      have hcm : monoMax ds (monoCostB (budget j a) j u K (o+a) R₀ (o+n) o r w ρ (rowsAt R₀ j)) ≤
          2*B j+692*(NW*(rowsAt R₀ j*2^(o+n)*(r*w)+rowsAt R₀ j*2^(o+n)*(o+n))) :=
        lc_monoMax_le ds _ _ fun ins _ =>
          compactMono_linear (budget j a) hu hr hw hR₀ hρ hfit (hB j a) ins
      exact compactNodeCostR_linear ds hu hr hw hR₀ hρ hfit hcf hcm

/-- **Closed bound of the rounded layer** with the canonical compact basis budget: the bound of
`compactLayerCost_closed`, with the child scales below the width in place of `expZ ≤ w`. -/
theorem compactLayerCostR_closed (ds : ComplexFramedExecution.Directions)
    (D : ℕ) (s : Shape) (u R₀ n o r w : ℕ) {ρ : ℕ} {lam : ℝ}
    (hu : 1≤u) (hR₀ : 1≤R₀) (hr : 1≤r) (hw : 1≤w) (hρ : ρ<s.chunk)
    (hG : 1≤s.guard) (hbits : s.bits≤n)
    (hpayload : s.payload=2^o*(3*(r*w))) (hN : o+n≤r*w)
    (hτl : Parameters.tau≤lam)
    (hal : Real.logb (m:ℝ) ((factorCount (program ds):ℝ)/NW)<lam)
    (j : ℕ) (hs : ∀ i<j,expSeq (gateCount (program ds)) 0 u i≤w) (a : ℕ)
    (hfit : (o+a)+s.chunk*bits u j≤o+n) :
    (compactLayerCostR ds u s.chunk ρ R₀ n o r w
      (compactLayerBasisBudget (nT CompactBReg) D s u R₀ n) j a:ℝ) ≤
      ((rowsAt R₀ j*2^(o+n)*(r*w):ℕ):ℝ)*
      (compactLayerClosedConst (nT CompactBReg) D ds lam*((m:ℝ)^j*u)^lam*(s.guard:ℝ)^Parameters.tau+
       compactLayerClosedConst (nT CompactBReg) D ds lam*((factorCount (program ds):ℝ)/NW)^j*u) := by
  have hM := compactLayerCostR_majorant ds (compactLayerBasisBudget (nT CompactBReg) D s u R₀ n)
    (compactLayerBasisBound (nT CompactBReg) D s u R₀ n)
    hu hr hw hR₀ hρ (fun _ _ _ _ => le_rfl) j hs a hfit
  have hclosed := compactLayerNormalized_closed ds (nT CompactBReg) D s u R₀ n o r w
    hu hR₀ hr hw hG hbits hpayload hN hτl hal j
  have hV : (0:ℝ)<((rowsAt R₀ j*2^(o+n)*(r*w):ℕ):ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos (rowsAt_pos hR₀ j)
      (pow_pos (by decide : 0<2) _)) (Nat.mul_pos hr hw)
  have hh := (div_le_iff₀ hV).mp hclosed
  exact (Nat.cast_le.mpr hM).trans (by simpa only [mul_comm] using hh)

end
end IntegerMultBounds.MathlibTM2.Cost
