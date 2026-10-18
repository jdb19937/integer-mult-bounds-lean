module

public import IntegerMultBounds.MathlibTM2.Cost.CompactBasis
import IntegerMultBounds.MathlibTM2.Cost.LayerCostNat
public import IntegerMultBounds.MathlibTM2.Node.CompactFactor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Actual compact factor costs: the child bound has coefficient one, and every
other stage is paid by local volume and the compact selected-width envelope. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open CompactGadgetReservationShape (Shape)
noncomputable section

/-- The generic control, conjugation, shift and child-call framing costs are
linear in wire volume; the child execution retains coefficient one. -/
theorem compactFactorCost_linear (T : ℕ) (ds : ComplexFramedExecution.Directions)
    {j u K ρ a₀ R₀ n r w : ℕ} (g : ZMod 4 × BinaryWalsh.Address m) (cc B : ℕ) (basisBound : Fin m → ℕ)
    (hu : 1 ≤ u) (hr : 1 ≤ r) (hw : 1 ≤ w) (hR₀ : 1 ≤ R₀) (hρ : ρ < K)
    (hfit : a₀ + K * bits u (j + 1) ≤ n) (hTw : ∀ i ≤ j, expZ u ds i ≤ w)
    (hB : ∀ s,basisBound s≤B) :
    compactFactorCost T ds j u K ρ a₀ R₀ n r w g cc basisBound ≤
      cc + 2*B + 400*NW*(rowsAt R₀ j*2^n*(r*w)) := by
  have hF : LcFacts u K a₀ (rowsAt R₀ j) n r w j :=
    lcFacts_of hu hr hw (rowsAt_pos hR₀ j) hρ hfit
  set R := rowsAt R₀ j with hRdef
  have hNW : 1 ≤ NW := one_le_NW
  have hV1 := hF.hV1
  have hnV : n≤R*2^n*(r*w) :=
    (Nat.lt_two_pow_self.le.trans (Nat.le_mul_of_pos_left _ hF.hR)).trans hF.hPV
  have hWn := hnV
  have hRV := hF.hRV
  have hPr := hF.hPr
  have hwV := hF.hwV
  have hLc := hF.hLc
  have hun := hF.hun
  have hjn := hF.hjle
  have hjw := hF.hjw
  have hTc : expZ u ds j ≤ w := hTw j le_rfl
  have hE : expCost (gateCount (program ds)) (factorCount (program ds)) u j ≤
      4 * u + 2 * j + 8 + j * (8 * w + 12) := lc_expCost_le fun i hi => by
    rw [← expZ_eq_expSeq]; exact hTw i hi.le
  have hTcP : R * 2 ^ n * r * expZ u ds j ≤ R * 2 ^ n * (r * w) := by
    calc R * 2 ^ n * r * expZ u ds j ≤ R * 2 ^ n * r * w := Nat.mul_le_mul_left _ hTc
      _ = R * 2 ^ n * (r * w) := by ring
  have hNWV : ∀ x, x ≤ R * 2 ^ n * (r * w) → NW * x ≤ NW * (R * 2 ^ n * (r * w)) :=
    fun x hx => Nat.mul_le_mul_left _ hx
  have hNWV1 : NW ≤ NW * (R * 2 ^ n * (r * w)) := Nat.le_mul_of_pos_right _ hV1
  have hVNW : R * 2 ^ n * (r * w) ≤ NW * (R * 2 ^ n * (r * w)) := Nat.le_mul_of_pos_left _ hNW
  have hNB : NB ≤ 2 * NW := by rw [NB_eq, NW_eq]; norm_num
  have hNBx : ∀ x, NB * x ≤ 2 * NW * x := fun x => Nat.mul_le_mul_right x hNB
  have hs1 := hNBx (2 * (R * 2 ^ n * (r * w)) + 2)
  have hs2 := hNBx (4 * (R * 2 ^ n * (r * w)) + 5)
  have hs3 := hNBx (R * 2 ^ n * r * (6 * w + 4 * expZ u ds j + 14) + 4)
  unfold compactFactorCost
  split_ifs with hpiv
  · set s : Fin m := Fin.find _ hpiv
    have hs : (s : ℕ) * (K * bits u j) ≤ n := by
      have : (s : ℕ) * (K * bits u j) ≤ m * (K * bits u j) := Nat.mul_le_mul_right _ s.2.le
      have h' : m * (K * bits u j) = K * bits u (j + 1) := by
        rw [show bits u (j + 1) = m * bits u j from rfl]; ring
      have := hF.hKk
      omega
    have hb := hB s
    have h1 := hNWV _ hRV
    have h2' := hNWV _ hTcP
    have h3 := hNWV _ hPr
    unfold childCost callCost conjCost shiftCost
    nlinarith
  · unfold shiftCost
    have h2' := hNWV _ hTcP
    have h3 := hNWV _ hPr
    nlinarith


/-- A fixed dyadic coefficient, independent of shape, node level and payload. -/
theorem compactFactorDyadic (T D : ℕ) :
    ∃ e : ℕ,2*compactBasisConst T D+400*(NW:ℝ)+2≤(2:ℝ)^e := by
  have hB : (1:ℝ)≤compactBasisConst T D := one_le_pow₀ (by norm_num)
  obtain ⟨e,_,he⟩ := exists_nat_pow_near
    (show (1:ℝ)≤2*compactBasisConst T D+400*(NW:ℝ)+2 by
      nlinarith only [hB,Nat.cast_nonneg (α:=ℝ) NW])
    (show (1:ℝ)<2 by norm_num)
  exact ⟨e+1,he.le⟩

def compactFactorExponent (T D : ℕ) : ℕ := Classical.choose (compactFactorDyadic T D)
def compactFactorConst (T D : ℕ) : ℝ := 2^compactFactorExponent T D

theorem compactFactorConst_le (T D : ℕ) :
    2*compactBasisConst T D+400*(NW:ℝ)+2≤compactFactorConst T D :=
  Classical.choose_spec (compactFactorDyadic T D)

/-- Pure scalar absorption, keeping concrete machine programs opaque. -/
theorem compactFactor_envelope {cost cc B wires W V : ℕ} {C E F : ℝ}
    (hcost : cost≤cc+2*B+400*wires*W)
    (hB : (B:ℝ)≤C*(V:ℝ)*E+1) (hW : W≤V) (hV : 1≤V) (hE : 1≤E)
    (hF : 2*C+400*(wires:ℝ)+2≤F) :
    (cost:ℝ)≤(cc:ℝ)+F*(V:ℝ)*E := by
  have hc : (cost:ℝ)≤(cc:ℝ)+2*(B:ℝ)+400*(wires:ℝ)*(W:ℝ) := by exact_mod_cast hcost
  have hwR : (W:ℝ)≤V := by exact_mod_cast hW
  have hvR : (1:ℝ)≤V := by exact_mod_cast hV
  have hw := mul_le_mul_of_nonneg_left hwR (show (0:ℝ)≤400*(wires:ℝ) by positivity)
  have he := mul_le_mul_of_nonneg_left hE (show (0:ℝ)≤400*(wires:ℝ)*(V:ℝ) by positivity)
  have hone : (1:ℝ)≤(V:ℝ)*E := by nlinarith only [hvR,hE]
  have hf := mul_le_mul_of_nonneg_right hF (show 0≤(V:ℝ)*E by positivity)
  nlinarith only [hc,hB,hw,he,hone,hf]

end
end IntegerMultBounds.MathlibTM2.Cost
