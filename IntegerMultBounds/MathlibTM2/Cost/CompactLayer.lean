module

public import IntegerMultBounds.MathlibTM2.Node.CompactLayerProc
import IntegerMultBounds.MathlibTM2.Cost.CompactFactor
public import IntegerMultBounds.MathlibTM2.Cost.LayerCostNat
public import IntegerMultBounds.MathlibTM2.Cost.CompactBasis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Actual compact recursive layer budgets. The numerical basis budget uses the
compact selected width at each level; leaf and full-address control costs are
retained explicitly rather than hidden in an execution assumption. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open CompactGadgetReservationShape (Shape)
noncomputable section

/-- Node assembly accounting, independent of the implementation of its factors. -/
theorem compactNodeCost_linear (ds : ComplexFramedExecution.Directions)
    {u K ρ R₀ n r w j a₀ M B cf : ℕ}
    (hu : 1≤u) (hr : 1≤r) (hw : 1≤w) (hR₀ : 1≤R₀) (hρ : ρ<K)
    (hfit : a₀+K*bits u (j+1)≤n) (hTw : ∀ i≤j,expZ u ds i≤w)
    (hcf : cf≤M+2*B+400*NW*(rowsAt R₀ j*2^n*(r*w)+rowsAt R₀ j*2^n*n)) :
    nodeCost ds u j K ρ a₀ (rowsAt R₀ j) n r w cf+4 ≤
      factorCount (program ds)*(M+2*B)+
        lcLin ds*(NW*(rowsAt R₀ j*2^n*(r*w)+rowsAt R₀ j*2^n*n)) := by
  have hF : LcFacts u K a₀ (rowsAt R₀ j) n r w j :=
    lcFacts_of hu hr hw (rowsAt_pos hR₀ j) hρ hfit
  obtain ⟨hX1, hXV, hXW⟩ := lc_X_ge hF.hV1
  have hNW : 1 ≤ NW := one_le_NW
  have hSS := lc_signStage_le hF hρ
  have hgate : gateCost (rowsAt R₀ j) n r w ≤
      43 * (NW * (rowsAt R₀ j * 2 ^ n * (r * w) + rowsAt R₀ j * 2 ^ n * n)) := by
    unfold gateCost
    have h1 : NW * (rowsAt R₀ j * 2 ^ n * r) * (11 * w + 24) ≤
        35 * (NW * (rowsAt R₀ j * 2 ^ n * (r * w))) := by
      have := Nat.mul_le_mul_left NW hF.hPr
      nlinarith
    have h2 : NW * (rowsAt R₀ j * 2 ^ n * (r * w)) ≤
        NW * (rowsAt R₀ j * 2 ^ n * (r * w) + rowsAt R₀ j * 2 ^ n * n) :=
      Nat.mul_le_mul_left NW (Nat.le_add_right _ _)
    have h3 : NW ≤ NW * (rowsAt R₀ j * 2 ^ n * (r * w) + rowsAt R₀ j * 2 ^ n * n) :=
      Nat.le_mul_of_pos_right _ (by have := hF.hV1; omega)
    rw [show Fintype.card NWire = NW from rfl]
    omega
  have hexch : exchCost u (rowsAt R₀ j) n r w ≤
      30 * (NW * (rowsAt R₀ j * 2 ^ n * (r * w) + rowsAt R₀ j * 2 ^ n * n)) := by
    unfold exchCost
    nlinarith [hF.hPr, hF.hun, hF.hnW]
  have hE : expCost (gateCount (program ds)) (factorCount (program ds)) u j ≤
      4 * u + 2 * j + 8 + j * (8 * w + 12) := lc_expCost_le fun i hi => by
    rw [← expZ_eq_expSeq]; exact hTw i hi.le
  have hTc : expZ u ds j ≤ w := hTw j le_rfl
  have hNWR : NW * rowsAt R₀ j ≤
      NW * (rowsAt R₀ j * 2 ^ n * (r * w) + rowsAt R₀ j * 2 ^ n * n) :=
    Nat.mul_le_mul_left NW (hF.hRV.trans (Nat.le_add_right _ _))
  have hNWV : NW * (rowsAt R₀ j * 2 ^ n * (r * w)) ≤
      NW * (rowsAt R₀ j * 2 ^ n * (r * w) + rowsAt R₀ j * 2 ^ n * n) :=
    Nat.mul_le_mul_left NW (Nat.le_add_right _ _)
  have hNW1 : NW ≤ NW * (rowsAt R₀ j * 2 ^ n * (r * w) + rowsAt R₀ j * 2 ^ n * n) :=
    Nat.le_mul_of_pos_right _ (by have := hF.hV1; omega)
  have h1 := Nat.mul_le_mul_left (factorCount (program ds)) hcf
  have h2 := Nat.mul_le_mul_left (gateCount (program ds)) hgate
  have h3 := Nat.mul_le_mul_left (Fintype.card (Wires.Address 25)) hexch
  unfold nodeCost lcLin
  have hjw := hF.hjw
  have hun := hF.hun
  have hjle := hF.hjle
  have hnW := hF.hnW
  have hwV := hF.hwV
  generalize Fintype.card (Wires.Address 25) = c25 at *
  generalize factorCount (program ds) = F at *
  generalize gateCount (program ds) = G at *
  generalize rowsAt R₀ j * 2 ^ n * (r * w) = V at *
  generalize rowsAt R₀ j * 2 ^ n * n = Wn at *
  have := Nat.zero_le (G * (NW * (V + Wn)))
  have := Nat.zero_le (c25 * (NW * (V + Wn)))
  have := Nat.zero_le (m * c25 * (NW * (V + Wn)))
  have := Nat.zero_le (F * (NW * (V + Wn)))
  have := Nat.zero_le (NW * (V + Wn))
  linarith


/-- Levelwise basis budget; its width is selected axes times guard, never chunk
width times selected axes. It is independent of local offset and direction. -/
def compactLayerBasisBound (T D : ℕ) (s : Shape) (u R₀ n j : ℕ) : ℕ :=
  ⌈compactBasisConst T D*((2^(n-s.bits)*rowsAt R₀ j)*s.recordWidth : ℕ)*
    ((max 1 ((bits u j-1)*s.guard) : ℕ) : ℝ)^Parameters.tau⌉₊

def compactLayerBasisBudget (T D : ℕ) (s : Shape) (u R₀ n : ℕ) : CompactBasisBudget :=
  fun j _ _ _ => compactLayerBasisBound T D s u R₀ n j

/-- The canonical budget bounds the concrete executable basis, with only its
existing geometric and packing premises. -/
theorem compactLayerBasisBudget_covers {s : Shape} {n a kρ left right o R₀ u j r w : ℕ}
    (layout : CompactRecursiveLayout s n a (bits u j) kρ left right)
    (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (hR₀ : 1≤R₀)
    (hrecord : s.bits+1≤s.payload) (hpayload : s.payload=2^o*(3*(r*w)))
    (T Ka D : ℕ)
    (hp : ∀ x y (hxy : x≠y),1<bits u j → ActivePrefixStageRuntimeData.Packed
      (compactSlotComputedInputs layout x y hxy (rowsAt R₀ j) hG hGK (rowsAt_pos hR₀ j) hrecord) D)
    (vv : BinaryWalsh.Address m) (x : Fin m) :
    compactFactorBasisCost layout hG hGK (rowsAt_pos hR₀ j) hrecord D hp T Ka o r w vv x ≤
      compactLayerBasisBudget T D s u R₀ n j a vv x := by
  have h := compactBasisCost_le layout x hG hGK (rowsAt_pos hR₀ j) hrecord hpayload T Ka D (hp x) vv
  exact_mod_cast h.trans (Nat.le_ceil _)

/-- Scalar recurrence retaining the actual leaf and full-address linear costs. -/
def compactLayerMajorant (ds : ComplexFramedExecution.Directions)
    (u R₀ N r w : ℕ) (B : ℕ → ℕ) : ℕ → ℕ
  | 0 => 200*u*(R₀*2^N*(r*w)+R₀*2^N*N)
  | j+1 => factorCount (program ds)*(compactLayerMajorant ds u R₀ N r w B j+2*B j)+
      lcLin ds*(NW*(rowsAt R₀ j*2^N*(r*w)+rowsAt R₀ j*2^N*N))

/-- Every branch of the concrete recursive cost is bounded by the scalar
recurrence. This theorem assumes numerical budget inequalities, never executions. -/
theorem compactLayerCost_majorant (ds : ComplexFramedExecution.Directions)
    {u K ρ R₀ n o r w : ℕ} (budget : CompactBasisBudget) (B : ℕ → ℕ)
    (hu : 1≤u) (hr : 1≤r) (hw : 1≤w) (hR₀ : 1≤R₀) (hρ : ρ<K)
    (hB : ∀ j a vv x,budget j a vv x≤B j) :
    ∀ j, (∀ i<j,expZ u ds i≤w) → ∀ a,
      (o+a)+K*bits u j≤o+n →
      compactLayerCost ds u K ρ R₀ n o r w budget j a ≤
        compactLayerMajorant ds u R₀ (o+n) r w B j := by
  intro j
  induction j with
  | zero =>
      intro _ a hfit
      exact lc_leaf_nat 0 ds hu hr hw hR₀ hρ hfit
  | succ j ih =>
      intro hTw a hfit
      have hM : ∀ z<m,compactLayerCost ds u K ρ R₀ n o r w budget j
          (a+z*(K*bits u j))≤compactLayerMajorant ds u R₀ (o+n) r w B j := by
        intro z hz
        apply ih (fun i hi => hTw i (by omega))
        have hm : (z+1)*(K*bits u j)≤m*(K*bits u j) := Nat.mul_le_mul_right _ (by omega)
        have he : K*bits u (j+1)=m*(K*bits u j) := by rw [bits]; ring
        rw [he] at hfit
        nlinarith only [hfit,hm]
      have hcf : facMax ds (fun _ g => compactFactorCost (nT CompactBReg) ds j u K ρ (o+a)
          R₀ (o+n) r w g
          (compactLayerCost ds u K ρ R₀ n o r w budget j (a+pivotOf g.2*(K*bits u j)))
          (budget j a g.2)) ≤
          compactLayerMajorant ds u R₀ (o+n) r w B j+2*B j+
            400*NW*(rowsAt R₀ j*2^(o+n)*(r*w)+rowsAt R₀ j*2^(o+n)*(o+n)) := by
        apply lc_facMax_le
        intro fw g _
        have hf := compactFactorCost_linear (nT CompactBReg) ds g
          (compactLayerCost ds u K ρ R₀ n o r w budget j (a+pivotOf g.2*(K*bits u j))) (B j) (budget j a g.2)
          hu hr hw hR₀ hρ hfit (fun i hi => hTw i (by omega)) (hB j a g.2)
        have hc := hM (pivotOf g.2) (lc_pivotOf_lt g.2)
        have hextra := Nat.mul_le_mul_left (400*NW)
          (Nat.le_add_right (rowsAt R₀ j*2^(o+n)*(r*w)) (rowsAt R₀ j*2^(o+n)*(o+n)))
        omega
      exact compactNodeCost_linear ds hu hr hw hR₀ hρ hfit
        (fun i hi => hTw i (by omega)) hcf

/-- The actual layer with the concrete compact-width budget satisfies the full
scalar recurrence, with the original leaf/stopping cost unchanged. -/
theorem compactLayerCost_compact_majorant (ds : ComplexFramedExecution.Directions)
    {s : Shape} {u ρ R₀ n o r w : ℕ} (D : ℕ)
    (hu : 1≤u) (hr : 1≤r) (hw : 1≤w) (hR₀ : 1≤R₀) (hρ : ρ<s.chunk)
    (j : ℕ) (hTw : ∀ i<j,expZ u ds i≤w) (a : ℕ)
    (hfit : (o+a)+s.chunk*bits u j≤o+n) :
    compactLayerCost ds u s.chunk ρ R₀ n o r w
      (compactLayerBasisBudget (nT CompactBReg) D s u R₀ n) j a ≤
      compactLayerMajorant ds u R₀ (o+n) r w
        (compactLayerBasisBound (nT CompactBReg) D s u R₀ n) j :=
  compactLayerCost_majorant ds (compactLayerBasisBudget (nT CompactBReg) D s u R₀ n)
    (compactLayerBasisBound (nT CompactBReg) D s u R₀ n)
    hu hr hw hR₀ hρ (fun _ _ _ _ => le_rfl) j hTw a hfit

end
end IntegerMultBounds.MathlibTM2.Cost
