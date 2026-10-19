module

public import IntegerMultBounds.MathlibTM2.Node.CompactBasis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Full compact basis budgets, including quadratic unary division costs in
runtime descriptor synthesis, native preparation, and both cleanup stages. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.Networks
open CompactGadgetReservationShape (Shape)
noncomputable section

/-- The constant of one compact slot operation. -/
def compactBasisSlotConst (T D : ℕ) : ℝ := 2 * CxData.cxSlotConst T D + 1

/-- One compact slot operation costs `O(V max(1, (k - 1) guard)^τ)` on a local volume `V`. -/
theorem compactBasisSlotCost_le {s : Shape} {n a₀ k ρ left right o R r w : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (hR : 0<R)
    (hpayload : s.payload=2^o*(3*(r*w))) (T D : ℕ)
    (hp : CompactSlotPacked s k (2^(n-s.bits)*R) D) :
    (compactBasisSlotCost T D layout R o r w : ℝ) ≤
      compactBasisSlotConst T D*((2^(n-s.bits)*R)*s.recordWidth : ℕ)*
        ((max 1 ((k-1)*s.guard) : ℕ) : ℝ)^Parameters.tau := by
  have hrb := compactSlot_rowBits (R := R) layout.totalFits hR
  have hrec := hp.record
  have hW : R * 2 ^ n * (n + (sxBits R).length + r * w * 2 ^ o) ≤
      2 * ((2^(n-s.bits)*R)*s.recordWidth) := by
    rw [compactSlot_volume layout R, hpayload]
    have : n + (sxBits R).length + r * w * 2 ^ o ≤ 2 * (2 ^ o * (3 * (r * w))) := by
      have h1 : r * w * 2 ^ o = 2 ^ o * (r * w) := Nat.mul_comm _ _
      have h2 : 2 ^ o * (3 * (r * w)) = 3 * (2 ^ o * (r * w)) := by ring
      rw [hpayload, h2] at hrec
      rw [h2]
      omega
    calc R * 2 ^ n * (n + (sxBits R).length + r * w * 2 ^ o)
        ≤ R * 2 ^ n * (2 * (2 ^ o * (3 * (r * w)))) := Nat.mul_le_mul_left _ this
      _ = 2 * (R * 2 ^ n * (2 ^ o * (3 * (r * w)))) := by ring
  obtain ⟨V, hV⟩ : ∃ V, (2^(n-s.bits)*R)*s.recordWidth = V := ⟨_, rfl⟩
  rw [hV] at hW ⊢
  have hV1 : 1 ≤ V := by
    rw [← hV]
    have : 0 < s.payload := by omega
    exact Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hR)
      (Nat.mul_pos (Nat.two_pow_pos _) this)
  have hE : (1:ℝ)≤((max 1 ((k-1)*s.guard) : ℕ) : ℝ)^Parameters.tau :=
    Real.one_le_rpow (by exact_mod_cast le_max_left 1 ((k-1)*s.guard)) (by norm_num [Parameters.tau])
  unfold compactBasisSlotCost
  generalize ((max 1 ((k-1)*s.guard) : ℕ) : ℝ)^Parameters.tau = E at hE ⊢
  have hC := CxData.cxSlotConst_nonneg T D
  have hWR : ((R * 2 ^ n * (n + (sxBits R).length + r * w * 2 ^ o) : ℕ) : ℝ) ≤ 2 * V := by
    exact_mod_cast hW
  have hVR : (1:ℝ) ≤ V := by exact_mod_cast hV1
  refine (Nat.ceil_lt_add_one (by positivity)).le.trans ?_
  have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWR hC) (by linarith : (0:ℝ) ≤ E)
  have h2 : (1:ℝ) ≤ V * E := by nlinarith
  unfold compactBasisSlotConst
  have h3 : (2 * CxData.cxSlotConst T D + 1) * V * E =
      CxData.cxSlotConst T D * (2 * V) * E + V * E := by ring
  rw [h3]
  linarith

theorem compactBasisDyadic (T D : ℕ) : ∃ e : ℕ, (m:ℝ)*compactBasisSlotConst T D+1 ≤ (2:ℝ)^e :=
  pow_unbounded_of_one_lt _ (by norm_num) |>.imp fun _ h => h.le

/-- The exponent of the basis constant. -/
def compactBasisExponent (T D : ℕ) : ℕ := Classical.choose (compactBasisDyadic T D)

def compactBasisConst (T D : ℕ) : ℝ := 2^compactBasisExponent T D

theorem compactBasisConst_le (T D : ℕ) :
    (m:ℝ)*compactBasisSlotConst T D+1≤compactBasisConst T D :=
  Classical.choose_spec (compactBasisDyadic T D)

private theorem list_cost_le {α : Type} (f : α → ℕ) (C : ℝ) (l : List α)
    (h : ∀ y∈l,(f y:ℝ)≤C) : ((l.map f).sum:ℝ)≤l.length*C := by
  induction l with
  | nil => simp
  | cons y l ih =>
      have hy := h y (by simp)
      have hl := ih (fun z hz => h z (by simp [hz]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      linarith

/-- The entire concrete basis target list retains the local compact-width
bound; the final terminating instruction is included in the power-of-two coefficient. -/
theorem compactBasisCost_le {s : Shape} {n a₀ k ρ left right o R r w : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x : Fin m)
    (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (hR : 0<R)
    (hrecord : s.bits+1≤s.payload) (hpayload : s.payload=2^o*(3*(r*w)))
    (T K D : ℕ)
    (hp : CompactSlotPacked s k (2^(n-s.bits)*R) D)
    (vv : BinaryWalsh.Address m) :
    ((((basisTargets vv x).map
      (compactBasisTargetCost layout x hG hGK hR hrecord D hp T K o r w)).sum+1 : ℕ):ℝ) ≤
      compactBasisConst T D*((2^(n-s.bits)*R)*s.recordWidth : ℕ)*
        ((max 1 ((k-1)*s.guard) : ℕ) : ℝ)^Parameters.tau := by
  let V := (2^(n-s.bits)*R)*s.recordWidth
  let E : ℝ := ((max 1 ((k-1)*s.guard) : ℕ) : ℝ)^Parameters.tau
  have hV : 1≤V := by
    have hpay : 0<s.payload := by omega
    change 0<(2^(n-s.bits)*R)*(2^s.bits*s.payload)
    positivity
  have hE : 1≤E := Real.one_le_rpow
    (by exact_mod_cast le_max_left 1 ((k-1)*s.guard)) (by norm_num [Parameters.tau])
  have hslot : 0≤compactBasisSlotConst T D := by
    have := CxData.cxSlotConst_nonneg T D; unfold compactBasisSlotConst; linarith
  have hs := list_cost_le (compactBasisTargetCost layout x hG hGK hR hrecord D hp T K o r w)
    (compactBasisSlotConst T D*(V:ℝ)*E) (basisTargets vv x) (by
      intro y hy
      have hxy : x≠y := (mem_basisTargets.mp hy).2.symm
      simpa only [compactBasisTargetCost,hxy,ne_eq,not_false_eq_true,↓reduceIte] using
        compactBasisSlotCost_le layout hR hpayload T D hp)
  have hlen : (basisTargets vv x).length≤m := by
    exact (List.length_filter_le _ _).trans_eq (List.length_finRange (n := m))
  have hlenR : ((basisTargets vv x).length:ℝ)≤m := by exact_mod_cast hlen
  have hs' := hs.trans (mul_le_mul_of_nonneg_right hlenR
    (show 0≤compactBasisSlotConst T D*(V:ℝ)*E by positivity))
  have hVR : (1:ℝ)≤V := by exact_mod_cast hV
  have hone : (1:ℝ)≤(V:ℝ)*E := by nlinarith only [hVR,hE]
  have hc := mul_le_mul_of_nonneg_right (compactBasisConst_le T D)
    (show 0≤(V:ℝ)*E by positivity)
  change _≤compactBasisConst T D*(V:ℝ)*E
  simp only [Nat.cast_add,Nat.cast_one]
  nlinarith only [hs',hone,hc]

end
end IntegerMultBounds.MathlibTM2.Cost
