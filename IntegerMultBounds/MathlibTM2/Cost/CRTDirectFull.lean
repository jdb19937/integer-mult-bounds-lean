module

public import IntegerMultBounds.MathlibTM2.Fast.CRTDirectMachineFull
public import IntegerMultBounds.MathlibTM2.Cost.CRTDirectMachine
import IntegerMultBounds.MathlibTM2.Cost.CRTDirectSetup
public import IntegerMultBounds.MathlibTM2.Fast.CRTDirectSetup
import IntegerMultBounds.MathlibTM2.Cost.MatchBase
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! # Matching the full concrete direct CRT costs -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter
  IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

theorem crtDirectMachineScanCost_le {L c cw p : ℕ}
    (hc : c ≤ cw * p) (hL : L ≤ p) (hp : 1 ≤ p) :
    crtDirectMachineScanCost L c ≤ (16 * cw + 93) * (2 ^ L * p) := by
  have hX : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  have h1 : 10 * c + 10 * L + 29 ≤ (10 * cw + 39) * p := by nlinarith
  have h2 := Nat.mul_le_mul_left (2 ^ L) h1
  have h3 : 25 * L + 6 * c + 29 ≤ (6 * cw + 54) * p := by nlinarith
  have h4 := Nat.mul_le_mul_right ((6 * cw + 54) * p) hX
  unfold crtDirectMachineScanCost
  nlinarith

theorem crtDirectMachineCoreCosts_le {d K : ℕ} (Tm B w c : ℕ)
    (a s μ : Fin (d + 1) → ℕ) :
    let overhead := 12 * (∑ i, a i) + 4 * (∑ i, s i) + 4 * (∑ i, μ i) + 37 * (d + 1) + 3
    crtDirectMachineForwardCoreCost (K := K) Tm B w c a s μ ≤
      crtDirectMachineLoopCost (K := K) Tm B w c a s μ + overhead ∧
    crtDirectMachineInverseCoreCost (K := K) Tm B w c a s μ ≤
      crtDirectMachineLoopCost (K := K) Tm B w c a s μ + overhead := by
  have hwidth (f : Fin (d + 1) → ℕ) : crtW f (List.finRange (d + 1)) = ∑ i, f i := by
    unfold crtW
    rw [← List.ofFn_eq_map, List.sum_ofFn]
  have hlength (f : Fin (d + 1) → ℕ) :
      (crtEnts (A := prime + K) ((List.finRange (d + 1)).map f)).length =
        (∑ i, f i) + 2 * (d + 1) := by
    rw [crtEnts_map_length, hwidth, List.length_finRange]
  simp only [crtDirectMachineForwardCoreCost, crtDirectMachineInverseCoreCost,
    hlength, crtDirectSetupStream_length, hwidth, crtControl_fullWidth]
  constructor <;> omega

theorem crtDirectMachineReverseCost_le {d K : ℕ} (Tm c am : ℕ)
    (a : Fin (d + 1) → ℕ) (ha : ∀ i, a i ≤ am) (ascending : Bool) :
    crtDirectMachineReverseCost (K := K) Tm c a ascending ≤
      crtReverseBudget Tm (∑ i, a i) c (d + 1) am := by
  have hlen : (crtDirectMachineOrder (d := d + 1) ascending).length = d + 1 := by
    cases ascending <;> simp [crtDirectMachineOrder, crtRevAx_full]
  have h := crtReverseFull_cost_le (A := prime + K) a Tm c am ha
    (crtDirectMachineOrder ascending)
  simpa only [crtDirectMachineReverseCost, crtDirectMachineOrder_width,
    crtControl_fullWidth, hlen] using h

def mtCrtDirectFullC (Tm cw : ℕ) : ℝ :=
  mtCrtDirectMachineLoopC Tm cw + mtCrtReverseC Tm cw + 16 * cw + 94

theorem crtDirectMachineFull_pipeline_le (Tm cw K : ℕ) :
    ∀ᶠ n in atTop, ∀ m w c : ℕ, ∀ a s μ : Fin (m + 1) → ℕ,
      m + 1 = d n → (∑ j, a j) = logT n →
      (∀ j, a j = ℓ n ∨ a j = ℓ n - 1) →
      (∀ j, s j ≤ 2 ^ a j) → (∀ j, μ j ≤ s j) →
      w ≤ 3 * logT n + 1 → c ≤ cw * p n →
      (crtDirectMachineFullForwardCost (K := K) Tm (logT n) w c a s μ : ℝ) ≤
        mtCrtDirectFullC Tm cw * totDirectCRT n ∧
      (crtDirectMachineFullInverseCost (K := K) Tm (logT n) w c a s μ : ℝ) ≤
        mtCrtDirectFullC Tm cw * totDirectCRT n := by
  filter_upwards [crtDirectMachineLoop_pipeline_le Tm cw K,
    crtDirectMachineMetadata_pipeline_le, eventually_big] with n hloop hmeta hb m w c a s μ
      hdim hL ha hs hμ hw hc
  have ha' : ∀ i, a i ≤ ℓ n := by intro i; rcases ha i with h | h <;> omega
  have hl := hloop m w c a s μ hdim hL ha hs hμ hw hc
  have hm := hmeta m a s μ hdim hL ha' hs hμ
  have hcore := crtDirectMachineCoreCosts_le (K := K) Tm (logT n) w c a s μ
  have hf := (Nat.cast_le (α := ℝ)).2 (hcore.1.trans (Nat.add_le_add_left hm _))
  have hi := (Nat.cast_le (α := ℝ)).2 (hcore.2.trans (Nat.add_le_add_left hm _))
  have hT : (T n : ℝ) ≤ totDirectCRT n := by
    have hd : (1 : ℝ) ≤ d n := by exact_mod_cast hb.one_le_d
    have := mt_directCRT_dT_le hb
    nlinarith [Nat.cast_nonneg (α := ℝ) (T n)]
  have hTp : (T n : ℝ) * p n ≤ totDirectCRT n := by
    have hd : (1 : ℝ) ≤ d n := by exact_mod_cast hb.one_le_d
    have := mt_directCRT_dTp_le n
    nlinarith [mt_Tp_nonneg n]
  have hLp : logT n ≤ p n := by have := mt_logT_le_b hb; unfold p; omega
  have hscan := (Nat.cast_le (α := ℝ)).2 (crtDirectMachineScanCost_le hc hLp (by exact_mod_cast mt_one_le_p hb))
  have hscan' : (crtDirectMachineScanCost (crtPre a (m + 1)) c : ℝ) ≤
      (16 * cw + 93) * totDirectCRT n := by
    rw [crtControl_fullWidth, hL]
    change (crtDirectMachineScanCost (logT n) c : ℝ) ≤ ((16 * cw + 93) * (T n * p n) : ℕ) at hscan
    push_cast at hscan
    nlinarith
  have hrev (ascending : Bool) : (crtDirectMachineReverseCost (K := K) Tm c a ascending : ℝ) ≤
      mtCrtReverseC Tm cw * totDirectCRT n := by
    have hr := (Nat.cast_le (α := ℝ)).2 (crtDirectMachineReverseCost_le (K := K) Tm c (ℓ n) a ha' ascending)
    rw [hL, hdim] at hr
    exact hr.trans (mt_crt_reverse_le Tm cw hb c (ℓ n) hc le_rfl)
  have hr₁ := hrev false
  have hr₂ := hrev true
  simp only [crtDirectMachineFullForwardCost, crtDirectMachineFullInverseCost, Nat.cast_add]
  push_cast at hf hi
  unfold mtCrtDirectFullC
  constructor <;> nlinarith

/-- The entry constant includes the actual setup and disposal of its outputs. -/
def mtCrtDirectEntryC (Tm cw : ℕ) : ℝ := mtCrtDirectFullC Tm cw + 1

/-- Matching setup, full ready-state execution, and final cleanup together. -/
theorem crtDirectMachineEntry_pipeline_le (Tm cw K : ℕ) :
    ∀ᶠ n in atTop, ∀ m w c : ℕ, ∀ a s μ : Fin (m + 1) → ℕ,
      m + 1 = d n → (∑ j, a j) = logT n →
      (∀ j, a j = ℓ n ∨ a j = ℓ n - 1) →
      (∀ j, s j ≤ 2 ^ a j) → (∀ j, μ j ≤ s j) →
      w ≤ 3 * logT n + 1 → c ≤ cw * p n →
      let setup := crtDirectSetupCost
        (crtEnts (A := prime + K) ((crtRevAx (m + 1)).map a)).length
        (crtEnts (A := prime + K) ((crtRevAx (m + 1)).map s)).length
        (a 0) (crtPre a (m + 1)) c
      let clear := crtDirectSetupClearCost a s c
      ((setup + crtDirectMachineFullForwardCost (K := K) Tm (logT n) w c a s μ + clear : ℕ) : ℝ) ≤
        mtCrtDirectEntryC Tm cw * totDirectCRT n ∧
      ((setup + crtDirectMachineFullInverseCost (K := K) Tm (logT n) w c a s μ + clear : ℕ) : ℝ) ≤
        mtCrtDirectEntryC Tm cw * totDirectCRT n := by
  filter_upwards [crtDirectMachineFull_pipeline_le Tm cw K,
    crtDirectSetup_pipeline_le cw, eventually_big] with n hfull hsetup hb m w c a s μ
      hdim hL ha hs hμ hw hc
  have ha' : ∀ i, a i ≤ ℓ n := by intro i; rcases ha i with h | h <;> omega
  have ha1 : ∀ i, 1 ≤ a i := by
    intro i
    have := hb.two_le_ℓ
    rcases ha i with h | h <;> omega
  have hdimL : m + 1 ≤ logT n := by
    calc
      m + 1 = ∑ _ : Fin (m + 1), 1 := by simp
      _ ≤ ∑ i, a i := Finset.sum_le_sum fun i _ => ha1 i
      _ = _ := hL
  have hrad : ∀ i, s i ≤ r n := fun i =>
    (hs i).trans (Nat.pow_le_pow_right (by decide) (ha' i))
  have hsc := (Nat.cast_le (α := ℝ)).2
    (hsetup m (prime + K) c a s hL.le hdimL hrad hc)
  obtain ⟨hf, hi⟩ := hfull m w c a s μ hdim hL ha hs hμ hw hc
  have hT : (T n : ℝ) ≤ totDirectCRT n := by
    have hd : (1 : ℝ) ≤ d n := by exact_mod_cast hb.one_le_d
    have := mt_directCRT_dT_le hb
    nlinarith [Nat.cast_nonneg (α := ℝ) (T n)]
  dsimp only
  push_cast at hsc ⊢
  unfold mtCrtDirectEntryC
  constructor <;> nlinarith

end
end IntegerMultBounds.MathlibTM2.Cost
