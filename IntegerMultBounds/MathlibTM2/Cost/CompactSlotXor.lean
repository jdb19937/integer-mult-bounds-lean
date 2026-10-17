module

public import IntegerMultBounds.MathlibTM2.Cost.CompactRuntime
public import IntegerMultBounds.MathlibTM2.Node.CompactSlotXor
import IntegerMultBounds.MathlibTM2.Node.CompactEncoding
import Mathlib.Tactic.Positivity.Finset

/-! Uniform compact-width cost for the concrete encoded slot-XOR program.
Both codecs and transfers are included; the canonical header bank is supplied
by the caller and restored. The exposed coefficient is a power of two. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData
noncomputable section

theorem compactSlotXorDyadic (T D : ℕ) :
    ∃ e : ℕ, compactRuntimeHostConst T D + 28 ≤ (2:ℝ)^e := by
  have hC := compactRuntimeHostConst_pos T D
  obtain ⟨e,_,he⟩ := exists_nat_pow_near
    (show (1:ℝ) ≤ compactRuntimeHostConst T D+28 by linarith)
    (show (1:ℝ)<2 by norm_num)
  exact ⟨e+1,he.le⟩

/-- Fixed dyadic exponent, independent of the shape, array, widths and row count. -/
def compactSlotXorExponent (T D : ℕ) : ℕ := Classical.choose (compactSlotXorDyadic T D)

/-- Public power-of-two coefficient for the complete encoded compact stage. -/
def compactSlotXorConst (T D : ℕ) : ℝ := 2 ^ compactSlotXorExponent T D

theorem compactSlotXorConst_pos (T D : ℕ) : 0 < compactSlotXorConst T D := by
  unfold compactSlotXorConst
  positivity

/-- The exact node budget, including codecs, is uniform at the local compact width.
The stream length is at most the literal native bit-array volume. -/
theorem compactSlotXorCost_le {s : Shape} (T K D : ℕ) (d : Inputs s)
    (hp : 1<d.stage.f → ActivePrefixStageRuntimeData.Packed d D)
    (length : ℕ) (hlength : length ≤ d.rows*s.recordWidth) :
    (compactSlotXorCost T K D d hp length : ℝ) ≤
      compactSlotXorConst T D * (d.rows*s.recordWidth : ℕ) *
        ((max 1 ((d.stage.f-1)*s.guard) : ℕ) : ℝ)^Parameters.tau := by
  have hV : 1 ≤ d.rows*s.recordWidth := by
    have hp : 0<s.payload := by have := d.hrecord; omega
    exact Nat.mul_pos d.hr (by unfold Shape.recordWidth; positivity)
  have hc : compactSlotXorCost T K D d hp length =
      compactStageHostCost T ActivePrefixStageRuntimeProgram.count 13
        (ActivePrefixStageRuntimeData.cost D d hp) (compactStageBankSize d) + 16*length+12 := by
    unfold compactSlotXorCost
    rw [compactRawWords_length_sum compactRuntimeCount]
    unfold compactStageHostCost
    omega
  have hb := (Classical.choose_spec (compactRuntimeHost_uniform T D)).2 s d hp
  change (_ : ℝ) ≤ compactRuntimeHostConst T D * _ * _ at hb
  have he : (1:ℝ) ≤ ((max 1 ((d.stage.f-1)*s.guard) : ℕ) : ℝ)^Parameters.tau :=
    Real.one_le_rpow (by exact_mod_cast le_max_left 1 ((d.stage.f-1)*s.guard))
      (by norm_num [Parameters.tau])
  have hn : 16*length+12 ≤ 28*(d.rows*s.recordWidth) := by omega
  have hnR : ((16*length+12 : ℕ):ℝ) ≤ 28*(d.rows*s.recordWidth : ℕ) := by exact_mod_cast hn
  have hm := mul_le_mul_of_nonneg_left he
    (show (0:ℝ) ≤ 28*(d.rows*s.recordWidth : ℕ) by positivity)
  have hd : compactRuntimeHostConst T D+28 ≤ compactSlotXorConst T D :=
    Classical.choose_spec (compactSlotXorDyadic T D)
  have hd' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd
    (show (0:ℝ) ≤ (d.rows*s.recordWidth : ℕ) by positivity))
    (show (0:ℝ) ≤ ((max 1 ((d.stage.f-1)*s.guard) : ℕ) : ℝ)^Parameters.tau by positivity)
  rw [hc]
  push_cast at hnR hb hm hd' ⊢
  nlinarith only [hb,hnR,hm,hd']

variable {s : Shape} {T Q K : ℕ} {U F : Type}

/-- Actual encoded slot-XOR execution with a fixed dyadic compact-width coefficient.
Canonical headers, reserved geometry and repair premises remain explicit. -/
theorem compactSlotXor_exec_le {n a₀ k ρ left right rows R r w : ℕ}
    (body : F → Pr F T Q (prime+K) U)
    (hQ : compactRuntimeStates ≤ Q)
    (ι : Fin ActivePrefixStageRuntimeProgram.count → Fin T) (hι : Function.Injective ι)
    (hT : ActivePrefixStageRuntimeProgram.count ≤ T)
    (str tmp : Fin T) (hst : str ≠ tmp) (hstr : ∀ j,ι j≠str) (htmp : ∀ j,ι j≠tmp)
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x y : Fin m) (hxy : x≠y)
    (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (hr : 0<rows) (hrecord : s.bits+1≤s.payload)
    (hA : 4≤prime+K) (hpayload : s.payload=3*(r*w))
    (hvolume : rows*s.recordWidth=(R*2^n)*s.payload)
    (D : ℕ)
    (hp : 1<k → ActivePrefixStageRuntimeData.Packed
      (compactRecursiveInputs layout x y hxy rows hG hGK hr hrecord) D)
    (Z : ZArr (Fin R × Fin r) n)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hL : ∀ j,S.L (ι j)=[]) (hR : S.R str=encZ (prime+K) w Z)
    (htmp0 : S.R tmp=[]) (hpay0 : S.R (ι compactRuntimeRaw)=[])
    (hhdr : ∀ j,j≠compactRuntimeRaw → S.R (ι j)=compactRawWords
      (compactRecursiveInputs layout x y hxy rows hG hGK hr hrecord) (fun _ => false) j) :
    ∃ v', ∃ steps : ℕ, v'.user=v.user ∧
      (steps:ℝ) ≤ compactSlotXorConst T D * (rows*s.recordWidth : ℕ) *
        ((max 1 ((k-1)*s.guard) : ℕ) : ℝ)^Parameters.tau ∧
      Exec body (compactSlotXorProg hQ ι hι hT str tmp) (mk v S) steps
        (mk v' {S with R:=Function.update S.R str (encZ (prime+K) w (pullM (compactRecursiveBits layout) (sxXorCol x y) Z))}) := by
  obtain ⟨v',steps,hu,hm,he⟩ := compactSlotXor_exec body hQ ι hι hT str tmp hst hstr htmp
    layout x y hxy hG hGK hr hrecord hA hpayload hvolume D hp Z v S hL hR htmp0 hpay0 hhdr
  refine ⟨v',steps,hu,?_,he⟩
  have hlength : (encZ (prime+K) w Z).length ≤ rows*s.recordWidth := by
    have h := compactEncoding_length (w:=w) hA Z
    rw [length_toBits,←hpayload,←hvolume] at h
    omega
  exact (Nat.cast_le.mpr hm).trans
    (compactSlotXorCost_le T K D (compactRecursiveInputs layout x y hxy rows hG hGK hr hrecord)
      hp _ hlength)

end
end IntegerMultBounds.MathlibTM2.Cost
