module

public import IntegerMultBounds.MathlibTM2.Node.SlotXor
public import IntegerMultBounds.Machine.ActivePrefixStageRuntimeOrdinal
import Mathlib.Tactic.Positivity.Finset

/-! # Reserved geometry for compact slot-XOR integration

The native compact stage numbers slots from the high end; the live layer numbers them from
the low end. Its front reservations occupy the high address bits, while the dirty back
reservation is below the live active region. This file states the extra space invariant
explicitly; the existing unrestricted slot-XOR contract does not imply it.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Layer
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters ActivePrefixStageGeometry

noncomputable section

/-- The whole native reservation is present in the live address, with optional unused high bits.
The low offset is fixed by the complete dirty back reservation, not by zero padding. -/
structure CompactReservedLayout (s : Shape) (n a₀ k ρ : ℕ) : Prop where
  active : s.active = m * k
  positiveWidth : 0 < k
  widthFits : k ≤ s.axes
  selectedFits : ρ < s.chunk
  lowReserve : a₀ = s.H + s.B
  totalFits : s.bits ≤ n

/-- Reversing native slot numbers aligns them with the live little-endian columns. -/
def compactReservedStage {s : Shape} {n a₀ k ρ : ℕ}
    (layout : CompactReservedLayout s n a₀ k ρ) (x y : Fin m) (hxy : x ≠ y) : Stage s where
  slots := m
  f := k
  left := 0
  right := 0
  rho := ρ
  source := x.rev
  target := y.rev
  distinct := fun h => hxy (Fin.rev_injective h)
  activeAxes := by simpa using layout.active.symm
  positiveWidth := layout.positiveWidth
  widthFits := layout.widthFits
  selectedFits := layout.selectedFits

lemma compactReservedStage_slotLow {s : Shape} {n a₀ k ρ : ℕ}
    (layout : CompactReservedLayout s n a₀ k ρ) (x y : Fin m) (hxy : x ≠ y) (j : Fin m) :
    slotLow (compactReservedStage layout x y hxy) j.rev = j.val * k * s.chunk := by
  have hj := j.isLt
  simp [slotLow, lowAxes, compactReservedStage, Fin.rev]
  omega

/-- The strengthened reservation invariant implies the original live layout's fit premise. -/
lemma CompactReservedLayout.live_fit {s : Shape} {n a₀ k ρ : ℕ}
    (layout : CompactReservedLayout s n a₀ k ρ) : a₀ + m * (s.chunk * k) ≤ n := by
  have h := layout.totalFits
  rw [Shape.bits, layout.active] at h
  rw [layout.lowReserve]
  nlinarith

/-- All live selected bits exist inside the fully reserved address. -/
def compactReservedBits {s : Shape} {n a₀ k ρ : ℕ}
    (layout : CompactReservedLayout s n a₀ k ρ) : Fin (m * k) → Fin n := fun i =>
  ⟨a₀ + ρ + s.chunk * i.val, by
    have hi := i.isLt
    have hp := layout.selectedFits
    have hf := layout.live_fit
    have hm := Nat.mul_le_mul_left s.chunk (show i.val + 1 ≤ m * k by omega)
    nlinarith⟩

lemma compactReservedBits_injective {s : Shape} {n a₀ k ρ : ℕ}
    (layout : CompactReservedLayout s n a₀ k ρ) : Function.Injective (compactReservedBits layout) := by
  intro i j hij
  have hp := layout.selectedFits
  have hv := congrArg Fin.val hij
  simp only [compactReservedBits] at hv
  apply Fin.ext
  nlinarith

/-- Native low-to-high selected positions coincide with the live selected-bit embedding. -/
lemma compactReservedStage_selected {s : Shape} {n a₀ k ρ : ℕ}
    (layout : CompactReservedLayout s n a₀ k ρ) (x y : Fin m) (hxy : x ≠ y)
    (j : Fin m) (c : Fin k) :
    a₀ + slotLow (compactReservedStage layout x y hxy) j.rev + (ρ + c.val * s.chunk) =
      (compactReservedBits layout (bitIdx j c)).val := by
  rw [compactReservedStage_slotLow]
  simp [compactReservedBits, bitIdx, finProdFinEquiv]
  ring


private theorem toggleMask_support (q : ℕ) (hq : 0 < q) (zs : List Bool) (j : ℕ)
    (h : (Compact.PowerTwo.toggleMask q zs).getD j false ≠ false) :
    ∃ c : Fin zs.length, j = c.val * q := by
  induction zs generalizing j with
  | nil => simp [Compact.PowerTwo.toggleMask] at h
  | cons z zs ih =>
    rw [Compact.PowerTwo.toggleMask_cons] at h
    have hl : (z :: List.replicate (q-1) false).length = q := by simp; omega
    by_cases hj : j < q
    · rw [List.getD_append _ _ _ _ (by simpa only [hl] using hj)] at h
      cases j with
      | zero => exact ⟨⟨0, by simp⟩, by simp⟩
      | succ j =>
        simp only [List.getD_cons_succ, ActivePrefixStageRuntimeWord.zeros_bit] at h
        exact (h rfl).elim
    · rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl] at h
      obtain ⟨c, hc⟩ := ih (j-q) h
      refine ⟨⟨c.val+1, by simpa only [List.length_cons] using Nat.succ_lt_succ c.isLt⟩, ?_⟩
      simp only [Nat.add_mul, Nat.one_mul]
      omega

private theorem nativeMask_support {s : Shape} (d : ActivePrefixStageFullData.Inputs s)
    (i : ActivePrefixStageFullSelected.Address d) (j : ℕ)
    (h : (ActivePrefixStageRuntimeWord.mask d i).getD j false ≠ false) :
    ∃ c : Fin d.stage.f, j = after d.stage + c.val * s.chunk := by
  have hq : 0 < s.chunk := by have := d.stage.selectedFits; omega
  have hf := d.stage.positiveWidth
  have hl := ActivePrefixStageRuntimeWord.low_length d i
  have hm := Compact.PowerTwo.toggleMask_length s.chunk hq (ActivePrefixStageRuntimeSelected.lowControl d i)
  by_cases hj : j < after d.stage
  · exact (h (ActivePrefixStageRuntimeWord.mask_below d i j hj)).elim
  by_cases hh : after d.stage + (d.stage.f-1)*s.chunk + 1 ≤ j
  · exact (h (ActivePrefixStageRuntimeWord.mask_above d i j hh)).elim
  by_cases he : j = after d.stage + (d.stage.f-1)*s.chunk
  · exact ⟨⟨d.stage.f-1, by omega⟩, he⟩
  have hr : j-after d.stage < (d.stage.f-1)*s.chunk := by omega
  rw [ActivePrefixStageRuntimeWord.mask, List.append_assoc,
    List.getD_append_right _ _ _ _ (by simp only [List.length_replicate]; exact Nat.le_of_not_gt hj),
    List.length_replicate,
    List.getD_append _ _ _ _ (by rw [hm, hl]; exact hr)] at h
  obtain ⟨c, hc⟩ := toggleMask_support s.chunk hq _ _ h
  refine ⟨⟨c.val, by
    have hh : c.val < d.stage.f-1 := by simpa only [hl] using c.isLt
    exact lt_of_lt_of_le hh (Nat.sub_le _ _)⟩, ?_⟩
  change j - after d.stage = c.val*s.chunk at hc
  change j = after d.stage + c.val*s.chunk
  omega

/-- Original native inputs with the reversed slot numbering fixed by the reservation. -/
def compactReservedInputs {s : Shape} {n a₀ k ρ : ℕ}
    (layout : CompactReservedLayout s n a₀ k ρ) (x y : Fin m) (hxy : x ≠ y)
    (rows : ℕ) (hG : 1 ≤ s.guard) (hGK : s.guard+1 ≤ s.chunk)
    (hr : 0 < rows) (hrecord : s.bits+1 ≤ s.payload) : ActivePrefixStageFullData.Inputs s where
  stage := compactReservedStage layout x y hxy
  rows := rows
  hG := hG
  hGK := hGK
  hr := hr
  hrecord := hrecord

/-- All physical address bits, including complete dirty back and front spectators.
The row ordinal is retained in the high bits when the live address has extra width. -/
def compactNativeBits {s : Shape} {n : ℕ} (d : ActivePrefixStageFullData.Inputs s)
    (i : ActivePrefixStageFullSelected.Address d) : Fin n → ZMod 2 := fun t =>
  Networks.BinaryRowColumns.scalar (
    if t.val < s.H+s.B then Nat.testBit i.back.val t.val
    else if t.val < s.H+s.B+s.active*s.chunk then
      (ActivePrefixStageRuntimeWord.word d i).getD (t.val-(s.H+s.B)) false
    else Nat.testBit (ActivePrefixStageRuntimeOrdinal.front d i) (t.val-(s.H+s.B+s.active*s.chunk)))


/-- The live bits are exactly the binary digits of the physical serialized record ordinal. -/
theorem compactNativeBits_eq_addrBits {s : Shape} {n : ℕ}
    (d : ActivePrefixStageFullData.Inputs s) (i : ActivePrefixStageFullSelected.Address d) :
    compactNativeBits (n:=n) d i = addrBits n
      ((ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d) i).val / s.payload) := by
  funext t
  have hw : Counter.value (ActivePrefixStageRuntimeWord.word d i) < 2^(s.active*s.chunk) := by
    simpa only [ActivePrefixStageRuntimeWord.word_length] using Counter.value_lt (ActivePrefixStageRuntimeWord.word d i)
  have hi := ActivePrefixStageRuntimeOrdinal.index_factored d i
  have hp : 0 < s.payload := by have := d.hrecord; omega
  simp only [addrBits]
  rw [hi,ActivePrefixStageRuntimeOrdinal.quotient _ _ _ hp i.payload.isLt]
  rw [Nat.mul_comm (_ * _ + _) (2^(s.H+s.B)),Nat.testBit_two_pow_mul_add _ i.back.isLt]
  rw [Nat.mul_comm (ActivePrefixStageRuntimeOrdinal.front d i),Nat.testBit_two_pow_mul_add _ hw]
  simp only [Compact.PowerTwo.testBit_value]
  unfold compactNativeBits Networks.BinaryRowColumns.scalar
  by_cases hlo : t.val < s.H+s.B
  · simp only [ite_eq_left hlo]
  · simp only [ite_eq_right hlo]
    by_cases hhi : t.val < s.H+s.B+s.active*s.chunk
    · have hh : t.val-(s.H+s.B) < s.active*s.chunk := by omega
      simp only [ite_eq_left hhi,ite_eq_left hh]
    · have hh : ¬t.val-(s.H+s.B) < s.active*s.chunk := by omega
      simp only [ite_eq_right hhi,ite_eq_right hh]
      rw [Nat.sub_sub]

section NativeDestination
variable {s : Shape} {n a₀ k ρ : ℕ}
variable (layout : CompactReservedLayout s n a₀ k ρ) (x y : Fin m) (hxy : x ≠ y)
variable (rows : ℕ) (hG : 1 ≤ s.guard) (hGK : s.guard+1 ≤ s.chunk)
variable (hr : 0 < rows) (hrecord : s.bits+1 ≤ s.payload)
local notation "d" => compactReservedInputs layout x y hxy rows hG hGK hr hrecord

lemma compactNativeBits_selected (i : ActivePrefixStageFullSelected.Address d) (j : Fin m) (c : Fin k) :
    compactNativeBits d i (compactReservedBits layout (bitIdx j c)) =
      Networks.BinaryRowColumns.scalar (ActivePrefixStageRuntimeCoordinates.coordinates d i c j.rev) := by
  have hp := selected_inside_slot (d).stage j.rev c
  have ht := original_slot_split (d).stage j.rev
  simp only [compactReservedInputs] at hp ht
  have he := compactReservedStage_selected layout x y hxy j c
  have hlo : s.H+s.B ≤ (compactReservedBits layout (bitIdx j c)).val := by
    rw [←he]; have := layout.lowReserve; omega
  have hhi : (compactReservedBits layout (bitIdx j c)).val < s.H+s.B+s.active*s.chunk := by
    rw [←he]
    have := layout.lowReserve
    simp only [compactReservedStage] at hp ht ⊢
    simp only [compactReservedStage] at he
    omega
  simp only [compactNativeBits,ite_eq_right (Nat.not_lt.mpr hlo),ite_eq_left hhi]
  congr 1
  unfold ActivePrefixStageRuntimeCoordinates.coordinates
  congr 1
  change _ = slotLow (compactReservedStage layout x y hxy) j.rev + (ρ+c.val*s.chunk)
  rw [←he]
  have := layout.lowReserve
  omega

/-- The actual runtime destination, including the native highest-bit repair, acts on all
live address bits as `sxMap`. No assumed selected-action premise occurs here. -/
theorem compactNativeBits_destination (i : ActivePrefixStageFullSelected.Address d) :
    compactNativeBits d (ActivePrefixStageRuntimeSelected.destination d i) =
      sxMap (compactReservedBits layout) x y (compactNativeBits d i) := by
  funext t
  by_cases ht : ∃ c : Fin k, t = compactReservedBits layout (bitIdx y c)
  · obtain ⟨c, rfl⟩ := ht
    rw [sxMap_apply_y (compactReservedBits_injective layout),
      compactNativeBits_selected,compactNativeBits_selected,compactNativeBits_selected]
    exact congrArg Networks.BinaryRowColumns.scalar
      (ActivePrefixStageRuntimeCoordinates.target d i c) |>.trans (Networks.BinaryRowColumns.scalar_xor _ _)
  · rw [sxMap_apply_ne (compactReservedBits_injective layout) x y (compactNativeBits d i) t
      (fun c he => ht ⟨c,he.symm⟩)]
    unfold compactNativeBits
    by_cases hlo : t.val < s.H+s.B
    · simp only [ite_eq_left hlo]
      rw [ActivePrefixStageRuntimeSelected.fields]
    · simp only [ite_eq_right hlo]
      by_cases hhi : t.val < s.H+s.B+s.active*s.chunk
      · simp only [ite_eq_left hhi]
        rw [ActivePrefixStageRuntimeWord.destination_bit]
        have hm : (ActivePrefixStageRuntimeWord.mask d i).getD (t.val-(s.H+s.B)) false = false := by
          by_contra hm
          obtain ⟨c,hc⟩ := nativeMask_support d i _ hm
          change t.val-(s.H+s.B) = after (compactReservedStage layout x y hxy)+c.val*s.chunk at hc
          apply ht
          refine ⟨c, Fin.ext ?_⟩
          have he := compactReservedStage_selected layout x y hxy y c
          have hp := target_selected_position (d).stage c.val
          change after (d).stage+c.val*s.chunk=slotLow (d).stage y.rev+(ρ+c.val*s.chunk) at hp
          change after (compactReservedStage layout x y hxy) + c.val*s.chunk =
            slotLow (compactReservedStage layout x y hxy) y.rev + (ρ+c.val*s.chunk) at hp
          rw [←he]
          have := layout.lowReserve
          omega
        rw [hm,Bool.xor_false]
      · simp only [ite_eq_right hhi]
        rw [ActivePrefixStageRuntimeSelected.fields]
        rfl

/-- Exact serialized address rank of the real native destination. The volume premise
makes the native outer rows precisely part of the live address rather than extra bits. -/
theorem compactNative_destination_rank (hvolume : rows * 2^s.bits ≤ 2^n)
    (i : ActivePrefixStageFullSelected.Address d) :
    (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d)
      (ActivePrefixStageRuntimeSelected.destination d i)).val / s.payload =
      addrNum (sxMap (compactReservedBits layout) x y)
        ((ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d) i).val / s.payload) := by
  have hp : 0 < s.payload := by omega
  have hlt (j : ActivePrefixStageFullSelected.Address d) :
      (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d) j).val / s.payload < 2^n := by
    have hj := (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d) j).isLt
    change _ < rows * (2^s.bits*s.payload) at hj
    have hv : (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d) j).val <
        (rows*2^s.bits)*s.payload := by simpa only [Nat.mul_assoc] using hj
    exact lt_of_lt_of_le ((Nat.div_lt_iff_lt_mul hp).mpr hv) hvolume
  apply addrBits_bijOn.injOn (hlt _) (addrNum_lt _ _)
  rw [addrBits_addrNum,←compactNativeBits_eq_addrBits,←compactNativeBits_eq_addrBits]
  exact compactNativeBits_destination layout x y hxy rows hG hGK hr hrecord i

/-- Exact native entry transport paired with the established live address rank.
Both statements concern the same real runtime destination. -/
theorem compactNative_result_entry (hvolume : rows * 2^s.bits ≤ 2^n)
    (array : ActiveRepairLayoutRecordsData.Array s rows)
    (i : ActivePrefixStageFullSelected.Address d) :
    let j := ActivePrefixStageRuntimeSelected.destination d i
    ActivePrefixStageRuntimeData.result d array
        (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d) j) =
      array (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d) i) ∧
    (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d) j).val / s.payload =
      addrNum (sxMap (compactReservedBits layout) x y)
        ((ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d) i).val / s.payload) :=
  ⟨ActivePrefixStageRuntimeSelected.entry d array i,
    compactNative_destination_rank layout x y hxy rows hG hGK hr hrecord hvolume i⟩


end NativeDestination

end
end IntegerMultBounds.MathlibTM2.Node
