module

public import IntegerMultBounds.MathlibTM2.Node.CompactGeometry
import Mathlib.Tactic.Positivity.Finset

/-! # Recursive reserved geometry for compact slot-XOR integration

One global native Shape is reused by every recursive child. Left and right active
spectators change the live selected-bit offset without allocating new reservations.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Layer
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters ActivePrefixStageGeometry

noncomputable section

/-- The whole native reservation is present in the live address, with optional unused high bits.
The low offset includes the complete dirty back reservation and the right active spectators. -/
structure CompactRecursiveLayout (s : Shape) (n a₀ k ρ left right : ℕ) : Prop where
  active : s.active = left + m * k + right
  positiveWidth : 0 < k
  widthFits : k ≤ s.axes
  selectedFits : ρ < s.chunk
  lowReserve : a₀ = s.H + s.B + right * s.chunk
  totalFits : s.bits ≤ n

/-- A child occupies one complete parent slot, retaining all other active fields as
spectators in the same global native reservation. -/
theorem CompactRecursiveLayout.child {s : Shape} {n a₀ k ρ left right : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (p : Fin m)
    (k' : ℕ) (hk' : 0 < k') (hdivide : m*k'=k) :
    CompactRecursiveLayout s n (a₀+p.val*(s.chunk*k)) k' ρ
      (left+(m-1-p.val)*k) (right+p.val*k) where
  active := by
    have hp := p.isLt
    have he : (m-1-p.val)+1+p.val=m := by omega
    have hh := congrArg (fun z => z*k) he
    simp only [Nat.add_mul,Nat.one_mul] at hh
    have ha := layout.active
    omega
  positiveWidth := hk'
  widthFits := by
    have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le p.val) p.isLt
    have hh : k' ≤ k := by nlinarith
    exact hh.trans layout.widthFits
  selectedFits := layout.selectedFits
  lowReserve := by
    have ha := layout.lowReserve
    rw [ha]
    ring
  totalFits := layout.totalFits

/-- The root layout is the zero-spectator instance of the recursive invariant. -/
theorem CompactReservedLayout.toRecursive {s : Shape} {n a₀ k ρ : ℕ}
    (layout : CompactReservedLayout s n a₀ k ρ) : CompactRecursiveLayout s n a₀ k ρ 0 0 :=
  ⟨by simpa using layout.active, layout.positiveWidth,layout.widthFits,layout.selectedFits,
    by simpa using layout.lowReserve,layout.totalFits⟩

/-- Reversing native slot numbers aligns them with the live little-endian columns. -/
def compactRecursiveStage {s : Shape} {n a₀ k ρ left right : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x y : Fin m) (hxy : x ≠ y) : Stage s where
  slots := m
  f := k
  left := left
  right := right
  rho := ρ
  source := x.rev
  target := y.rev
  distinct := fun h => hxy (Fin.rev_injective h)
  activeAxes := by simpa using layout.active.symm
  positiveWidth := layout.positiveWidth
  widthFits := layout.widthFits
  selectedFits := layout.selectedFits

lemma compactRecursiveStage_slotLow {s : Shape} {n a₀ k ρ left right : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x y : Fin m) (hxy : x ≠ y) (j : Fin m) :
    slotLow (compactRecursiveStage layout x y hxy) j.rev = (j.val * k + right) * s.chunk := by
  have hj := j.isLt
  simp [slotLow, lowAxes, compactRecursiveStage, Fin.rev]
  omega

lemma compactRecursiveStage_early {s : Shape} {n a₀ k ρ left right : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x y : Fin m) (hxy : x ≠ y) :
    (compactRecursiveStage layout x y hxy).source.val < (compactRecursiveStage layout x y hxy).target.val ↔
      y.val < x.val := by
  have hx := x.isLt
  have hy := y.isLt
  simp only [compactRecursiveStage, Fin.rev]
  omega

lemma compactRecursiveStage_late {s : Shape} {n a₀ k ρ left right : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x y : Fin m) (hxy : x ≠ y) :
    (compactRecursiveStage layout x y hxy).target.val < (compactRecursiveStage layout x y hxy).source.val ↔
      x.val < y.val := by
  have hx := x.isLt
  have hy := y.isLt
  simp only [compactRecursiveStage, Fin.rev]
  omega

/-- The strengthened reservation invariant implies the original live layout's fit premise. -/
lemma CompactRecursiveLayout.live_fit {s : Shape} {n a₀ k ρ left right : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) : a₀ + m * (s.chunk * k) ≤ n := by
  have h := layout.totalFits
  rw [Shape.bits, layout.active] at h
  rw [layout.lowReserve]
  nlinarith

/-- All live selected bits exist inside the fully reserved address. -/
def compactRecursiveBits {s : Shape} {n a₀ k ρ left right : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) : Fin (m * k) → Fin n := fun i =>
  ⟨a₀ + ρ + s.chunk * i.val, by
    have hi := i.isLt
    have hp := layout.selectedFits
    have hf := layout.live_fit
    have hm := Nat.mul_le_mul_left s.chunk (show i.val + 1 ≤ m * k by omega)
    nlinarith⟩

lemma compactRecursiveBits_injective {s : Shape} {n a₀ k ρ left right : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) : Function.Injective (compactRecursiveBits layout) := by
  intro i j hij
  have hp := layout.selectedFits
  have hv := congrArg Fin.val hij
  simp only [compactRecursiveBits] at hv
  apply Fin.ext
  nlinarith

/-- Native low-to-high selected positions coincide with the live selected-bit embedding. -/
lemma compactRecursiveStage_selected {s : Shape} {n a₀ k ρ left right : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x y : Fin m) (hxy : x ≠ y)
    (j : Fin m) (c : Fin k) :
    s.H + s.B + slotLow (compactRecursiveStage layout x y hxy) j.rev + (ρ + c.val * s.chunk) =
      (compactRecursiveBits layout (bitIdx j c)).val := by
  rw [compactRecursiveStage_slotLow]
  simp [compactRecursiveBits, bitIdx, finProdFinEquiv,layout.lowReserve]
  ring

/-- The native selected-position formula viewed as an actual live address index. -/
def compactRecursiveStageBit {s : Shape} {n a₀ k ρ left right : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x y : Fin m) (hxy : x ≠ y)
    (j : Fin m) (c : Fin k) : Fin n :=
  ⟨s.H + s.B + slotLow (compactRecursiveStage layout x y hxy) j.rev + (ρ + c.val * s.chunk), by
    rw [compactRecursiveStage_selected]
    exact (compactRecursiveBits layout (bitIdx j c)).isLt⟩

lemma compactRecursiveStageBit_eq {s : Shape} {n a₀ k ρ left right : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x y : Fin m) (hxy : x ≠ y)
    (j : Fin m) (c : Fin k) :
    compactRecursiveStageBit layout x y hxy j c = compactRecursiveBits layout (bitIdx j c) := by
  apply Fin.ext
  exact compactRecursiveStage_selected layout x y hxy j c

/-- Full selected XOR described using the native stage's physical bit positions.
Identifying a native machine's result with this map remains a separate endpoint lemma. -/
def compactRecursiveXor {s : Shape} {n a₀ k ρ left right : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x y : Fin m) (hxy : x ≠ y)
    (bits : Fin n → ZMod 2) (t : Fin n) : ZMod 2 :=
  if ht : ∃ c : Fin k, t = compactRecursiveStageBit layout x y hxy y c then
    bits t + bits (compactRecursiveStageBit layout x y hxy x ht.choose)
  else bits t

/-- Native-indexed selected XOR is exactly the live slot-XOR address map. -/
theorem compactRecursiveXor_eq_sxMap {s : Shape} {n a₀ k ρ left right : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x y : Fin m) (hxy : x ≠ y) :
    compactRecursiveXor layout x y hxy = sxMap (compactRecursiveBits layout) x y := by
  funext bits t
  unfold compactRecursiveXor
  split_ifs with ht
  · let c := ht.choose
    have htc : t = compactRecursiveStageBit layout x y hxy y c := ht.choose_spec
    change bits t + bits (compactRecursiveStageBit layout x y hxy x c) = _
    clear_value c
    clear ht
    rw [htc]
    simp only [compactRecursiveStageBit_eq]
    exact (sxMap_apply_y (compactRecursiveBits_injective layout) x y bits c).symm
  · symm
    apply sxMap_apply_ne (compactRecursiveBits_injective layout)
    intro c heq
    apply ht
    exact ⟨c, by simpa only [compactRecursiveStageBit_eq] using heq.symm⟩

/-- The preserved live `pullM` endpoint follows once the native program is identified with
its full selected-index XOR; this equality does not assume a host execution. -/
theorem compactRecursive_pullM {s : Shape} {n a₀ k ρ R r left right : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x y : Fin m) (hxy : x ≠ y)
    (Z : ZArr (Fin R × Fin r) n) :
    pullAddr (compactRecursiveXor layout x y hxy) Z =
      pullM (compactRecursiveBits layout) (sxXorCol x y) Z := by
  rw [compactRecursiveXor_eq_sxMap]
  rfl


private theorem recursiveToggleMask_support (q : ℕ) (hq : 0 < q) (zs : List Bool) (j : ℕ)
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

private theorem recursiveNativeMask_support {s : Shape} (d : ActivePrefixStageFullData.Inputs s)
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
  obtain ⟨c, hc⟩ := recursiveToggleMask_support s.chunk hq _ _ h
  refine ⟨⟨c.val, by
    have hh : c.val < d.stage.f-1 := by simpa only [hl] using c.isLt
    exact lt_of_lt_of_le hh (Nat.sub_le _ _)⟩, ?_⟩
  change j - after d.stage = c.val*s.chunk at hc
  change j = after d.stage + c.val*s.chunk
  omega

/-- Original native inputs with the reversed slot numbering fixed by the reservation. -/
def compactRecursiveInputs {s : Shape} {n a₀ k ρ left right : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x y : Fin m) (hxy : x ≠ y)
    (rows : ℕ) (hG : 1 ≤ s.guard) (hGK : s.guard+1 ≤ s.chunk)
    (hr : 0 < rows) (hrecord : s.bits+1 ≤ s.payload) : ActivePrefixStageFullData.Inputs s where
  stage := compactRecursiveStage layout x y hxy
  rows := rows
  hG := hG
  hGK := hGK
  hr := hr
  hrecord := hrecord

private theorem nativeOrdinal_high {s : Shape} (d : ActivePrefixStageFullData.Inputs s)
    (i : ActivePrefixStageFullSelected.Address d) (t : ℕ)
    (ht : s.H+s.B+s.active*s.chunk ≤ t) :
    Nat.testBit ((ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d)
        (ActivePrefixStageRuntimeSelected.destination d i)).val / s.payload) t =
      Nat.testBit ((ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d) i).val / s.payload) t := by
  have hbits : compactNativeBits (n:=t+1) d (ActivePrefixStageRuntimeSelected.destination d i) ⟨t,by omega⟩ =
      compactNativeBits (n:=t+1) d i ⟨t,by omega⟩ := by
    simp only [compactNativeBits,ite_eq_right (show ¬t<s.H+s.B by omega),ite_eq_right (Nat.not_lt.mpr ht)]
    rw [ActivePrefixStageRuntimeSelected.fields]
    rfl
  rw [compactNativeBits_eq_addrBits,compactNativeBits_eq_addrBits] at hbits
  exact Networks.BinaryRowColumns.scalar_injective hbits

section NativeDestination
variable {s : Shape} {n a₀ k ρ left right : ℕ}
variable (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x y : Fin m) (hxy : x ≠ y)
variable (rows : ℕ) (hG : 1 ≤ s.guard) (hGK : s.guard+1 ≤ s.chunk)
variable (hr : 0 < rows) (hrecord : s.bits+1 ≤ s.payload)
local notation "d" => compactRecursiveInputs layout x y hxy rows hG hGK hr hrecord

lemma compactRecursiveNativeBits_selected (i : ActivePrefixStageFullSelected.Address d) (j : Fin m) (c : Fin k) :
    compactNativeBits d i (compactRecursiveBits layout (bitIdx j c)) =
      Networks.BinaryRowColumns.scalar (ActivePrefixStageRuntimeCoordinates.coordinates d i c j.rev) := by
  have hp := selected_inside_slot (d).stage j.rev c
  have ht := original_slot_split (d).stage j.rev
  simp only [compactRecursiveInputs] at hp ht
  have he := compactRecursiveStage_selected layout x y hxy j c
  have hlo : s.H+s.B ≤ (compactRecursiveBits layout (bitIdx j c)).val := by
    rw [←he]; have := layout.lowReserve; omega
  have hhi : (compactRecursiveBits layout (bitIdx j c)).val < s.H+s.B+s.active*s.chunk := by
    rw [←he]
    have := layout.lowReserve
    simp only [compactRecursiveStage] at hp ht ⊢
    simp only [compactRecursiveStage] at he
    omega
  simp only [compactNativeBits,ite_eq_right (Nat.not_lt.mpr hlo),ite_eq_left hhi]
  congr 1
  unfold ActivePrefixStageRuntimeCoordinates.coordinates
  congr 1
  change _ = slotLow (compactRecursiveStage layout x y hxy) j.rev + (ρ+c.val*s.chunk)
  rw [←he]
  have := layout.lowReserve
  omega

/-- The actual runtime destination, including the native highest-bit repair, acts on all
live address bits as `sxMap`. No assumed selected-action premise occurs here. -/
theorem compactRecursiveNativeBits_destination (i : ActivePrefixStageFullSelected.Address d) :
    compactNativeBits d (ActivePrefixStageRuntimeSelected.destination d i) =
      sxMap (compactRecursiveBits layout) x y (compactNativeBits d i) := by
  funext t
  by_cases ht : ∃ c : Fin k, t = compactRecursiveBits layout (bitIdx y c)
  · obtain ⟨c, rfl⟩ := ht
    rw [sxMap_apply_y (compactRecursiveBits_injective layout),
      compactRecursiveNativeBits_selected,compactRecursiveNativeBits_selected,compactRecursiveNativeBits_selected]
    exact congrArg Networks.BinaryRowColumns.scalar
      (ActivePrefixStageRuntimeCoordinates.target d i c) |>.trans (Networks.BinaryRowColumns.scalar_xor _ _)
  · rw [sxMap_apply_ne (compactRecursiveBits_injective layout) x y (compactNativeBits d i) t
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
          obtain ⟨c,hc⟩ := recursiveNativeMask_support d i _ hm
          change t.val-(s.H+s.B) = after (compactRecursiveStage layout x y hxy)+c.val*s.chunk at hc
          apply ht
          refine ⟨c, Fin.ext ?_⟩
          have he := compactRecursiveStage_selected layout x y hxy y c
          have hp := target_selected_position (d).stage c.val
          change after (d).stage+c.val*s.chunk=slotLow (d).stage y.rev+(ρ+c.val*s.chunk) at hp
          change after (compactRecursiveStage layout x y hxy) + c.val*s.chunk =
            slotLow (compactRecursiveStage layout x y hxy) y.rev + (ρ+c.val*s.chunk) at hp
          rw [←he]
          have := layout.lowReserve
          omega
        rw [hm,Bool.xor_false]
      · simp only [ite_eq_right hhi]
        rw [ActivePrefixStageRuntimeSelected.fields]
        rfl

/-- Exact serialized address rank of the real native destination. The volume premise
makes the native outer rows precisely part of the live address rather than extra bits. -/
theorem compactRecursiveNative_destination_rank (hvolume : rows * 2^s.bits ≤ 2^n)
    (i : ActivePrefixStageFullSelected.Address d) :
    (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d)
      (ActivePrefixStageRuntimeSelected.destination d i)).val / s.payload =
      addrNum (sxMap (compactRecursiveBits layout) x y)
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
  exact compactRecursiveNativeBits_destination layout x y hxy rows hG hGK hr hrecord i

/-- The full serialized ordinal keeps its original outer live row and changes only
its n-bit address. No upper bound on the number of native rows is required. -/
theorem compactRecursiveNative_row_rank (i : ActivePrefixStageFullSelected.Address d) :
    (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d)
      (ActivePrefixStageRuntimeSelected.destination d i)).val / s.payload =
      ((ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d) i).val / s.payload / 2^n) * 2^n +
      addrNum (sxMap (compactRecursiveBits layout) x y)
        ((ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d) i).val / s.payload) := by
  let a := (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d) i).val / s.payload
  let b := (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d)
      (ActivePrefixStageRuntimeSelected.destination d i)).val / s.payload
  have hb : addrBits n b = sxMap (compactRecursiveBits layout) x y (addrBits n a) := by
    simpa only [compactNativeBits_eq_addrBits] using
      compactRecursiveNativeBits_destination layout x y hxy rows hG hGK hr hrecord i
  have hlo : b % 2^n = addrNum (sxMap (compactRecursiveBits layout) x y) a := by
    apply addrBits_bijOn.injOn (Nat.mod_lt _ (by positivity)) (addrNum_lt _ _)
    rw [addrBits_addrNum,←hb]
    funext t
    simp only [addrBits,Nat.testBit_mod_two_pow,t.isLt,decide_true,Bool.true_and]
  have hhi : b / 2^n = a / 2^n := by
    apply Nat.eq_of_testBit_eq
    intro t
    rw [Nat.testBit_div_two_pow,Nat.testBit_div_two_pow]
    apply nativeOrdinal_high
    have hh := layout.totalFits
    unfold Shape.bits at hh
    omega
  change b = (a / 2^n)*2^n + _
  calc
    b = (b / 2^n)*2^n + b % 2^n := by simpa only [Nat.mul_comm] using (Nat.div_add_mod b (2^n)).symm
    _ = _ := by rw [hlo,hhi]

/-- Literal live row, address, and payload serialization of the native destination.
The original row and every payload offset survive; only the n-bit address changes. -/
theorem compactRecursiveNative_serialized_rank
    (i : ActivePrefixStageFullSelected.Address d) (u a p : ℕ) (ha : a < 2^n) (hp : p < s.payload)
    (hi : (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d) i).val =
      (u*2^n+a)*s.payload+p) :
    (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d)
      (ActivePrefixStageRuntimeSelected.destination d i)).val =
      (u*2^n+addrNum (sxMap (compactRecursiveBits layout) x y) a)*s.payload+p := by
  have hpos : 0 < s.payload := by omega
  have hinput : (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d) i).val / s.payload =
      u*2^n+a := by rw [hi,ActivePrefixStageRuntimeOrdinal.quotient _ _ _ hpos hp]
  have hbits : addrBits n (u*2^n+a) = addrBits n a := by
    funext t
    simp only [addrBits]
    rw [Nat.mul_comm u,Nat.testBit_two_pow_mul_add _ ha,ite_eq_left t.isLt]
  have hmap : addrNum (sxMap (compactRecursiveBits layout) x y) (u*2^n+a) =
      addrNum (sxMap (compactRecursiveBits layout) x y) a := by simp only [addrNum,hbits]
  have hrank := compactRecursiveNative_row_rank layout x y hxy rows hG hGK hr hrecord i
  rw [hinput,ActivePrefixStageRuntimeOrdinal.quotient _ _ _ (by positivity) ha,hmap] at hrank
  have hmod (j : ActivePrefixStageFullSelected.Address d) :
      (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d) j).val % s.payload = j.payload.val := by
    rw [ActivePrefixStageRuntimeOrdinal.index_factored,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt j.payload.isLt]
  have hip : i.payload.val=p := by
    rw [←hmod i,hi,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hp]
  have hout : (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d)
      (ActivePrefixStageRuntimeSelected.destination d i)).val % s.payload = p := by
    rw [hmod,ActivePrefixStageRuntimeSelected.fields]
    exact hip
  have h := Nat.div_add_mod
    (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d)
      (ActivePrefixStageRuntimeSelected.destination d i)).val s.payload
  rw [hrank,hout] at h
  simpa only [Nat.mul_comm] using h.symm

/-- Exact native entry transport paired with the established live address rank.
Both statements concern the same real runtime destination. -/
theorem compactRecursiveNative_result_entry (hvolume : rows * 2^s.bits ≤ 2^n)
    (array : ActiveRepairLayoutRecordsData.Array s rows)
    (i : ActivePrefixStageFullSelected.Address d) :
    let j := ActivePrefixStageRuntimeSelected.destination d i
    ActivePrefixStageRuntimeData.result d array
        (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d) j) =
      array (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d) i) ∧
    (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d) j).val / s.payload =
      addrNum (sxMap (compactRecursiveBits layout) x y)
        ((ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d) i).val / s.payload) :=
  ⟨ActivePrefixStageRuntimeSelected.entry d array i,
    compactRecursiveNative_destination_rank layout x y hxy rows hG hGK hr hrecord hvolume i⟩


/-- Direct full-stage early branch, with the native order reversed from live slot order. -/
theorem compactRecursiveNative_early_rank (hk : 1 < k) (horder : y.val < x.val)
    (hvolume : rows * 2^s.bits ≤ 2^n) (i : ActivePrefixStageFullSelected.Address d) :
    (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d)
      (ActivePrefixStageFullSelected.earlyDestination d
        ((compactRecursiveStage_early layout x y hxy).mpr horder) i)).val / s.payload =
      addrNum (sxMap (compactRecursiveBits layout) x y)
        ((ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d) i).val / s.payload) := by
  have ho := (compactRecursiveStage_early layout x y hxy).mpr horder
  have hh := compactRecursiveNative_destination_rank layout x y hxy rows hG hGK hr hrecord hvolume i
  simpa only [ActivePrefixStageRuntimeSelected.destination,show 1 < (d).stage.f from hk,dite_eq_left,
    ActivePrefixStageDispatchSelected.destination,show (d).stage.source.val < (d).stage.target.val from ho] using hh

/-- Direct full-stage late branch, with the native order reversed from live slot order. -/
theorem compactRecursiveNative_late_rank (hk : 1 < k) (horder : x.val < y.val)
    (hvolume : rows * 2^s.bits ≤ 2^n) (i : ActivePrefixStageFullSelected.Address d) :
    (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d)
      (ActivePrefixStageFullSelected.lateDestination d
        ((compactRecursiveStage_late layout x y hxy).mpr horder) i)).val / s.payload =
      addrNum (sxMap (compactRecursiveBits layout) x y)
        ((ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d) i).val / s.payload) := by
  have ho := (compactRecursiveStage_late layout x y hxy).mpr horder
  have hn : ¬(d).stage.source.val < (d).stage.target.val := by
    change (d).stage.target.val < (d).stage.source.val at ho
    omega
  have hh := compactRecursiveNative_destination_rank layout x y hxy rows hG hGK hr hrecord hvolume i
  simpa only [ActivePrefixStageRuntimeSelected.destination,show 1 < (d).stage.f from hk,dite_eq_left,
    ActivePrefixStageDispatchSelected.destination,dite_eq_right hn] using hh

/-- Early native branch with original row and payload coordinates explicit. -/
theorem compactRecursiveNative_early_serialized_rank (hk : 1 < k) (horder : y.val < x.val)
    (i : ActivePrefixStageFullSelected.Address d) (u a p : ℕ) (ha : a < 2^n) (hp : p < s.payload)
    (hi : (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d) i).val =
      (u*2^n+a)*s.payload+p) :
    (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d)
      (ActivePrefixStageFullSelected.earlyDestination d
        ((compactRecursiveStage_early layout x y hxy).mpr horder) i)).val =
      (u*2^n+addrNum (sxMap (compactRecursiveBits layout) x y) a)*s.payload+p := by
  have ho := (compactRecursiveStage_early layout x y hxy).mpr horder
  have hh := compactRecursiveNative_serialized_rank layout x y hxy rows hG hGK hr hrecord i u a p ha hp hi
  simpa only [ActivePrefixStageRuntimeSelected.destination,show 1 < (d).stage.f from hk,dite_eq_left,
    ActivePrefixStageDispatchSelected.destination,show (d).stage.source.val < (d).stage.target.val from ho] using hh

/-- Late native branch with original row and payload coordinates explicit. -/
theorem compactRecursiveNative_late_serialized_rank (hk : 1 < k) (horder : x.val < y.val)
    (i : ActivePrefixStageFullSelected.Address d) (u a p : ℕ) (ha : a < 2^n) (hp : p < s.payload)
    (hi : (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d) i).val =
      (u*2^n+a)*s.payload+p) :
    (ActivePrefixDirtyControlGlobalSwap.index s (ActivePrefixStageFullSelected.geometry d)
      (ActivePrefixStageFullSelected.lateDestination d
        ((compactRecursiveStage_late layout x y hxy).mpr horder) i)).val =
      (u*2^n+addrNum (sxMap (compactRecursiveBits layout) x y) a)*s.payload+p := by
  have ho := (compactRecursiveStage_late layout x y hxy).mpr horder
  have hn : ¬(d).stage.source.val < (d).stage.target.val := by
    change (d).stage.target.val < (d).stage.source.val at ho
    omega
  have hh := compactRecursiveNative_serialized_rank layout x y hxy rows hG hGK hr hrecord i u a p ha hp hi
  simpa only [ActivePrefixStageRuntimeSelected.destination,show 1 < (d).stage.f from hk,dite_eq_left,
    ActivePrefixStageDispatchSelected.destination,dite_eq_right hn] using hh

end NativeDestination

end
end IntegerMultBounds.MathlibTM2.Node
