module

public import IntegerMultBounds.Machine.ActivePrefixSelectedOffsetData
public import IntegerMultBounds.Machine.BinaryVaryingParityOnlyGather
import IntegerMultBounds.Machine.GatherStreamData
import IntegerMultBounds.Compact.KeyValue
import Mathlib.Tactic.Positivity.Finset
import IntegerMultBounds.Compact.PowerTwoDigits

/-! Literal pure-parity offsets from the current full prefix-address target
field and physically extracted source controls. The emitted rows are the pure-parity second-load offsets. -/

@[expose] public section

namespace IntegerMultBounds.Machine.ActivePrefixParityOnlyData

def offsets (W startT startX q b rho n f : ℕ) (hT : startT+n*q≤W) (hX : startX+f*q≤W)
    (hb : 1≤b) (hbq : b+1≤q) :=
  BinaryVaryingParityOnlyGather.word q b hb hbq (BinaryPrefixFieldTableData.word W startT (n*q) hT)
    (SelectedSourceBitsStreamData.selected (BinaryPrefixFieldTableData.word W startX (f*q) hX)
      q rho n f (2^W))

theorem offsets_length (W startT startX q b rho n f : ℕ)
    (hT : startT+n*q≤W) (hX : startX+f*q≤W) (hb : 1≤b) (hbq : b+1≤q) :
    (offsets W startT startX q b rho n f hT hX hb hbq).length=2^W*(n*b) := by
  simp [offsets,Nat.mul_assoc]

/-- Each physical pure-parity row reads its own current target and source. -/
theorem offset_row (W startT startX q b rho n f i : ℕ)
    (hT : startT+n*q≤W) (hX : startX+f*q≤W) (hb : 1≤b) (hbq : b+1≤q)
    (hnf : n+1=f) (hr : rho<q) (hi : i<2^W) :
    Gather.field (offsets W startT startX q b rho n f hT hX hb hbq) (i*(n*b)) (n*b)=
      Gather.gather (fun x _ => x) (PackedArith.parity q b hb hbq)
        (Gather.field (BinaryAddressTableData.row W i) startT (n*q))
        (ActivePrefixSelectedOffsetData.controls W startX q rho n f i) n := by
  unfold offsets BinaryVaryingParityOnlyGather.word
  rw [ActivePrefixSelectedOffsetData.extracted_controls W startX q rho n f hX hnf hr,
    BinaryPrefixFieldTableData.word_rows]
  exact GatherStreamData.field_eq (fun x _ => x) (PackedArith.parity q b hb hbq) (by exact hb) n (2^W) i
    _ _ (by intro k hk; exact Gather.field_length _ _ _)
    (by intro k hk; exact SelectedSourceBitsData.selected_length _ _ _ _) hi

def rows (W startT startX q b rho n f : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  (List.range (2^W)).map (fun i => Gather.gather (fun x _ => x) (PackedArith.parity q b hb hbq)
    (Gather.field (BinaryAddressTableData.row W i) startT (n*q))
    (ActivePrefixSelectedOffsetData.controls W startX q rho n f i) n)

@[simp] theorem rows_length (W startT startX q b rho n f : ℕ) (hb : 1≤b) (hbq : b+1≤q) :
    (rows W startT startX q b rho n f hb hbq).length=2^W := by simp [rows]

theorem rows_uniform (W startT startX q b rho n f : ℕ) (hb : 1≤b) (hbq : b+1≤q) :
    BlockRotationData.Uniform (n*b) (rows W startT startX q b rho n f hb hbq) := by
  intro xs hx
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
  simp [Gather.gather_length,PackedArith.parity]

theorem rows_flatten (W startT startX q b rho n f : ℕ)
    (hT : startT+n*q≤W) (hX : startX+f*q≤W) (hb : 1≤b) (hbq : b+1≤q)
    (hnf : n+1=f) (hr : rho<q) :
    (rows W startT startX q b rho n f hb hbq).flatten=
      offsets W startT startX q b rho n f hT hX hb hbq := by
  have he : rows W startT startX q b rho n f hb hbq=
      (List.range (2^W)).map (fun i => Gather.field
        (offsets W startT startX q b rho n f hT hX hb hbq) (i*(n*b)) (n*b)) := by
    apply List.map_congr_left
    intro i hi
    exact (offset_row W startT startX q b rho n f i hT hX hb hbq hnf hr
      (List.mem_range.mp hi)).symm
  rw [he]
  exact GatherStreamData.stream_fields _ (2^W) (n*b)
    (offsets_length W startT startX q b rho n f hT hX hb hbq)

end IntegerMultBounds.Machine.ActivePrefixParityOnlyData
