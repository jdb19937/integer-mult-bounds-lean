module

public import IntegerMultBounds.Machine.BinaryAddressOffsetHeaders
public import IntegerMultBounds.Machine.CountedPackedShapeHeaders
public import IntegerMultBounds.Compact.PowerTwoDigits
public import IntegerMultBounds.Machine.BlockRotationData

/-! Literal parity-load offsets in increasing regular address order. Each
q-bit source digit contributes its low bit to the corresponding b-bit output
digit; this is the second modular line of the early-source gadget. -/

@[expose] public section

namespace IntegerMultBounds.Machine.BinaryAddressOffsetData
open BinaryAddressTableData

def source (q n : ℕ) := table (n*q) (2^(n*q))
def dummy (q n : ℕ) := List.replicate (n*2^(n*q)) false
def digit (b : ℕ) (x : Bool) := x :: List.replicate (b-1) false

def word (q b n : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :=
  Gather.gather (fun x _ => x) (PackedArith.parity q b hb hbq) (source q n) (dummy q n) (n*2^(n*q))

@[simp] theorem source_length (q n : ℕ) : (source q n).length=(n*2^(n*q))*q := by
  rw [source,table_length]; ring
@[simp] theorem dummy_length (q n : ℕ) : (dummy q n).length=n*2^(n*q) := List.length_replicate
@[simp] theorem digit_length (b : ℕ) (hb : 1 ≤ b) (x : Bool) : (digit b x).length=b := by
  simp [digit]; omega
@[simp] theorem word_length (q b n : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :
    (word q b n hb hbq).length=(n*2^(n*q))*b := by
  exact Gather.gather_length _ _ _ _ _

theorem table_entry (w N i j : ℕ) (hi : i<N) (hj : j<w) :
    (table w N).getD (i*w+j) false=(row w i).getD j false := by
  have hh := BlockRotationData.flatten_index w ((List.range N).map (row w))
    (by intro xs hx; obtain ⟨k,_,rfl⟩ := List.mem_map.mp hx; exact row_length w k)
    i j (by simpa using hi) hj
  simp only [List.getElem_map,List.getElem_range] at hh
  simp only [table,List.getD_eq_getElem?_getD,hh]

theorem source_entry (q n i j : ℕ) (hi : i<2^(n*q)) (hj : j<n) (hq : 0<q) :
    (source q n).getD ((i*n+j)*q) false=(row (n*q) i).getD (j*q) false := by
  have h := table_entry (n*q) (2^(n*q)) i (j*q) hi (Nat.mul_lt_mul_of_pos_right hj hq)
  simpa only [source,Nat.add_mul,Nat.mul_assoc] using h

end IntegerMultBounds.Machine.BinaryAddressOffsetData
