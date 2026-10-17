module

public import IntegerMultBounds.Networks.DisjointCircuit
public import Mathlib.Data.BitVec

/-! Fixed-width bitmasks for finite source supports: decoding, bitwise
union and intersection, and singleton masks. -/

@[expose] public section

namespace IntegerMultBounds.Networks.MaskDAG

open DisjointCircuit

variable {width : ℕ}

/-- Source indices represented by the set bits of a fixed-width mask. -/
def decode (mask : BitVec width) : Finset (Fin width) :=
  Finset.univ.filter (fun i => mask.getLsbD i.val)

@[simp] theorem mem_decode (mask : BitVec width) (i : Fin width) :
    i ∈ decode mask ↔ mask.getLsbD i.val = true := by simp [decode]

@[simp] theorem decode_zero : decode (0 : BitVec width) = ∅ := by
  ext i
  simp

@[simp] theorem decode_or (a b : BitVec width) : decode (a ||| b) = decode a ∪ decode b := by
  ext i
  simp

@[simp] theorem decode_and (a b : BitVec width) : decode (a &&& b) = decode a ∩ decode b := by
  ext i
  simp

theorem decode_injective : Function.Injective (decode (width := width)) := by
  intro a b he
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  apply Bool.eq_iff_iff.mpr
  simpa only [mem_decode] using Finset.ext_iff.mp he ⟨i, hi⟩

@[simp] theorem and_eq_zero_iff (a b : BitVec width) :
    a &&& b = 0 ↔ Disjoint (decode a) (decode b) := by
  rw [Finset.disjoint_iff_inter_eq_empty, ← decode_and, ← decode_zero]
  exact ⟨congrArg decode, fun h => decode_injective h⟩

/-- The exact singleton input mask. -/
def singleton (i : Fin width) : BitVec width := BitVec.ofNat width 1 <<< i.val

@[simp] theorem decode_singleton (i : Fin width) : decode (singleton i) = {i} := by
  ext j
  simp only [mem_decode, singleton, BitVec.getLsbD_shiftLeft,
    Finset.mem_singleton, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  have hi := i.isLt
  have hj := j.isLt
  rw [Fin.ext_iff]
  have hone := @BitVec.getLsbD_one width (j.val - i.val)
  rw [hone]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

end IntegerMultBounds.Networks.MaskDAG
