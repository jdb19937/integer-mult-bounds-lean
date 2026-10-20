module

public import IntegerMultBounds.MathlibTM2.Node.CompactBridge

/-!
# The record index of a compact slot XOR

`CxData` collects the numbers of one compact slot XOR: segment length `K`, selected offset `ρ`,
digit length `G`, slot width `k K` (`k` columns), the low reserve `a₀`, the address width `n`,
the start `sT` of the front reserve, the rows `R`, and the record length `B`. The record index
has ten fields, least significant first (`lens`):

* `0`: the compact field `b` (`(k - 1) G` bits) at the bottom of the low reserve;
* `2`, `4`: the lower and the higher of the slots `x`, `y` (`k K` bits each);
* `6`, `8`: the compact fields `t` and `u` at the start of the front reserve;
* `1`, `3`, `5`, `7`, `9`: the gaps between them; the last one also holds the row.

`CxData.OK` lists the conditions on the numbers; under them the fields fit the gadget
(`valid`, `order`), the touched fields lie below the address width (`touched_le`), and column
`c` of slot `j ∈ {x, y}` sits at `posS c` of its field (`slot_bits`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.MathlibTM2.Layer (bitIdx m)

/-- The numbers of one compact slot XOR. -/
structure CxData where
  K : ℕ
  ρ : ℕ
  G : ℕ
  k : ℕ
  a₀ : ℕ
  n : ℕ
  sT : ℕ
  R : ℕ
  B : ℕ
  x : Fin m
  y : Fin m

namespace CxData

variable (d : CxData)

/-- The slot width. -/
def wy : ℕ := d.k * d.K

/-- The compact width. -/
def wc : ℕ := (d.k - 1) * d.G

/-- The lower and the higher slot. -/
def lo : ℕ := min d.x.val d.y.val

def hi : ℕ := max d.x.val d.y.val

/-- The start of the lower and of the higher slot. -/
def sLo : ℕ := d.a₀ + d.lo * d.wy

def sHi : ℕ := d.a₀ + d.hi * d.wy

/-- The row bits. -/
def rb : ℕ := (sxBits d.R).length

/-- The field lengths of the record index. -/
def lens : Fin 10 → ℕ :=
  ![d.wc, d.sLo - d.wc, d.wy, d.sHi - (d.sLo + d.wy), d.wy, d.sT - (d.sHi + d.wy), d.wc, 0, d.wc,
    d.n - (d.sT + 2 * d.wc) + d.rb]

/-- The gadget parameters. -/
def par : Par := ⟨d.K, d.ρ, d.k - 1, d.G, d.K - d.ρ⟩

/-- The gadget fields: `y` in the lower slot field when `y < x`. -/
def fields : Fields 10 :=
  ⟨0, 6, 8, if d.y.val < d.x.val then 2 else 4, if d.y.val < d.x.val then 4 else 2⟩

/-- The conditions on the numbers. -/
structure OK : Prop where
  ρK : d.ρ < d.K
  k1 : 1 ≤ d.k
  G0 : 0 < d.G
  GK : d.G + 1 < d.K
  hxy : d.x ≠ d.y
  low : d.wc ≤ d.a₀
  slots : d.a₀ + m * d.wy ≤ d.sT
  front : d.sT + 2 * d.wc ≤ d.n
  R0 : 0 < d.R
  B1 : 1 ≤ d.B

variable {d}

lemma OK.lo_hi (h : d.OK) : d.lo < d.hi := by
  have := h.hxy
  unfold lo hi
  have : d.x.val ≠ d.y.val := fun e => this (Fin.ext e)
  omega

lemma OK.hi_lt (h : d.OK) : d.hi < m := by unfold hi; exact max_lt d.x.isLt d.y.isLt

lemma OK.offsets (h : d.OK) :
    d.wc ≤ d.sLo ∧ d.sLo + d.wy ≤ d.sHi ∧ d.sHi + d.wy ≤ d.sT := by
  have hlh := h.lo_hi
  have hhm := h.hi_lt
  have h1 := Nat.mul_le_mul_right d.wy (show d.lo + 1 ≤ d.hi by omega)
  have h2 := Nat.mul_le_mul_right d.wy (show d.hi + 1 ≤ m by omega)
  have := h.low
  have := h.slots
  unfold sLo sHi
  rw [Nat.add_mul, Nat.one_mul] at h1 h2
  omega

/-- The offsets of the fields. -/
lemma OK.offs (h : d.OK) :
    fieldOff d.lens 0 = 0 ∧ fieldOff d.lens 2 = d.sLo ∧ fieldOff d.lens 4 = d.sHi ∧
    fieldOff d.lens 6 = d.sT ∧ fieldOff d.lens 8 = d.sT + d.wc ∧
    fieldsLen d.lens = d.n + d.rb := by
  obtain ⟨h1, h2, h3⟩ := h.offsets
  have h4 := h.front
  simp only [Host.fieldOff, fieldsLen, lens, Finset.sum_filter, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.lt_def]
  simp
  omega

lemma OK.wy_eq (h : d.OK) : d.par.wy = d.wy := by
  have := h.k1; have := h.ρK
  unfold Par.wy par wy
  simp only
  obtain ⟨k', hk⟩ : ∃ k', d.k = k' + 1 := ⟨d.k - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul]; omega

lemma par_wc : d.par.wc = d.wc := by unfold Par.wc par wc; ring

/-- The fields fit the gadget. -/
theorem OK.valid (h : d.OK) : d.fields.Valid d.par d.lens where
  lb := by simp [fields, lens, par_wc]
  lt := by simp [fields, lens, par_wc]
  lu := by simp [fields, lens, par_wc]
  ly := by rw [h.wy_eq]; unfold fields; split_ifs <;> simp [lens]
  lx := by rw [h.wy_eq]; unfold fields; split_ifs <;> simp [lens]
  distinct := by unfold fields; split_ifs <;> decide

theorem order : d.fields.Order := by
  unfold fields
  split_ifs <;> exact ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- The touched fields lie below the address width. -/
theorem OK.touched_le (h : d.OK) :
    ∀ g, touched d.fields g → fieldOff d.lens g + d.lens g ≤ d.n := by
  obtain ⟨e0, e2, e4, e6, e8, -⟩ := h.offs
  obtain ⟨h1, h2, h3⟩ := h.offsets
  have := h.front
  rintro g (rfl | rfl | rfl | rfl)
  · simp only [fields] at e0 ⊢; rw [e0]; simp [lens]; omega
  · simp only [fields] at e6 ⊢; rw [e6]; simp [lens]; omega
  · simp only [fields] at e8 ⊢; rw [e8]; simp [lens]; omega
  · simp only [fields]
    split_ifs
    · rw [e2]; simp [lens]; omega
    · rw [e4]; simp [lens]; omega

/-- The selected-bit positions of the slots. -/
def bits (d : CxData) (j : Fin m) (c : Fin d.k) : ℕ := d.a₀ + d.ρ + d.K * (j * d.k + c)

/-- Column `c` of slot `x` and of slot `y` sits at `posS c` of its field. -/
theorem OK.slot_bits (h : d.OK) (c : Fin d.k) :
    d.bits d.y c = fieldOff d.lens d.fields.y + posS d.par c ∧
    d.bits d.x c = fieldOff d.lens d.fields.x + posS d.par c := by
  obtain ⟨-, e2, e4, -⟩ := h.offs
  have hlo : ∀ j : Fin m, d.a₀ + d.ρ + d.K * (j * d.k + c) = d.a₀ + j * d.wy + posS d.par c :=
    fun j => by unfold posS par wy; simp only; ring
  have hx : d.x ≠ d.y := h.hxy
  unfold bits fields
  by_cases hyx : d.y.val < d.x.val
  · simp only [hyx, ↓reduceIte, e2, e4, sLo, sHi, lo, hi, hlo]
    rw [min_eq_right hyx.le, max_eq_left hyx.le]
    exact ⟨rfl, rfl⟩
  · have hxy : d.x.val < d.y.val := by
      have : d.x.val ≠ d.y.val := fun e => hx (Fin.ext e)
      omega
    simp only [hyx, ↓reduceIte, e2, e4, sLo, sHi, lo, hi, hlo]
    rw [min_eq_left hxy.le, max_eq_right hxy.le]
    exact ⟨rfl, rfl⟩

end CxData

end IntegerMultBounds.MathlibTM2.Node
