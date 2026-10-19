module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ext

/-! Arithmetic and stream semantics of splitting a positive unit scaling into
monotone pieces. For modulus Q and fixed positive multiplier c coprime to Q,
the source y belongs to piece floor(c*y/Q). Every output has one admissible
piece and an exact reconstructed source. No tape runtime is asserted here. -/

@[expose] public section

namespace IntegerMultBounds.Machine.ScalingPieces

/-- Reduced output address. -/
def output (Q c y : ℕ) : ℕ := c * y % Q

/-- The quotient discarded by reduction identifies the source stream. -/
def piece (Q c y : ℕ) : ℕ := c * y / Q

/-- Reconstruct a source address from an output and its selected piece. -/
def restore (Q c z j : ℕ) : ℕ := (z + j * Q) / c

theorem output_lt {Q c y : ℕ} (hQ : 0 < Q) : output Q c y < Q := Nat.mod_lt _ hQ

theorem piece_lt {Q c y : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hy : y < Q) :
    piece Q c y < c := by
  apply (Nat.div_lt_iff_lt_mul hQ).mpr
  exact Nat.mul_lt_mul_of_pos_left hy hc

/-- Exact quotient/remainder identity, without wraparound subtraction. -/
theorem decomposition (Q c y : ℕ) : output Q c y + piece Q c y * Q = c * y := by
  simpa only [output,piece,Nat.mul_comm (c * y / Q) Q] using Nat.mod_add_div (c * y) Q

/-- Multiplication by a unit is injective on canonical source addresses. -/
theorem output_injective {Q c : ℕ} (hcop : c.Coprime Q) {x y : ℕ}
    (hx : x < Q) (hy : y < Q) (h : output Q c x = output Q c y) : x = y := by
  have hm : c * x ≡ c * y [MOD Q] := h
  exact (Nat.ModEq.cancel_left_of_coprime hcop.symm hm).eq_of_lt_of_lt hx hy

/-- Every canonical output has a unique canonical source. -/
theorem existsUnique_source {Q c : ℕ} (hQ : 0 < Q) (hcop : c.Coprime Q)
    {z : ℕ} (hz : z < Q) : ∃! y, y < Q ∧ output Q c y = z := by
  let f : Fin Q → Fin Q := fun y => ⟨output Q c y.val,output_lt hQ⟩
  have hi : Function.Injective f := by
    intro x y h
    apply Fin.ext
    exact output_injective hcop x.isLt y.isLt (congrArg Fin.val h)
  obtain ⟨y,hy⟩ := Finite.surjective_of_injective hi ⟨z,hz⟩
  have hyz : output Q c y.val = z := congrArg Fin.val hy
  refine ⟨y.val,⟨y.isLt,hyz⟩,?_⟩
  intro y' hy'
  exact output_injective hcop hy'.1 y.isLt (hy'.2.trans hyz.symm)

/-- An admissible piece is a stream whose affine source reconstruction is integral. -/
def AdmissiblePiece (Q c z j : ℕ) : Prop := j < c ∧ c ∣ z + j * Q

theorem source_piece {Q c : ℕ} (hQ : 0 < Q) (hc : 0 < c) {y : ℕ} (hy : y < Q) :
    AdmissiblePiece Q c (output Q c y) (piece Q c y) := by
  refine ⟨piece_lt hQ hc hy,?_⟩
  rw [decomposition]
  exact dvd_mul_right c y

/-- Divisibility fixes the exact product before any quotient simplification. -/
theorem restore_product {Q c z j : ℕ} (hj : AdmissiblePiece Q c z j) :
    c * restore Q c z j = z + j * Q := Nat.mul_div_cancel' hj.2

theorem restore_lt {Q c z j : ℕ} (_hc : 0 < c) (hz : z < Q)
    (hj : AdmissiblePiece Q c z j) : restore Q c z j < Q := by
  have hp := restore_product hj
  have hjlt := hj.1
  nlinarith

theorem output_restore {Q c z j : ℕ} (hz : z < Q) (hj : AdmissiblePiece Q c z j) :
    output Q c (restore Q c z j) = z := by
  rw [output,restore_product hj,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hz]

theorem piece_restore {Q c z j : ℕ} (hQ : 0 < Q) (hz : z < Q)
    (hj : AdmissiblePiece Q c z j) : piece Q c (restore Q c z j) = j := by
  rw [piece,restore_product hj,Nat.add_mul_div_right _ _ hQ,Nat.div_eq_of_lt hz,zero_add]

/-- The merge step selects exactly one stream for each output address. -/
theorem existsUnique_piece {Q c : ℕ} (hQ : 0 < Q) (hc : 0 < c) (hcop : c.Coprime Q)
    {z : ℕ} (hz : z < Q) : ∃! j, AdmissiblePiece Q c z j := by
  obtain ⟨y,⟨hy,hyz⟩,_⟩ := existsUnique_source hQ hcop hz
  refine ⟨piece Q c y,?_,?_⟩
  · rw [← hyz]
    exact source_piece hQ hc hy
  · intro j hj
    have hrest : restore Q c z j = y :=
      output_injective hcop (restore_lt hc hz hj) hy ((output_restore hz hj).trans hyz.symm)
    rw [← hrest,piece_restore hQ hz hj]

/-- On one quotient piece, reduction preserves the strict source order. -/
theorem output_lt_iff {Q c x y : ℕ} (hc : 0 < c) (hpiece : piece Q c x = piece Q c y) :
    output Q c x < output Q c y ↔ x < y := by
  have hx := decomposition Q c x
  have hy := decomposition Q c y
  rw [hpiece] at hx
  constructor <;> intro h <;> nlinarith

/-- Integral reconstruction preserves strict output order within one piece. -/
theorem restore_lt_iff {Q c z w j : ℕ} (hc : 0 < c)
    (hz : AdmissiblePiece Q c z j) (hw : AdmissiblePiece Q c w j) :
    restore Q c z j < restore Q c w j ↔ z < w := by
  have hp := restore_product hz
  have hq := restore_product hw
  constructor <;> intro h <;> nlinarith

/-- Split a source stream by its quotient piece, preserving encounter order,
then replace each address by its scaled output. -/
def stream (Q c j : ℕ) (xs : List ℕ) : List ℕ :=
  (xs.filter (fun y => decide (piece Q c y = j))).map (output Q c)

end IntegerMultBounds.Machine.ScalingPieces
