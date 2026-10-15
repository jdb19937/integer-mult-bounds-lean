module

public import IntegerMultBounds.MathlibTM2.Fast.SynRec

/-! Rebase a recursive piece at a leaf cutoff. Active addresses and total rows
are unchanged; the exponent belongs to the new recursion and is not identified
with the old exponent. This module does not yet generate cutoff records at runtime. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
noncomputable section

/-- Absorb the first `min pc.j cutoff` levels into each leaf. -/
def compactStoppedPiece (cutoff : ℕ) (pc : TopPc) : TopPc :=
  let s := min pc.j cutoff
  ⟨pc.j-s,pc.u*m^s,rowsAt pc.R₀ s,pc.a₀⟩

lemma compactStoppedPiece_bits (cutoff : ℕ) (pc : TopPc) :
    bits (compactStoppedPiece cutoff pc).u (compactStoppedPiece cutoff pc).j=bits pc.u pc.j := by
  simp only [compactStoppedPiece,bits_eq_mul]
  rw [mul_assoc,←pow_add,Nat.add_sub_of_le (min_le_left _ _)]

lemma compactStoppedPiece_rows (cutoff : ℕ) (pc : TopPc) :
    rowsAt (compactStoppedPiece cutoff pc).R₀ (compactStoppedPiece cutoff pc).j=rowsAt pc.R₀ pc.j := by
  simp only [compactStoppedPiece,rowsAt_eq]
  rw [←mul_assoc,←pow_add,Nat.sub_add_cancel (min_le_left _ _)]

lemma compactStoppedPiece_offset (cutoff : ℕ) (pc : TopPc) :
    (compactStoppedPiece cutoff pc).a₀=pc.a₀ := rfl

lemma compactStoppedPiece_zero (pc : TopPc) : compactStoppedPiece 0 pc=pc := by
  cases pc
  simp [compactStoppedPiece,rowsAt]

lemma compactStoppedPiece_depth (cutoff : ℕ) (pc : TopPc) :
    (compactStoppedPiece cutoff pc).j=pc.j-cutoff := by
  simp only [compactStoppedPiece]
  omega

lemma compactStoppedPiece_leaf_iff (cutoff : ℕ) (pc : TopPc) :
    (compactStoppedPiece cutoff pc).j=0 ↔ pc.j≤cutoff := by
  rw [compactStoppedPiece_depth,Nat.sub_eq_zero_iff_le]

lemma compactStoppedPiece_fit {K n cutoff : ℕ} {pc : TopPc}
    (h : pc.a₀+K*bits pc.u pc.j≤n) :
    (compactStoppedPiece cutoff pc).a₀+
      K*bits (compactStoppedPiece cutoff pc).u (compactStoppedPiece cutoff pc).j≤n := by
  simpa only [compactStoppedPiece_bits,compactStoppedPiece_offset] using h

lemma compactStoppedPiece_padding (cutoff : ℕ) (pc : TopPc) (R : ℕ)
    (h : R≤rowsAt pc.R₀ pc.j) :
    R≤rowsAt (compactStoppedPiece cutoff pc).R₀ (compactStoppedPiece cutoff pc).j := by
  rwa [compactStoppedPiece_rows]

/-- Geometric validity transfers; precision must be proved for the new recursion. -/
theorem compactStoppedPiece_ok {ds : Networks.ComplexFramedExecution.Directions}
    {K n w R cutoff : ℕ} {pc : TopPc} (h : pc.Ok ds K n w R)
    (hTw : ∀ i<(compactStoppedPiece cutoff pc).j,
      expZ (compactStoppedPiece cutoff pc).u ds i≤w) :
    (compactStoppedPiece cutoff pc).Ok ds K n w R := by
  refine ⟨?_,?_,?_,hTw,compactStoppedPiece_fit h.hfit⟩
  · exact one_le_mul h.hu (Nat.one_le_pow _ _ m_pos)
  · rw [compactStoppedPiece,rowsAt_eq]
    exact one_le_mul (Nat.one_le_pow _ _ (NeZero.pos NW)) h.hR₀
  · simpa only [compactStoppedPiece_rows] using h.hR

/-- Serialized address extent is preserved; depth and leaf count are replaced. -/
lemma compactStoppedPiece_fields (cutoff K : ℕ) (pc : TopPc) :
    topPcFields K (compactStoppedPiece cutoff pc)=
      [pc.j-cutoff,pc.u*m^(min pc.j cutoff),pc.a₀,K*bits pc.u pc.j] := by
  unfold topPcFields
  rw [compactStoppedPiece_bits,compactStoppedPiece_depth]
  rfl

end
end IntegerMultBounds.MathlibTM2.Fast
