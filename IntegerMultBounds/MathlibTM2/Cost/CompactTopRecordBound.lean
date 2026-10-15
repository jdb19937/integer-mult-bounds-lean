module

public import IntegerMultBounds.MathlibTM2.Cost.CompactTopRowControlBound

/-! Complete piece-record read, dispatch and cleanup overhead from actual piece
validity, keeping the record count explicit for later logarithmic absorption. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

private theorem compactBits_indices {u : ℕ} (hu : 1≤u) (j : ℕ) :
    u≤bits u j ∧ j≤bits u j := by
  induction j with
  | zero => simp [bits]
  | succ j ih =>
    have hb := bits_pos hu j
    have hm := Nat.mul_le_mul_right (bits u j) one_lt_m
    simp only [bits]
    constructor <;> nlinarith only [ih.1,ih.2,hb,hm]

/-- Valid serialized piece headers have no field longer than the address. -/
theorem compactTopPc_header_bounds {ds : ComplexFramedExecution.Directions}
    {K n w R₂ : ℕ} {pc : TopPc} (hK : 1≤K) (h : pc.Ok ds K n w R₂) :
    pc.j≤n ∧ pc.u≤n ∧ pc.a₀≤n ∧ K*bits pc.u pc.j≤n := by
  have hb : bits pc.u pc.j≤n :=
    (Nat.le_mul_of_pos_left _ hK).trans (by have := h.hfit; omega)
  have hi := compactBits_indices h.hu pc.j
  exact ⟨hi.2.trans hb,hi.1.trans hb,by have := h.hfit; omega,by have := h.hfit; omega⟩

/-- All record reads and call cleanup for one piece are explicitly charged. -/
theorem compactTopPcCost_control {ds : ComplexFramedExecution.Directions}
    (cfg : List ℕ) {K n w R₂ : ℕ} {pc : TopPc}
    (hK : 1≤K) (h : pc.Ok ds K n w R₂) :
    compactTopPcCost cfg K pc 0 ≤ topGetCost cfg+16*n+2*R₂+23 := by
  obtain ⟨hj,hu,ha,hwidth⟩ := compactTopPc_header_bounds hK h
  have hrow := h.hR
  unfold compactTopPcCost
  omega

/-- The whole piece loop charges every header, row counter and loop transition. -/
theorem compactTopPcsCost_control {ds : ComplexFramedExecution.Directions}
    (cfg : List ℕ) {K n w R₂ : ℕ} (pcs : List TopPc) (hK : 1≤K)
    (h : ∀ pc∈pcs,pc.Ok ds K n w R₂) :
    compactTopPcsCost cfg K (fun _ => 0) pcs ≤
      pcs.length*(topGetCost cfg+16*n+2*R₂+24)+1 := by
  induction pcs with
  | nil => simp [compactTopPcsCost]
  | cons pc pcs ih =>
    have hc := compactTopPcCost_control cfg hK (h pc (by simp))
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [compactTopPcsCost,List.length_cons]
    nlinarith only [hc,ht]

/-- The actual piece record and its final erasure have linear header length. -/
theorem compactTopPcRecLen_control {ds : ComplexFramedExecution.Directions}
    {K n w R₂ : ℕ} (pcs : List TopPc) (hK : 1≤K)
    (h : ∀ pc∈pcs,pc.Ok ds K n w R₂) :
    topRecLen (topPcRec K pcs) ≤ pcs.length*(4*n+4) := by
  induction pcs with
  | nil => simp [topPcRec,topRecLen]
  | cons pc pcs ih =>
    obtain ⟨hj,hu,ha,hwidth⟩ := compactTopPc_header_bounds hK (h pc (by simp))
    have ht := ih (fun x hx => h x (by simp [hx]))
    have he : topRecLen (topPcRec K (pc::pcs)) =
        pc.j+pc.u+pc.a₀+K*bits pc.u pc.j+4+topRecLen (topPcRec K pcs) := by
      simp [topPcRec,topPcFields,topRecLen]
      omega
    rw [he,List.length_cons]
    nlinarith only [hj,hu,ha,hwidth,ht]

end IntegerMultBounds.MathlibTM2.Cost
