module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynSel
public import IntegerMultBounds.Machine.CompactGlobalRowPadding

/-! Reinterpret the unchanged runtime piece records at the actual padded row count.
The base-row metadata is not serialized; its exact quotient is justified by the
single global padding, rather than assumed to be a power of two. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
noncomputable section

/-- Each level consumes precisely its power of the fixed wire count. -/
noncomputable def compactRebasePc (R : ℕ) (pc : TopPc) : TopPc := {pc with R₀ := R / NW^pc.j}


private theorem compactRebaseMetadata_ok {ds : ComplexFramedExecution.Directions} {K n w R S base : ℕ}
    {pc : TopPc} (h : pc.Ok ds K n w S) (hbase : 1≤base)
    (hrows : R=rowsAt base pc.j) :
    ({pc with R₀:=base} : TopPc).Ok ds K n w R := by
  cases pc with
  | mk j u oldBase a₀ =>
    rcases h with ⟨hu,_,_,hTw,hfit⟩
    exact ⟨hu,hbase,hrows,hTw,hfit⟩


theorem compactRebasePc_ok {ds : ComplexFramedExecution.Directions} {K n w R S : ℕ}
    {pc : TopPc} (h : pc.Ok ds K n w S) (hR : 0<R) (hdiv : NW^pc.j ∣ R) :
    (compactRebasePc R pc).Ok ds K n w R := by
  have hpow : 0 < NW^pc.j := pow_pos NW_pos pc.j
  have hle : NW^pc.j ≤ R := Nat.le_of_dvd hR hdiv
  have hbase : 1 ≤ R / NW^pc.j := Nat.div_pos hle hpow
  have hrows : R = rowsAt (R / NW^pc.j) pc.j := by
    rw [rowsAt_eq]
    exact (Nat.mul_div_cancel' hdiv).symm
  unfold compactRebasePc
  generalize hquot : R / NW^pc.j = base at hbase hrows ⊢
  exact compactRebaseMetadata_ok (base:=base) h hbase hrows


private theorem compactRebaseMetadata_record (K : ℕ) (pcs : List TopPc) (base : TopPc → ℕ) :
    topPcRec K (pcs.map (fun pc => {pc with R₀:=base pc})) = topPcRec K pcs := by
  simp only [topPcRec,List.flatMap_map]
  rfl

/-- Rebased row metadata changes no byte in the emitted record. -/
theorem compactRebasePc_record (R K : ℕ) (pcs : List TopPc) :
    topPcRec K (pcs.map (compactRebasePc R)) = topPcRec K pcs := by
  exact compactRebaseMetadata_record K pcs (fun pc => R / NW^pc.j)


theorem compactReservedPcs_level {K a oS B activeOffset J D : ℕ}
    (hlevels : synJ D D - 1 ≤ J) {pc : TopPc}
    (hpc : pc ∈ compactReservedPcs K a oS B activeOffset J D) : pc.j ≤ J := by
  unfold compactReservedPcs at hpc
  rcases List.mem_append.mp hpc with hb | ha
  · split_ifs at hb with hB
    · simp at hb
    · simp only [List.mem_singleton] at hb
      subst pc
      exact Nat.zero_le J
  · obtain ⟨j,hj,hpos,rfl⟩ := mem_synPcs ha
    have hh := lt_synJ hj (synDg_pos_div hpos)
    change j ≤ J
    omega


/-- All actual piece records act on the same padded row count. -/
theorem compactRebasedPcs_ok (ds : ComplexFramedExecution.Directions)
    {K oS B activeOffset J D n w R : ℕ}
    (hR : 0<R) (hdiv : NW^J ∣ R)
    (hlevels : synJ D D - 1 ≤ J) (hback : oS + K*B ≤ n)
    (hactive : activeOffset + K*D ≤ n)
    (hw : synE (gateCount (program ds)) (factorCount (program ds)) D D + D ≤ w) :
    ∀ pc ∈ (compactReservedPcs K 0 oS B activeOffset J D).map (compactRebasePc R),
      pc.Ok ds K n w R := by
  intro pc hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact compactRebasePc_ok (compactReservedPcs_ok ds hlevels hback hactive hw q hq) hR
    (dvd_trans (pow_dvd_pow NW (compactReservedPcs_level hlevels hq)) hdiv)


/-- Reducing active axes never requires more levels than the original global depth. -/
theorem compactSyn_depth_le {D d : ℕ} (hD : D≤d) :
    synJ D D-1 ≤ CompactGlobalRowPadding.depth m d := by
  by_cases hz : D=0
  · subst D
    simp [synJ,synJk]
  · rw [synJ_self_eq hz,Nat.add_sub_cancel]
    exact (Nat.log_mono_right (b:=m) hD).trans (Nat.log_le_clog m d)

/-- The existing single global pad discharges the shared row-count premise. -/
theorem compactRebasedPcs_initial_ok (ds : ComplexFramedExecution.Directions)
    {K oS B activeOffset D n w d : ℕ} (hK : 0<K)
    (hlevels : synJ D D - 1 ≤ CompactGlobalRowPadding.depth m d)
    (hback : oS + K*B ≤ n) (hactive : activeOffset + K*D ≤ n)
    (hw : synE (gateCount (program ds)) (factorCount (program ds)) D D + D ≤ w) :
    ∀ pc ∈ (compactReservedPcs K 0 oS B activeOffset (CompactGlobalRowPadding.depth m d) D).map
      (compactRebasePc (CompactGlobalRowPadding.initialRows NW m d K)),
      pc.Ok ds K n w (CompactGlobalRowPadding.initialRows NW m d K) := by
  have hc : 0<NW := Nat.pos_of_ne_zero (NeZero.ne NW)
  exact compactRebasedPcs_ok ds (CompactGlobalRowPadding.initial_positive NW m d K hc hK)
    (CompactGlobalRowPadding.initial_bounds NW m d K hc hK).2.2.2
    hlevels hback hactive hw

end
end IntegerMultBounds.MathlibTM2.Fast
