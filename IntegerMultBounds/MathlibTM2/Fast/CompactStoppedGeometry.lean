module

public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedPrecision
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopSelection

/-! Stopping changes recursion metadata, not selected physical addresses.
The shared padded-row divisor remains sufficient because depth only decreases. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
noncomputable section

theorem compactStoppedReservedPcs_eq_map (K a oS B activeOffset J D globalD : ℕ) :
    compactStoppedReservedPcs K a oS B activeOffset J D globalD =
      (compactReservedPcs K a oS B activeOffset J D).map
        (compactStoppedPiece (compactGlobalCutoff globalD)) := by
  unfold compactStoppedReservedPcs compactReservedPcs
  rw [List.map_append]
  by_cases hB : B=0 <;> simp [hB,compactStoppedPiece,rowsAt]

theorem compactStoppedPiece_vals (ρ K cutoff : ℕ) (pc : TopPc) :
    synPcVals ρ K (compactStoppedPiece cutoff pc) = synPcVals ρ K pc := by
  simp only [synPcVals,compactStoppedPiece_bits,compactStoppedPiece_offset]

theorem compactStoppedReservedPcs_vals (ρ K a oS B activeOffset J D globalD R : ℕ) :
    ((compactStoppedReservedPcs K a oS B activeOffset J D globalD).map
      (compactRebasePc R)).flatMap (synPcVals ρ K) =
    ((compactReservedPcs K a oS B activeOffset J D).map
      (compactRebasePc R)).flatMap (synPcVals ρ K) := by
  rw [compactRebasePc_vals,compactRebasePc_vals,compactStoppedReservedPcs_eq_map]
  simp only [List.flatMap_map,Function.comp_def,compactStoppedPiece_vals]

theorem compactStoppedReservedPcs_level {K a oS B activeOffset J D globalD : ℕ}
    (hlevels : synJ D D-1≤J) {pc : TopPc}
    (hpc : pc∈compactStoppedReservedPcs K a oS B activeOffset J D globalD) : pc.j≤J := by
  rw [compactStoppedReservedPcs_eq_map] at hpc
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hpc
  rw [compactStoppedPiece_depth]
  exact (Nat.sub_le _ _).trans (compactReservedPcs_level hlevels ho)

theorem compactStoppedRebasedPcs_ok (ds : ComplexFramedExecution.Directions)
    {K oS B activeOffset J D globalD n w R : ℕ}
    (hR : 0<R) (hdiv : NW^J ∣ R)
    (hlevels : synJ D D-1≤J) (hback : oS+K*B≤n) (hactive : activeOffset+K*D≤n)
    (hw : (((synPcs K 0 D activeOffset J D).map
      (compactStoppedPiece (compactGlobalCutoff globalD))).map
      (fun pc => expZ pc.u ds pc.j)).sum+D≤w) :
    ∀ pc∈(compactStoppedReservedPcs K 0 oS B activeOffset J D globalD).map
      (compactRebasePc R), pc.Ok ds K n w R := by
  intro pc hp
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hp
  exact compactRebasePc_ok
    (compactStoppedReservedPcs_ok ds hlevels hback hactive hw original ho) hR
    (dvd_trans (pow_dvd_pow NW (compactStoppedReservedPcs_level hlevels ho)) hdiv)

end
end IntegerMultBounds.MathlibTM2.Fast
