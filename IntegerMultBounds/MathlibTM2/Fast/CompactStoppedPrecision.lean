module

public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedReservedPieces
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynSel

/-! Precision of actual stopped records from their freshly computed exponent sum.
No transfer of the old recursive precision hypothesis is assumed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
noncomputable section

theorem compactStoppedSynPcs_ok (ds : ComplexFramedExecution.Directions)
    {K a D oS n w J cutoff : ℕ}
    (hlevels : synJ D D - 1 ≤ J) (hfit : oS + K*D ≤ n)
    (hw : (((synPcs K a D oS J D).map (compactStoppedPiece cutoff)).map
      (fun pc => expZ pc.u ds pc.j)).sum + D ≤ w) :
    ∀ pc ∈ (synPcs K a D oS J D).map (compactStoppedPiece cutoff),
      pc.Ok ds K n w (rowsAt (2^a) J) := by
  intro pc hpc
  obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hpc
  have hgeo := compactSynPcs_ok ds hlevels hfit (le_refl
    (synE (gateCount (program ds)) (factorCount (program ds)) D D + D)) original horiginal
  have hleaf : (compactStoppedPiece cutoff original).u ≤ D := by
    obtain ⟨j, _, _, rfl⟩ := mem_synPcs horiginal
    change synDg D j * m^(min j cutoff) ≤ D
    calc
      _ ≤ synDg D j * m^j := Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by norm_num [m]) (min_le_left _ _))
      _ ≤ D := by
        have h : D % m^j + synDg D j * m^j ≤ D := by
          rw [← mod_pow_succ_dg]
          exact Nat.mod_le _ _
        exact le_trans (Nat.le_add_left _ _) h
  refine ⟨one_le_mul hgeo.hu (Nat.one_le_pow _ _ m_pos), ?_, ?_, ?_,
    compactStoppedPiece_fit hgeo.hfit⟩
  · rw [compactStoppedPiece,rowsAt_eq]
    exact one_le_mul (Nat.one_le_pow _ _ (NeZero.pos NW)) hgeo.hR₀
  · rw [compactStoppedPiece_rows]
    exact hgeo.hR
  · intro i hi
    have hexp := expSeq_le_add (gateCount (program ds)) (factorCount (program ds))
      (compactStoppedPiece cutoff original).u hi
    rw [← expZ_eq_expSeq, ← expZ_eq_expSeq] at hexp
    have hsum := List.le_sum_of_mem (List.mem_map_of_mem
      (f := fun pc : TopPc => expZ pc.u ds pc.j)
      (List.mem_map_of_mem (f := compactStoppedPiece cutoff) horiginal))
    omega

theorem compactStoppedReservedPcs_ok (ds : ComplexFramedExecution.Directions)
    {K a oS B activeOffset J D globalD n w : ℕ}
    (hlevels : synJ D D - 1 ≤ J) (hback : oS + K*B ≤ n)
    (hactive : activeOffset + K*D ≤ n)
    (hw : (((synPcs K a D activeOffset J D).map
      (compactStoppedPiece (compactGlobalCutoff globalD))).map
      (fun pc => expZ pc.u ds pc.j)).sum + D ≤ w) :
    ∀ pc ∈ compactStoppedReservedPcs K a oS B activeOffset J D globalD,
      pc.Ok ds K n w (rowsAt (2^a) J) := by
  intro pc hp
  unfold compactStoppedReservedPcs at hp
  rcases List.mem_append.mp hp with hb | ha
  · by_cases hB : B=0
    · simp [hB] at hb
    · simp only [ite_eq_right hB, List.mem_singleton] at hb
      subst pc
      refine ⟨Nat.pos_of_ne_zero hB, ?_, rfl, ?_, ?_⟩
      · rw [rowsAt_eq]
        exact Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne NW)) _) (by positivity)
      · intro i hi
        exact (Nat.not_lt_zero i hi).elim
      · simpa only [bits] using hback
  · exact compactStoppedSynPcs_ok ds hlevels hactive hw pc ha

/-- The exponent carried by the replacement program is exactly the new list's sum. -/
theorem compactStoppedReservedPcs_exp_sum (ds : ComplexFramedExecution.Directions)
    (K a oS B activeOffset J D globalD : ℕ) :
    ((compactStoppedReservedPcs K a oS B activeOffset J D globalD).map
      (fun pc => expZ pc.u ds pc.j)).sum =
    B + (((synPcs K a D activeOffset J D).map
      (compactStoppedPiece (compactGlobalCutoff globalD))).map
      (fun pc => expZ pc.u ds pc.j)).sum := by
  unfold compactStoppedReservedPcs
  rw [List.map_append, List.sum_append]
  by_cases hB : B=0 <;> simp [hB, expZ]

/-- The actual configuration formula has enough precision once its E field is
populated by the replacement constructor's new exponent sum. -/
theorem compactStoppedReservedPcs_config_ok (ds : ComplexFramedExecution.Directions)
    {K a oS B activeOffset J D globalD n W q : ℕ}
    (hlevels : synJ D D - 1 ≤ J) (hback : oS + K*B ≤ n)
    (hactive : activeOffset + K*D ≤ n) (hD : D ≤ globalD) :
    let E := B + (((synPcs K a D activeOffset J D).map
      (compactStoppedPiece (compactGlobalCutoff globalD))).map
      (fun pc => expZ pc.u ds pc.j)).sum
    ∀ pc ∈ compactStoppedReservedPcs K a oS B activeOffset J D globalD,
      pc.Ok ds K n (W+((globalD+1)/2+q+E)+globalD) (rowsAt (2^a) J) := by
  dsimp only
  apply compactStoppedReservedPcs_ok ds hlevels hback hactive
  omega

end
end IntegerMultBounds.MathlibTM2.Fast
