module

public import IntegerMultBounds.MathlibTM2.Cost.CompactTopActualBound
public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedReservedPieces
public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedBackBudget

/-! Source-faithful separate reservation charge. The compact-control source
processes reserved axes individually and applies the stopping recurrence only
to active middle pieces. No selected-beta budget is required of the back leaf.
-/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast CompactGadgetReservationCapacity
noncomputable section

/-- Real reservation rate from the actual ceiling, for any chosen chunk exponent.
The chunk lower bound is the standard integer-root rounding estimate. -/
theorem compactStopped_back_rate (d g K : ℕ) (hd : 0<d) (hK : 0<K) (c : ℝ)
    (hchunk : (d:ℝ)^c ≤ 2*(K:ℝ)) :
    (backChunks d g K:ℝ) ≤ 2*(g:ℝ)*(d:ℝ)^(1-c)+1 := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hKR : (0:ℝ)<K := by exact_mod_cast hK
  have hdim : (d:ℝ) ≤ 2*(K:ℝ)*(d:ℝ)^(1-c) := by
    have h := mul_le_mul_of_nonneg_right hchunk (Real.rpow_nonneg hdR.le (1-c))
    rw [←Real.rpow_add hdR, show c+(1-c)=1 by ring, Real.rpow_one] at h
    exact h
  have hb := (compactStoppedBack_reservation d g K hK).2
  have hbR : (backChunks d g K:ℝ)*(K:ℝ) ≤ (d:ℝ)*(g:ℝ)+(K:ℝ) := by
    exact_mod_cast hb.le
  have hscale := mul_le_mul_of_nonneg_right hdim (Nat.cast_nonneg (α:=ℝ) g)
  apply (mul_le_mul_iff_left₀ hKR).mp
  nlinarith only [hbR,hscale]

/-- The original back leaf is charged once, independently of the stopped active
cost. Both sides use the actual canonical layer cost attached to each record. -/
theorem compactStopped_reserved_cost_split (T : ℕ) (ds : ComplexFramedExecution.Directions)
    (D K X active oS activeOffset B J globalD R n o r w ρ : ℕ)
    (s : CompactGadgetReservationShape.Shape)
    (hr : 1≤r) (hw : 1≤w) (hρ : ρ<s.chunk) (hN : o+n≤r*w)
    (hok : ∀ pc∈(compactStoppedReservedPcs K X oS B activeOffset J active globalD).map
      (compactRebasePc R), pc.Ok ds s.chunk n w R) :
    (((compactStoppedReservedPcs K X oS B activeOffset J active globalD).map
      (compactRebasePc R)).map (compactPieceCostWith T ds D s n o r w ρ)).sum ≤
    512*B*(R*2^(o+n)*(r*w))+
      ((((synPcs K X active activeOffset J active).map
        (compactStoppedPiece (compactGlobalCutoff globalD))).map
        (compactRebasePc R)).map (compactPieceCostWith T ds D s n o r w ρ)).sum := by
  by_cases hb : B=0
  · simp [compactStoppedReservedPcs,hb]
  · have hback : (⟨0,B,R,oS⟩ : TopPc).Ok ds s.chunk n w R := by
      apply hok
      simp [compactStoppedReservedPcs,hb,compactRebasePc]
    have hleaf := compactPieceCost_leaf_with T ds D s n o r w ρ B R oS
      (by omega) hback.hR₀ hr hw hρ hback.hfit hN
    simpa [compactStoppedReservedPcs,hb,compactRebasePc] using
      Nat.add_le_add_right hleaf
        (((((synPcs K X active activeOffset J active).map
          (compactStoppedPiece (compactGlobalCutoff globalD))).map
          (compactRebasePc R)).map (compactPieceCostWith T ds D s n o r w ρ)).sum)

/-- The separately charged back term has the manuscript's reservation exponent
1-c, not its active-recursion leaf exponent. -/
theorem compactStopped_back_cost_rate (d g K V : ℕ) (hd : 0<d) (hK : 0<K) (c : ℝ)
    (hchunk : (d:ℝ)^c ≤ 2*(K:ℝ)) :
    (512*backChunks d g K*V:ℕ) ≤
      (512:ℝ)*(V:ℝ)*(2*(g:ℝ)*(d:ℝ)^(1-c)+1) := by
  have h := mul_le_mul_of_nonneg_left (compactStopped_back_rate d g K hd hK c hchunk)
    (show (0:ℝ)≤512*(V:ℝ) by positivity)
  push_cast
  nlinarith only [h]

/-- For the source's actual rounded power chunk, the reservation budget needs
no supplied chunk-rate or back-leaf-size bound. -/
theorem compactStopped_back_cost_floor (d g V : ℕ) (hd : 1≤d) (c : ℝ) (hc : 0≤c) :
    (512*backChunks d g ⌊(d:ℝ)^c⌋₊*V:ℕ) ≤
      (512:ℝ)*(V:ℝ)*(2*(g:ℝ)*(d:ℝ)^(1-c)+1) := by
  have hp : (1:ℝ)≤(d:ℝ)^c := Real.one_le_rpow (by exact_mod_cast hd) hc
  have hK : 1≤⌊(d:ℝ)^c⌋₊ := (Nat.one_le_floor_iff _).mpr hp
  have hKR : (1:ℝ)≤(⌊(d:ℝ)^c⌋₊:ℝ) := by exact_mod_cast hK
  have hfloor := Nat.lt_floor_add_one ((d:ℝ)^c)
  exact compactStopped_back_cost_rate d g _ V (by omega) (by omega) c (by linarith)

end
end IntegerMultBounds.MathlibTM2.Cost
