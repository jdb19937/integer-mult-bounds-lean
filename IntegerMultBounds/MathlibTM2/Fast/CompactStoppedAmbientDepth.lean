module

public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedGlobalPipeline
public import IntegerMultBounds.MathlibTM2.Fast.SynSel

/-! The selected-axis cutoff is conservative relative to ambient dimension.
Its recursion depth obeys the source's (1-beta) logarithmic bound with a fixed
two-level slack, including the small selected-dimension case. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node

private theorem stopped_depth_arithmetic (q L j : ℕ) (hq : 1≤q) (hj : j≤L) :
    q*(j-(L/q-1)) ≤ (q-1)*L+2*q := by
  have hrem := Nat.mod_lt L (by omega : 0<q)
  have heq := Nat.mod_add_div L q
  have hqeq : q-1+1=q := by omega
  by_cases hzero : L/q=0
  · simp only [hzero,Nat.zero_sub,Nat.sub_zero]
    simp only [hzero,mul_zero,add_zero] at heq
    have hL : L<q := by omega
    nlinarith
  · have hc : L/q-1+1=L/q := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hzero)
    by_cases hjc : j≤L/q-1
    · rw [Nat.sub_eq_zero_of_le hjc]
      simp
    · have hj' : j-(L/q-1)+(L/q-1)=j := Nat.sub_add_cancel (by omega)
      nlinarith

theorem compactGlobalCutoff_ambient_depth (D d j : ℕ) (hD : D≤d)
    (hj : j≤Nat.log m D) :
    selectedStopDen*(j-compactGlobalCutoff D) ≤
      (selectedStopDen-1)*Nat.log m d+2*selectedStopDen := by
  have h := stopped_depth_arithmetic selectedStopDen (Nat.log m D) j
    (by norm_num [selectedStopDen]) hj
  have hlog : Nat.log m D≤Nat.log m d := Nat.log_mono_right hD
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hlog) _)

/-- Every emitted active record satisfies the ambient depth bound. -/
theorem compactStoppedGlobalPipeline_ambient_depth (K X oS J active D d t : ℕ)
    (hactive : active≤D) (hD : D≤d) (pc : TopPc)
    (hpc : pc∈(synPcs K X active oS J t).map (compactStoppedPiece (compactGlobalCutoff D))) :
    selectedStopDen*pc.j ≤ (selectedStopDen-1)*Nat.log m d+2*selectedStopDen := by
  obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hpc
  obtain ⟨j, hj, hnonzero, rfl⟩ := mem_synPcs horiginal
  rw [compactStoppedPiece_depth]
  apply compactGlobalCutoff_ambient_depth D d j hD
  have hpos := synDg_pos_div hnonzero
  have hpow : m^j≤active := (Nat.div_pos_iff).mp hpos |>.2
  exact (Nat.le_log_of_pow_le (by norm_num [m]) hpow).trans (Nat.log_mono_right hactive)

end IntegerMultBounds.MathlibTM2.Fast
