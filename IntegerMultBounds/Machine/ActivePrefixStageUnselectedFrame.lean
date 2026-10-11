module

public import IntegerMultBounds.Machine.ActivePrefixStageNativeFrameCoordinates

/-! Exact support of the actual runtime XOR mask. Every unselected active bit
is preserved by a physical stage, including bits inside the target chunk. -/

@[expose] public section

namespace IntegerMultBounds.Machine.ActivePrefixStageUnselectedFrame
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageFullSelected (Address geometry)
open ActivePrefixStageRuntimeWord
open ActivePrefixStageRuntimeSelected (destination lowControl highControl)
variable {sh : Shape}

private theorem toggle_other (q : ℕ) (hq : 1≤q) (zs : List Bool) (j : ℕ)
    (hj : j%q≠0) : (Compact.PowerTwo.toggleMask q zs).getD j false=false := by
  induction zs generalizing j with
  | nil => simp [Compact.PowerTwo.toggleMask]
  | cons z zs ih =>
    rw [Compact.PowerTwo.toggleMask_cons]
    have hl : (z::List.replicate (q-1) false).length=q := by simp; omega
    by_cases hlt : j<q
    · rw [List.getD_append _ _ _ _ (by rwa [hl])]
      have hp : 0<j := Nat.pos_of_ne_zero (by
        intro hz
        simp [hz] at hj)
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
      rw [List.getD_cons_succ,zeros_bit]
    · rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega),hl]
      apply ih
      have he : (j-q)%q=j%q := by
        have h := congrArg (fun n => n%q) (Nat.sub_add_cancel (by omega : q≤j))
        simpa only [Nat.add_mod_right] using h
      rwa [he]

/-- If the actual mask changes a bit, that bit is one of the original target
coordinates selected by rho and the node width. -/
theorem mask_support (d : Inputs sh) (i : Address d) (j : ℕ)
    (hj : (mask d i).getD j false≠false) :
    ∃ axis : Fin d.stage.f,j=(geometry d).after+axis.val*sh.chunk := by
  have hq : 1≤sh.chunk := by have hs := d.stage.selectedFits; omega
  have hf := d.stage.positiveWidth
  have hl := low_length d i
  have hm : (Compact.PowerTwo.toggleMask sh.chunk (lowControl d i)).length=
      (d.stage.f-1)*sh.chunk := by
    rw [Compact.PowerTwo.toggleMask_length _ hq,hl]
  have hlo : (geometry d).after≤j := by
    by_contra h
    exact hj (mask_below d i j (by omega))
  have hhi : j<(geometry d).after+(d.stage.f-1)*sh.chunk+1 := by
    by_contra h
    apply hj
    apply mask_above d i j
    change (geometry d).after+(d.stage.f-1)*sh.chunk+1≤j
    omega
  have hread : (mask d i).getD j false=
      (Compact.PowerTwo.toggleMask sh.chunk (lowControl d i)++
        (highControl d i::List.replicate ((geometry d).before-1) false)).getD
          (j-(geometry d).after) false := by
    rw [mask,List.append_assoc,List.getD_append_right _ _ _ _ (by simpa only [List.length_replicate] using hlo),
      List.length_replicate]
  by_cases hlow : j-(geometry d).after<(d.stage.f-1)*sh.chunk
  · have hmod : (j-(geometry d).after)%sh.chunk=0 := by
      by_contra hn
      apply hj
      rw [hread,List.getD_append _ _ _ _ (by rwa [hm])]
      exact toggle_other sh.chunk hq _ _ hn
    have ha : (j-(geometry d).after)/sh.chunk<d.stage.f := by
      apply (Nat.div_lt_iff_lt_mul hq).2
      have hm' := Nat.mul_le_mul_right sh.chunk (by omega : d.stage.f-1≤d.stage.f)
      omega
    refine ⟨⟨(j-(geometry d).after)/sh.chunk,ha⟩,?_⟩
    dsimp only [Fin.val_mk]
    have hd := Nat.mod_add_div (j-(geometry d).after) sh.chunk
    rw [hmod,Nat.zero_add,Nat.mul_comm] at hd
    omega
  · refine ⟨⟨d.stage.f-1,by omega⟩,?_⟩
    dsimp only
    omega

/-- Unselected active bits really survive the implemented target update;
the statement also covers all active spectators outside the target slot. -/
theorem destination_unselected (d : Inputs sh) (i : Address d) (j : ℕ)
    (hj : ¬∃ axis : Fin d.stage.f,j=(geometry d).after+axis.val*sh.chunk) :
    (word d (destination d i)).getD j false=(word d i).getD j false := by
  rw [destination_bit]
  have hm : (mask d i).getD j false=false := by
    by_contra hn
    exact hj (mask_support d i j hn)
  rw [hm,Bool.xor_false]

/-- A physical row-addition preserves every active bit outside all selected
node coordinates, even while the source and target headers change. -/
theorem step_unselected (d : Inputs sh) (op : Networks.BinaryRowProgram.Op (Fin d.stage.slots))
    (i : Fin (d.rows*sh.recordWidth)) (j : ℕ)
    (hj : ¬∃ (slot : Fin d.stage.slots) (axis : Fin d.stage.f),
      j=ActivePrefixStageGeometry.slotLow d.stage slot+(d.stage.rho+axis.val*sh.chunk)) :
    Nat.testBit (ActivePrefixStageRuntimeOrdinal.activeOrdinal sh
      (ActivePrefixStagePairCoordinates.destination d op i)) j=
    Nat.testBit (ActivePrefixStageRuntimeOrdinal.activeOrdinal sh i) j := by
  let input := ActivePrefixStagePairData.changePair d op
  let a := (ActivePrefixStagePairCoordinates.addressEquiv input).symm i
  have hi : ActivePrefixDirtyControlGlobalSwap.index sh (geometry input) a=i :=
    ActivePrefixStagePairCoordinates.index_decode input i
  change Nat.testBit (ActivePrefixStageRuntimeOrdinal.activeOrdinal sh
    (ActivePrefixDirtyControlGlobalSwap.index sh (geometry input) (destination input a))) j=_
  rw [←hi,ActivePrefixStageRuntimeOrdinal.active_at_index,
    ActivePrefixStageRuntimeOrdinal.active_at_index,Compact.PowerTwo.testBit_value,
    Compact.PowerTwo.testBit_value]
  apply destination_unselected input a j
  rintro ⟨axis,he⟩
  apply hj
  refine ⟨op.target,axis,?_⟩
  change j=ActivePrefixStageGeometry.slotLow d.stage op.target+(d.stage.rho+axis.val*sh.chunk)
  change j=ActivePrefixStageGeometry.slotLow d.stage op.target+d.stage.rho+axis.val*sh.chunk at he
  omega

/-- The entire actual chronological word retains all unselected active
spectators; no preservation premise is assumed about any stage. -/
theorem run_unselected (d : Inputs sh) (ops : List (Networks.BinaryRowProgram.Op (Fin d.stage.slots)))
    (i : Fin (d.rows*sh.recordWidth)) (j : ℕ)
    (hj : ¬∃ (slot : Fin d.stage.slots) (axis : Fin d.stage.f),
      j=ActivePrefixStageGeometry.slotLow d.stage slot+(d.stage.rho+axis.val*sh.chunk)) :
    Nat.testBit (ActivePrefixStageRuntimeOrdinal.activeOrdinal sh
      (ActivePrefixStagePairCoordinates.run d ops i)) j=
    Nat.testBit (ActivePrefixStageRuntimeOrdinal.activeOrdinal sh i) j := by
  induction ops generalizing i with
  | nil => rfl
  | cons op ops ih =>
    exact (ih (ActivePrefixStagePairCoordinates.destination d op i)).trans
      (step_unselected d op i j hj)

/-- The same frame equality at native row ordinals eliminates the expanded
codec payload, while retaining the original complete active address field. -/
theorem native_unselected (d : Inputs sh)
    (ops : List (Networks.BinaryRowProgram.Op (Fin d.stage.slots)))
    (r : Fin (ActivePrefixStageTripleWords.count d)) (j : ℕ)
    (hj : ¬∃ (slot : Fin d.stage.slots) (axis : Fin d.stage.f),
      j=ActivePrefixStageGeometry.slotLow d.stage slot+(d.stage.rho+axis.val*sh.chunk)) :
    Nat.testBit ((ActivePrefixStageNativePairCoordinates.run d ops r).val/
      2^(sh.H+sh.B)%2^(sh.active*sh.chunk)) j=
    Nat.testBit (r.val/2^(sh.H+sh.B)%2^(sh.active*sh.chunk)) j := by
  have hp : 0<sh.payload := by have hr := d.hrecord; omega
  have h := run_unselected d ops (ActivePrefixStageNativePairCoordinates.start d r) j hj
  rw [ActivePrefixStageNativePairCoordinates.run_start] at h
  simpa only [ActivePrefixStageRuntimeOrdinal.activeOrdinal,
    ActivePrefixStageNativePairCoordinates.start,Nat.mul_div_cancel _ hp] using h

/-- Every original global address bit outside the selected node coordinates
survives the actual native row permutation, including front and back reserves
and unselected bits between selected coordinates. -/
theorem native_bit_unselected (d : Inputs sh)
    (ops : List (Networks.BinaryRowProgram.Op (Fin d.stage.slots)))
    (r : Fin (ActivePrefixStageTripleWords.count d)) (t : ℕ)
    (ht : ¬∃ (slot : Fin d.stage.slots) (axis : Fin d.stage.f),
      t=sh.H+sh.B+ActivePrefixStageGeometry.slotLow d.stage slot+(d.stage.rho+axis.val*sh.chunk)) :
    Nat.testBit (ActivePrefixStageNativePairCoordinates.run d ops r).val t=
      Nat.testBit r.val t := by
  have hf := ActivePrefixStageNativeFrameCoordinates.native_frame d ops r
  by_cases hlo : t<sh.H+sh.B
  · have h := congrArg (fun n => Nat.testBit n t) hf.2
    simpa only [Nat.testBit_mod_two_pow,hlo,decide_true,Bool.true_and] using h
  by_cases hhi : sh.active*sh.chunk+sh.H+sh.B≤t
  · have h := congrArg
      (fun n => Nat.testBit n (t-(sh.active*sh.chunk+sh.H+sh.B))) hf.1
    rw [Nat.testBit_div_two_pow,Nat.testBit_div_two_pow] at h
    have he : t-(sh.active*sh.chunk+sh.H+sh.B)+(sh.active*sh.chunk+sh.H+sh.B)=t :=
      Nat.sub_add_cancel hhi
    rwa [he] at h
  · have hj : t-(sh.H+sh.B)<sh.active*sh.chunk := by omega
    have h := native_unselected d ops r (t-(sh.H+sh.B)) (by
      rintro ⟨slot,axis,he⟩
      apply ht
      refine ⟨slot,axis,?_⟩
      omega)
    simp only [Nat.testBit_mod_two_pow,hj,decide_true,Bool.true_and,
      Nat.testBit_div_two_pow] at h
    have he : t-(sh.H+sh.B)+(sh.H+sh.B)=t := Nat.sub_add_cancel (by omega)
    rwa [he] at h

end
end IntegerMultBounds.Machine.ActivePrefixStageUnselectedFrame
