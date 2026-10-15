module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepPrepare

/-! Derive the actual compact basis shape from initialized globals and round preparation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {A : ℕ}

lemma compactSynLayerRecordsOut_compact
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K W h G F d g : ℕ) (z : CompactBReg) :
    compactSynLayerRecordsOut R Ro v es ℓ K W h G F d g
      (reg (BReg := CompactHostBReg) (.bc (.inl z)))=
      R (reg (BReg := CompactHostBReg) (.bc (.inl z))) := by
  unfold compactSynLayerRecordsOut
  rw [embExt_off _ _ (fun i => compactLegacyReg_ne_compact_bc i z)]
  exact compactSynLayerSourcesOut_compact R Ro v h (layB ℓ K) K es.length d g z

lemma compactSynSourceClear_compact
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4))) (z : CompactBReg) :
    compactSynSourceClearOut R (reg (BReg := CompactHostBReg) (.bc (.inl z)))=
      R (reg (BReg := CompactHostBReg) (.bc (.inl z))) := by
  have hs (i : Fin 32) : reg (BReg := CompactHostBReg) (.bc (.inl z))≠compactSynScratch i := reg_ne (by simp)
  have hr : reg (BReg := CompactHostBReg) (.bc (.inl z))≠compactSynOutsideRow := reg_ne (by simp)
  simp only [compactSynSourceClearOut,Function.update_of_ne hr,Function.update_of_ne (hs 0),
    Function.update_of_ne (hs 1),Function.update_of_ne (hs 7)]

/-- The round's native shape is derived, including its non-row address width. -/
theorem compactSynLayerPrepare_basis
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (es : List ℕ) (ℓ K W l h G F d g payload : ℕ)
    (hK : 0<K) (hfit : CompactReservationFits d g K es.length)
    (hblank : ∀ z : CompactBReg,z≠.work 13 → z≠.work 14 → R (reg (BReg := CompactHostBReg) (.bc (.inl z)))=[])
    (hd : (R (reg (BReg := CompactHostBReg) (.bc (.inl (.work 13))))).length=d)
    (hg : (R (reg (BReg := CompactHostBReg) (.bc (.inl (.work 14))))).length=g) :
    ∀ z,compactBasisRest (compactReservationShape d g K es.length payload)
      (K*((h-layB ℓ K)/K*es.length)) (2^l) z
      (compactSynSourceClearOut (compactSynLayerRefreshOut R Ro v es ℓ K W l h G F d g)
        (reg (BReg := CompactHostBReg) (.bc (.inl z)))) := by
  let R₂ := compactSynLayerRecordsOut R Ro v es ℓ K W h G F d g
  have hoff (z : CompactBReg) : R₂ (reg (BReg := CompactHostBReg) (.bc (.inl z)))=
      R (reg (BReg := CompactHostBReg) (.bc (.inl z))) :=
    compactSynLayerRecordsOut_compact R Ro v es ℓ K W h G F d g z
  have hh := compactBasisRefresh_actual_rest (shape := compactReservationShape d g K es.length payload)
    R₂ d g K es.length (K*((h-layB ℓ K)/K*es.length)) (2^l)
    (by intro z h13 h14; rw [hoff]; exact hblank z h13 h14)
    (by rw [hoff]; exact hd) (by rw [hoff]; exact hg)
    (compactReservation_back d g K es.length payload hK) rfl
    (compactReservation_bits hK hfit) rfl rfl
  intro z
  rw [compactSynSourceClear_compact]
  exact hh (.inl z)

end
end IntegerMultBounds.MathlibTM2.Fast
