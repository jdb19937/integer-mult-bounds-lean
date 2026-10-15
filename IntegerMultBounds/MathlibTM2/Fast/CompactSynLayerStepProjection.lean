module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepSources

/-! Exact source projections and compact-bank frames for the chunk-round prefix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {A : ℕ}

def compactSynLayerSourceW (v : SynW → List (Fin (A+4))) (h b K D d g : ℕ) :=
  Function.update (Function.update (Function.update (compactSynChunkSourceOut v h b K D)
    (.s 0) (List.replicate d tick)) (.s 1) (List.replicate g tick)) (.ly 0) [tick]

private theorem compactLegacy_update_comp
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4))) (i : Fin (nT SXReg)) (xs : List (Fin (A+4))) :
    Function.update R (compactLegacyReg i) xs ∘ compactLegacyReg =
      Function.update (R ∘ compactLegacyReg) i xs := by
  funext j
  simp only [Function.comp_apply,Function.update_apply,compactLegacyReg_injective.eq_iff]

lemma compactSynOutsideRow_legacy : compactLegacyReg (sreg (.ly 0))=compactSynOutsideRow := by
  simp only [sreg_eq,compactLegacyReg,compactMapReg_reg,compactMapRegName,compactSynOutsideRow]

lemma compactSynLayerSourcesOut_projection
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (h b K D d g : ℕ) :
    compactSynLayerSourcesOut R Ro v h b K D d g ∘ compactLegacyReg=
      synG Ro (compactSynLayerSourceW v h b K D d g) := by
  simp only [compactSynLayerSourcesOut,←compactSynOutsideRow_legacy,←compactSynScratch_legacy,
    compactLegacy_update_comp,embExt_comp_e compactLegacyReg_injective,
    compactSynLayerSourceW,synG_update]

lemma compactSynLayerSourcesOut_compact
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (Ro : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (h b K D d g : ℕ) (z : CompactBReg) :
    compactSynLayerSourcesOut R Ro v h b K D d g
      (reg (BReg := CompactHostBReg) (.bc (.inl z)))=
      R (reg (BReg := CompactHostBReg) (.bc (.inl z))) := by
  have hr : reg (BReg := CompactHostBReg) (.bc (.inl z))≠compactSynOutsideRow := reg_ne (by simp)
  have hs (i : Fin 32) : reg (BReg := CompactHostBReg) (.bc (.inl z))≠compactSynScratch i := reg_ne (by simp)
  simp only [compactSynLayerSourcesOut,Function.update_of_ne hr,Function.update_of_ne (hs 0),
    Function.update_of_ne (hs 1)]
  exact embExt_off _ _ (fun i => compactLegacyReg_ne_compact_bc i z)

end
end IntegerMultBounds.MathlibTM2.Fast
