module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynDispatch

/-! The old and compact layer embeddings agree on every legacy register. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Node
noncomputable section

theorem compactMnLayerReg_legacy (i : Fin (nT SXReg)) :
    compactMnLayerReg (compactLegacyReg i)=compactMnLegacyReg (mnLayE i) := by
  have hi : compactLegacyReg i=reg (BReg := CompactHostBReg) .io ↔ i=mnLio := by
    rw [←compactLegacyReg_io]
    exact compactLegacyReg_injective.eq_iff
  by_cases h : i=mnLio
  · subst i
    rw [compactLegacyReg_io,compactMnLayerReg_io,mnLayE_io,compactMnLegacyReg_rg]
  · simp only [compactMnLayerReg,show ¬compactLegacyReg i=LayerMachine.reg .io from fun hz => h (hi.mp hz),
      ite_false,mnLayE_of_ne h,compactMnLegacyReg_lay]
    congr 1
    simp only [compactLegacyReg,compactMapReg,LayerMachine.reg,Equiv.symm_apply_apply]

end
end IntegerMultBounds.MathlibTM2.Fast.Main
