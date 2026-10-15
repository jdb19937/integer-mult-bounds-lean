module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynLayerStepPark

/-! The concrete parked state establishes every top register and input invariant. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {A : ℕ}

def compactSynParkedFile
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (io park : List (Fin (A+4))) (N r working K ρ : ℕ) (cfg pfs : List ℕ) :=
  embExt compactLegacyReg
    (synG (synRestFile (synIdle io (topRec cfg ++ park)) N r working K ρ (topRec pfs))
      (fun _ => [])) R

theorem compactSynParkedFile_topRegs
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (io park : List (Fin (A+4))) (N r working K ρ : ℕ) (cfg pfs : List ℕ)
    (shape : CompactGadgetReservationShape.Shape) (o : ℕ)
    (hb : ∀ z,compactBasisRest shape o r z (R (reg (BReg := CompactHostBReg) (.bc (.inl z))))) :
    CompactTopRegs (compactHostBasisRest shape o r)
      (compactSynParkedFile R io park N r working K ρ cfg pfs) N r working K ρ := by
  apply compactSynTopRegs_of_legacy
  · rw [compactSynParkedFile,embExt_comp_e compactLegacyReg_injective]
    exact synRest_topRegs _ _ _ _ _ _ _ _ _ (fun _ => rfl)
  · intro z
    unfold compactSynParkedFile
    rw [embExt_off _ _ (fun i => compactLegacyReg_ne_compact_bc i z)]
    exact hb z

theorem compactSynParkedFile_topIn
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (io park : List (Fin (A+4))) (N r working K ρ : ℕ) (cfg pfs : List ℕ) :
    CompactTopIn (BReg := CompactHostBReg)
      (compactSynParkedFile R io park N r working K ρ cfg pfs) cfg pfs := by
  apply compactSynTopIn_of_legacy
  rw [compactSynParkedFile,embExt_comp_e compactLegacyReg_injective]
  refine ⟨⟨park,?_⟩,?_,?_,?_,?_⟩ <;>
    rw [synG_of_ne (lreg_out (by simp))] <;>
    simp [synRestFile,synIdle,lreg]

end
end IntegerMultBounds.MathlibTM2.Fast
