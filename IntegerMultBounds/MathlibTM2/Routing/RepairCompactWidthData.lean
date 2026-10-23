module

public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactData
public import IntegerMultBounds.MathlibTM2.Routing.RepairConfigurationData
public import IntegerMultBounds.MathlibTM2.Routing.RepairWidthData

/-! Initial configuration omitting both the eleven descriptors and the raw
row/key mask. Width generation establishes the descriptor-free contract. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {A : ℕ} (p : Par) (X rb : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

/-- The row and mask updates inside the concrete descriptor bank. -/
def repairCompactWidths (rb wy : ℕ)
    (bank : Fin repairCompactT → List (Fin (A + 4))) :=
  Function.update (Function.update bank (compactDescriptorCore (repairSetupSource (.inr .row))) (binSyms rb 0))
    (compactDescriptorCore (repairSetupSource (.inr .keyMask))) (binSyms wy (maskVal wy id))

theorem repairCompactWidths_project (rb wy : ℕ)
    (bank : Fin repairCompactT → List (Fin (A + 4))) :
    (fun i => repairCompactWidths rb wy bank (compactDescriptorCore i)) =
      repairWidthBank rb wy (fun i => bank (compactDescriptorCore i)) := by
  funext i
  simp only [repairCompactWidths, repairWidthBank, Function.update_apply, compactDescriptorCore_injective.eq_iff]

theorem RepairPendingConfigurationData.compactDescriptorsGenerated {wb wm wp wk R B : ℕ}
    {headers : Fin 2 → Fin 5 → List Bool} (Lw Lg L : Fin 11 → ℕ)
    {bank : Fin repairCompactT → List (Fin (A + 4))}
    (data : RepairPendingConfigurationData p X rb wb wm wp wk R B headers
      (fun i => bank (compactDescriptorCore i)))
    (hblank : ∀ d, bank (compactDescriptorCore (J := 11) (repairDescriptorSource d)) = []) :
    RepairSetupData p X rb hG hK active s wb wm wp wk R B headers
      (fun i => compactDescriptorBankGenerated (repairCompactWidths rb p.wy bank)
        (repairCompactJobs p X hG hK active s Lw Lg L) (compactDescriptorCore i)) := by
  have hw : RepairPendingDescriptorData p X rb wb wm wp wk R B headers
      (fun i => repairCompactWidths rb p.wy bank (compactDescriptorCore i)) := by
    rw [repairCompactWidths_project]
    exact data.widthsGenerated p X rb
  apply hw.compactGenerated p X rb hG hK active s Lw Lg L
  intro d
  have hr : compactDescriptorCore (J := 11) (repairDescriptorSource d) ≠ compactDescriptorCore (repairSetupSource (.inr .row)) :=
    (compactDescriptorCore_injective (J := 11)).ne (repairNonDescriptor_source (.inr .row) trivial d).symm
  have hm : compactDescriptorCore (J := 11) (repairDescriptorSource d) ≠ compactDescriptorCore (repairSetupSource (.inr .keyMask)) :=
    (compactDescriptorCore_injective (J := 11)).ne (repairNonDescriptor_source (.inr .keyMask) trivial d).symm
  simpa only [repairCompactWidths, Function.update_of_ne hr, Function.update_of_ne hm] using hblank d

end
end IntegerMultBounds.MathlibTM2.Routing
