module

public import IntegerMultBounds.MathlibTM2.Routing.RepairWidthInstall
public import IntegerMultBounds.MathlibTM2.Routing.RepairStreamFrame

/-! Generating raw row/mask configuration preserves every blank register and
installed destination required by exact repair. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

noncomputable section

private theorem repairExtraSource_not_image (key : RepairExtra) (i : Fin selectiveT) :
    repairSetupSource (.inr key) ≠ repairRoutingEmbed i := by
  obtain ⟨r, rfl⟩ := (Fintype.equivFin SelectiveReg).surjective i
  change repairSetupSource (.inr key) ≠ repairRoutingEmbed (selectiveReg r)
  rw [repairRoutingEmbed_reg]
  cases r <;> simp [repairSetupSource, repairRoutingRole]

theorem repairBlank_extraSource (j : Fin repairT) (hj : RepairBlank j) (key : RepairExtra) :
    j ≠ repairSetupSource (.inr key) := by
  rcases hj with hh | he | ⟨r, _, _, _, hr⟩ | ⟨r, _, _, _, _, hr⟩
  · have hi : ∃ i : Fin selectiveT, repairRoutingEmbed i = j := by
      rcases hh with hm | ⟨d, he⟩ | ⟨d, he⟩ | ⟨off, r, _, _, he⟩ | ⟨c, r, _, he⟩
      · simp only [repairHost, SelectiveHost.map, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
      · exact ⟨_, he⟩
      · exact ⟨_, he⟩
      · exact ⟨_, he⟩
      · exact ⟨_, he⟩
    obtain ⟨i, rfl⟩ := hi
    exact (repairExtraSource_not_image key i).symm
  · rw [he]; simp [repairSetupSource]
  · rw [← hr]; cases r <;> simp [repairKey, repairSetupSource]
  · rw [← hr]; cases r <;> simp [repairBad, repairSetupSource]

theorem repairWidthGenerated_core_keep {A : ℕ} (p : Layer.CompactGadget.Par) (rb : ℕ)
    (bank : Fin (repairT + 6) → List (Fin (A + 4))) (j : Fin repairT)
    (hr : j ≠ repairSetupSource (.inr .row)) (hm : j ≠ repairSetupSource (.inr .keyMask)) :
    repairWidthGenerated p rb bank (fieldCore j) = bank (fieldCore j) := by
  simp [repairWidthGenerated, fieldCore_injective.eq_iff, hr, hm]

theorem repairWidthGenerated_blank {A : ℕ} (p : Layer.CompactGadget.Par) (rb : ℕ)
    (bank : Fin (repairT + 6) → List (Fin (A + 4)))
    (hblank : ∀ j, RepairBlank j → bank (fieldCore j) = []) :
    ∀ j, RepairBlank j → repairWidthGenerated p rb bank (fieldCore j) = [] := by
  intro j hj
  rw [repairWidthGenerated_core_keep p rb bank j (repairBlank_extraSource j hj .row)
    (repairBlank_extraSource j hj .keyMask)]
  exact hblank j hj

theorem repairWidthGenerated_targets {A : ℕ} (p : Layer.CompactGadget.Par) (rb : ℕ)
    (bank : Fin (repairT + 6) → List (Fin (A + 4)))
    (hempty : ∀ key, bank (fieldCore (repairSetupTarget key)) = []) :
    ∀ key, repairWidthGenerated p rb bank (fieldCore (repairSetupTarget key)) = [] := by
  intro key
  rw [repairWidthGenerated_core_keep p rb bank _ (repairSetup_sources _ _).symm (repairSetup_sources _ _).symm]
  exact hempty key

end
end IntegerMultBounds.MathlibTM2.Routing
