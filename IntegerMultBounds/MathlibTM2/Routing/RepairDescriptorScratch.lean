module

public import IntegerMultBounds.MathlibTM2.Routing.RepairDescriptorClean
public import IntegerMultBounds.MathlibTM2.Routing.RepairWidthFrame

/-! Generated descriptor tables do not touch any scratch, installed target or
record-stream tape needed by actual exact repair. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

theorem repairBlank_descriptorSource (j : Fin repairT) (hj : RepairBlank j)
    (d : RepairDescriptorKey) : j ≠ repairDescriptorSource d := by
  cases d with
  | none => exact repairBlank_extraSource j hj .keyDescriptor
  | some d =>
    rcases d with ⟨off, k⟩
    intro he
    subst j
    rcases hj with hh | he | ⟨r, _, _, _, hr⟩ | ⟨r, _, _, _, _, hr⟩
    · have hb : placedSelectiveHost.Blank (placedSelectiveConfig (.desc off k)) :=
        (SelectiveHost.Blank.map_iff placedSelectiveHost repairRoutingEmbed repairRoutingEmbed_injective _).mp hh
      rcases hb with hm | ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨o, r, hr, _, he⟩ | ⟨c, i, _, hi⟩
      · simp [placedSelectiveHost, placedSelectiveConfig] at hm
      · simp [placedSelectiveHost, placedSelectiveConfig] at hi
      · simp [placedSelectiveHost, placedSelectiveConfig] at hi
      · simp [placedSelectiveHost, placedSelectiveConfig, hr] at he
      · simp [placedSelectiveHost, placedSelectiveConfig] at hi
    · simp [repairDescriptorSource, repairSetupSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole] at he
    · cases r <;> simp [repairKey, repairDescriptorSource, repairSetupSource,
        repairRoutingConfig, placedSelectiveConfig, repairRoutingRole] at hr
    · cases r <;> simp [repairBad, repairDescriptorSource, repairSetupSource,
        repairRoutingConfig, placedSelectiveConfig, repairRoutingRole] at hr

variable {A : ℕ} (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

theorem repairDescriptorBank_core_keep (L : Fin 11 → ℕ)
    (bank : Fin (repairT + (2 * 11 + 12)) → List (Fin (A + 4))) (j : Fin repairT)
    (hj : ∀ d, j ≠ repairDescriptorSource d) :
    descriptorBankGenerated bank (repairDescriptorJobs p X hG hK active s L) (descriptorCore j) =
      bank (descriptorCore j) := by
  apply descriptorBankGenerated_keep
  intro job hjob
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hjob
  exact descriptorCore_injective.ne (hj (repairDescriptorKey k))

theorem repairDescriptorBank_blank (L : Fin 11 → ℕ)
    (bank : Fin (repairT + (2 * 11 + 12)) → List (Fin (A + 4)))
    (hblank : ∀ j, RepairBlank j → bank (descriptorCore j) = []) :
    ∀ j, RepairBlank j →
      descriptorBankGenerated bank (repairDescriptorJobs p X hG hK active s L) (descriptorCore j) = [] := by
  intro j hj
  rw [repairDescriptorBank_core_keep p X hG hK active s L bank j (repairBlank_descriptorSource j hj)]
  exact hblank j hj

theorem repairDescriptorBank_targets (L : Fin 11 → ℕ)
    (bank : Fin (repairT + (2 * 11 + 12)) → List (Fin (A + 4)))
    (hempty : ∀ key, bank (descriptorCore (repairSetupTarget key)) = []) :
    ∀ key, descriptorBankGenerated bank (repairDescriptorJobs p X hG hK active s L)
      (descriptorCore (repairSetupTarget key)) = [] := by
  intro key
  rw [repairDescriptorBank_core_keep p X hG hK active s L bank _ (fun d => ?_)]
  · exact hempty key
  · rw [repairDescriptorSource_eq]
    exact (repairSetup_sources _ _).symm

end
end IntegerMultBounds.MathlibTM2.Routing
