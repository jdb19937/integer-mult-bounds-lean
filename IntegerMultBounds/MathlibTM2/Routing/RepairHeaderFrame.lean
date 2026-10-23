module

public import IntegerMultBounds.MathlibTM2.Routing.RepairHeaderDataExec
public import IntegerMultBounds.MathlibTM2.Routing.RepairDescriptorScratch

/-! Header generation preserves all auxiliary inputs and raw tapes needed by
classifier-generated exact repair. Only the ten canonical headers change. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {A : ℕ} (p : Par) (X rb R B : ℕ)

theorem repairHeaderPairBank_core_keep (tapes : Fin repairHeaderT → List (Fin (A + 4)))
    (j : Fin repairClassifierT)
    (hj : ∀ c k, j ≠ classifierCore (repairConfigurationCore (repairRoutingConfig (.header c k)))) :
    repairHeaderPairBank p X rb R B repairSharedHeaderBank tapes (sharedHeaderCore j) = tapes (sharedHeaderCore j) := by
  apply repairHeaderPairBank_keep
  intro c k
  rw [repairSharedHeaderBank_header]
  exact sharedHeaderCore_injective.ne (hj c k)

theorem repairHeaderPairBank_classifierAux (tapes : Fin repairHeaderT → List (Fin (A + 4))) (i : Fin 16) :
    repairHeaderPairBank p X rb R B repairSharedHeaderBank tapes (sharedHeaderCore (classifierAux i)) =
      tapes (sharedHeaderCore (classifierAux i)) :=
  repairHeaderPairBank_core_keep p X rb R B tapes _ (fun _ _ => (classifierCore_aux _ i).symm)

theorem repairHeaderPairBank_widthAux (tapes : Fin repairHeaderT → List (Fin (A + 4))) (i : Fin 6) :
    repairHeaderPairBank p X rb R B repairSharedHeaderBank tapes
      (sharedHeaderCore (classifierCore (fieldAux (N := repairDescriptorT) i))) =
    tapes (sharedHeaderCore (classifierCore (fieldAux (N := repairDescriptorT) i))) :=
  repairHeaderPairBank_core_keep p X rb R B tapes _
    (fun _ _ => classifierCore_injective.ne (fieldCore_aux _ i).symm)

theorem repairHeaderPairBank_descriptorAux (tapes : Fin repairHeaderT → List (Fin (A + 4))) (i : Fin (2 * 11 + 12)) :
    repairHeaderPairBank p X rb R B repairSharedHeaderBank tapes
      (sharedHeaderCore (classifierCore (fieldCore (N := repairDescriptorT) (descriptorAux (N := repairT) (J := 11) i)))) =
    tapes (sharedHeaderCore (classifierCore (fieldCore (N := repairDescriptorT) (descriptorAux (N := repairT) (J := 11) i)))) :=
  repairHeaderPairBank_core_keep p X rb R B tapes _
    (fun _ _ => classifierCore_injective.ne (fieldCore_injective.ne (descriptorCore_aux _ i).symm))

theorem repairHeaderPairBank_descriptorReg (tapes : Fin repairHeaderT → List (Fin (A + 4))) (j : Fin 11) (r : BinaryMaskReg) :
    repairHeaderPairBank p X rb R B repairSharedHeaderBank tapes
      (sharedHeaderCore (classifierCore (fieldCore (N := repairDescriptorT) (descriptorBankReg (N := repairT) (J := 11) j r)))) =
    tapes (sharedHeaderCore (classifierCore (fieldCore (N := repairDescriptorT) (descriptorBankReg (N := repairT) (J := 11) j r)))) :=
  repairHeaderPairBank_core_keep p X rb R B tapes _
    (fun _ _ => classifierCore_injective.ne (fieldCore_injective.ne (descriptorCore_reg _ j r).symm))

theorem repairHeaderPairBank_targets (tapes : Fin repairHeaderT → List (Fin (A + 4))) (key : RepairSetupKey) :
    repairHeaderPairBank p X rb R B repairSharedHeaderBank tapes (repairHeaderRawCore (repairSetupTarget key)) =
      tapes (repairHeaderRawCore (repairSetupTarget key)) :=
  repairHeaderPairBank_raw_keep p X rb R B tapes _ (fun c k => (repairSetup_sources (.inl (.header c k)) key).symm)

theorem repairHeaderPairBank_extra (tapes : Fin repairHeaderT → List (Fin (A + 4))) (key : RepairExtra) :
    repairHeaderPairBank p X rb R B repairSharedHeaderBank tapes (repairHeaderRawCore (repairSetupSource (.inr key))) =
      tapes (repairHeaderRawCore (repairSetupSource (.inr key))) := by
  apply repairHeaderPairBank_raw_keep
  intro c k
  simp [repairSetupSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]

theorem repairHeaderPairBank_src (tapes : Fin repairHeaderT → List (Fin (A + 4))) :
    repairHeaderPairBank p X rb R B repairSharedHeaderBank tapes (repairHeaderRawCore repairHost.src) =
      tapes (repairHeaderRawCore repairHost.src) :=
  repairHeaderPairBank_raw_keep p X rb R B tapes _ (fun c k => (repairSetup_source_src (.inl (.header c k))).symm)

theorem repairHeaderPairBank_descriptors (tapes : Fin repairHeaderT → List (Fin (A + 4))) (d : RepairDescriptorKey) :
    repairHeaderPairBank p X rb R B repairSharedHeaderBank tapes (repairHeaderRawCore (repairDescriptorSource d)) =
      tapes (repairHeaderRawCore (repairDescriptorSource d)) := by
  apply repairHeaderPairBank_raw_keep
  intro c k
  cases d with
  | none => simp [repairDescriptorSource, repairSetupSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  | some d =>
    rcases d with ⟨off, j⟩
    simp [repairDescriptorSource, repairSetupSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]

theorem repairBlank_headerSource (j : Fin repairT) (hj : RepairBlank j) (c : Fin 2) (k : Fin 5) :
    j ≠ repairRoutingConfig (.header c k) := by
  intro he
  subst j
  rcases hj with hh | he | ⟨r, _, _, _, hr⟩ | ⟨r, _, _, _, _, hr⟩
  · have hb : placedSelectiveHost.Blank (placedSelectiveConfig (.header c k)) :=
      (SelectiveHost.Blank.map_iff placedSelectiveHost repairRoutingEmbed repairRoutingEmbed_injective _).mp hh
    rcases hb with hm | ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨off, r, hr, _, he⟩ | ⟨c, i, _, hi⟩
    · simp [placedSelectiveHost, placedSelectiveConfig] at hm
    · simp [placedSelectiveHost, placedSelectiveConfig] at hi
    · simp [placedSelectiveHost, placedSelectiveConfig] at hi
    · simp [placedSelectiveHost, placedSelectiveConfig, hr] at he
    · simp [placedSelectiveHost, placedSelectiveConfig] at hi
  · simp [repairRoutingConfig, placedSelectiveConfig, repairRoutingRole] at he
  · cases r <;> simp [repairKey, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole] at hr
  · cases r <;> simp [repairBad, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole] at hr

theorem repairHeaderPairBank_blank (tapes : Fin repairHeaderT → List (Fin (A + 4))) (j : Fin repairT) (hj : RepairBlank j) :
    repairHeaderPairBank p X rb R B repairSharedHeaderBank tapes (repairHeaderRawCore j) = tapes (repairHeaderRawCore j) :=
  repairHeaderPairBank_raw_keep p X rb R B tapes j (repairBlank_headerSource j hj)

end
end IntegerMultBounds.MathlibTM2.Routing
