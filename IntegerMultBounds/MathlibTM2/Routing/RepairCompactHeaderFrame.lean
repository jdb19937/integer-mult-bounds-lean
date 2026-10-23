module

public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactHeaderDataExec
public import IntegerMultBounds.MathlibTM2.Routing.RepairHeaderFrame
public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactScratch

/-! Header generation preserves all auxiliary inputs and raw tapes needed by
classifier-generated exact repair. Only the ten canonical headers change. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {A : ℕ} (p : Par) (X rb R B : ℕ)

theorem repairCompactHeaderPairBank_core_keep (tapes : Fin repairCompactHeaderT → List (Fin (A + 4)))
    (j : Fin repairCompactClassifierT)
    (hj : ∀ c k, j ≠ classifierCore (repairCompactConfigurationCore (repairRoutingConfig (.header c k)))) :
    repairHeaderPairBank p X rb R B repairCompactSharedHeaderBank tapes (sharedHeaderCore j) = tapes (sharedHeaderCore j) := by
  apply repairHeaderPairBank_keep
  intro c k
  rw [repairCompactSharedHeaderBank_header]
  exact sharedHeaderCore_injective.ne (hj c k)

theorem repairCompactHeaderPairBank_classifierAux (tapes : Fin repairCompactHeaderT → List (Fin (A + 4))) (i : Fin 16) :
    repairHeaderPairBank p X rb R B repairCompactSharedHeaderBank tapes (sharedHeaderCore (classifierAux i)) =
      tapes (sharedHeaderCore (classifierAux i)) :=
  repairCompactHeaderPairBank_core_keep p X rb R B tapes _ (fun _ _ => (classifierCore_aux _ i).symm)

theorem repairCompactHeaderPairBank_widthAux (tapes : Fin repairCompactHeaderT → List (Fin (A + 4))) (i : Fin 6) :
    repairHeaderPairBank p X rb R B repairCompactSharedHeaderBank tapes
      (sharedHeaderCore (classifierCore (fieldAux (N := repairCompactT) i))) =
    tapes (sharedHeaderCore (classifierCore (fieldAux (N := repairCompactT) i))) :=
  repairCompactHeaderPairBank_core_keep p X rb R B tapes _
    (fun _ _ => classifierCore_injective.ne (fieldCore_aux _ i).symm)

theorem repairCompactHeaderPairBank_compactDescriptorAux (tapes : Fin repairCompactHeaderT → List (Fin (A + 4))) (i : CompactDescriptorRole 11) :
    repairHeaderPairBank p X rb R B repairCompactSharedHeaderBank tapes
      (sharedHeaderCore (classifierCore (fieldCore (N := repairCompactT) (compactDescriptorAux (N := repairT) (J := 11) i)))) =
    tapes (sharedHeaderCore (classifierCore (fieldCore (N := repairCompactT) (compactDescriptorAux (N := repairT) (J := 11) i)))) :=
  repairCompactHeaderPairBank_core_keep p X rb R B tapes _
    (fun _ _ => classifierCore_injective.ne (fieldCore_injective.ne (compactDescriptorCore_aux _ i).symm))

theorem repairCompactHeaderPairBank_targets (tapes : Fin repairCompactHeaderT → List (Fin (A + 4))) (key : RepairSetupKey) :
    repairHeaderPairBank p X rb R B repairCompactSharedHeaderBank tapes (repairCompactHeaderRawCore (repairSetupTarget key)) =
      tapes (repairCompactHeaderRawCore (repairSetupTarget key)) :=
  repairCompactHeaderPairBank_raw_keep p X rb R B tapes _ (fun c k => (repairSetup_sources (.inl (.header c k)) key).symm)

theorem repairCompactHeaderPairBank_extra (tapes : Fin repairCompactHeaderT → List (Fin (A + 4))) (key : RepairExtra) :
    repairHeaderPairBank p X rb R B repairCompactSharedHeaderBank tapes (repairCompactHeaderRawCore (repairSetupSource (.inr key))) =
      tapes (repairCompactHeaderRawCore (repairSetupSource (.inr key))) := by
  apply repairCompactHeaderPairBank_raw_keep
  intro c k
  simp [repairSetupSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]

theorem repairCompactHeaderPairBank_src (tapes : Fin repairCompactHeaderT → List (Fin (A + 4))) :
    repairHeaderPairBank p X rb R B repairCompactSharedHeaderBank tapes (repairCompactHeaderRawCore repairHost.src) =
      tapes (repairCompactHeaderRawCore repairHost.src) :=
  repairCompactHeaderPairBank_raw_keep p X rb R B tapes _ (fun c k => (repairSetup_source_src (.inl (.header c k))).symm)

theorem repairCompactHeaderPairBank_descriptors (tapes : Fin repairCompactHeaderT → List (Fin (A + 4))) (d : RepairDescriptorKey) :
    repairHeaderPairBank p X rb R B repairCompactSharedHeaderBank tapes (repairCompactHeaderRawCore (repairDescriptorSource d)) =
      tapes (repairCompactHeaderRawCore (repairDescriptorSource d)) := by
  apply repairCompactHeaderPairBank_raw_keep
  intro c k
  cases d with
  | none => simp [repairDescriptorSource, repairSetupSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  | some d =>
    rcases d with ⟨off, j⟩
    simp [repairDescriptorSource, repairSetupSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]

theorem repairCompactHeaderPairBank_blank (tapes : Fin repairCompactHeaderT → List (Fin (A + 4))) (j : Fin repairT) (hj : RepairBlank j) :
    repairHeaderPairBank p X rb R B repairCompactSharedHeaderBank tapes (repairCompactHeaderRawCore j) = tapes (repairCompactHeaderRawCore j) :=
  repairCompactHeaderPairBank_raw_keep p X rb R B tapes j (repairBlank_headerSource j hj)

end
end IntegerMultBounds.MathlibTM2.Routing
