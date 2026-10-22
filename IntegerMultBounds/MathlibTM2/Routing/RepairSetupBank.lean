module

public import IntegerMultBounds.MathlibTM2.Routing.RepairPlacement

/-! The fixed 34-word metadata bank of the complete exact selective primitive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

abbrev RepairSetupKey := SetupKey ⊕ RepairExtra

def repairExtraKeys : List RepairExtra :=
  [.row, .keyDescriptor, .keyMask, .badMask, .badPhase, .payload, .keyLength]

def repairSetupKeys : List RepairSetupKey := setupKeys.map Sum.inl ++ repairExtraKeys.map Sum.inr

theorem repairExtraKeys_mem (key : RepairExtra) : key ∈ repairExtraKeys := by
  cases key <;> simp [repairExtraKeys]

theorem repairSetupKeys_mem (key : RepairSetupKey) : key ∈ repairSetupKeys := by
  cases key with
  | inl key => simp [repairSetupKeys, setupKeys_mem]
  | inr key => simp [repairSetupKeys, repairExtraKeys_mem]

theorem repairSetupKeys_nodup : repairSetupKeys.Nodup := by decide +kernel

def repairExtraTarget : RepairExtra → Fin repairT
  | .row => repairReg (.field 5)
  | .keyDescriptor => repairKey (.desc 0)
  | .keyMask => repairKey (.desc 1)
  | .badMask => repairBad .mask
  | .badPhase => repairBad .phase
  | .payload => repairReg .payload
  | .keyLength => repairReg .keyLength

def repairSetupTarget : RepairSetupKey → Fin repairT
  | .inl key => key.target repairHost
  | .inr key => repairExtraTarget key

def repairSetupSource : RepairSetupKey → Fin repairT
  | .inl key => repairRoutingConfig key
  | .inr key => repairReg (.config key)

theorem repairSetupTarget_injective : Function.Injective repairSetupTarget := by
  intro key other he
  cases key with
  | inl key =>
    cases other with
    | inl other => exact congrArg Sum.inl (repairHost_setup.targets he)
    | inr other =>
      cases key <;> cases other <;>
        simp [repairSetupTarget, repairExtraTarget, SetupKey.target, repairHost,
          SelectiveHost.map, placedSelectiveHost, repairRoutingRole, repairKey, repairBad] at he
      rename_i f
      have hv := congrArg Fin.val he
      have hf := f.isLt
      change f.val = 5 at hv
      omega
  | inr key =>
    cases other with
    | inl other =>
      cases key <;> cases other <;>
        simp [repairSetupTarget, repairExtraTarget, SetupKey.target, repairHost,
          SelectiveHost.map, placedSelectiveHost, repairRoutingRole, repairKey, repairBad] at he
      rename_i f
      have hv := congrArg Fin.val he
      have hf := f.isLt
      change 5 = f.val at hv
      omega
    | inr other =>
      cases key <;> cases other <;> simp_all [repairSetupTarget, repairExtraTarget, repairKey, repairBad]

theorem repairSetup_regs (key : RepairSetupKey) :
    [repairSetupSource key, repairSetupTarget key, repairHost.out, repairHost.tmp, repairHost.ctmp].Nodup := by
  cases key with
  | inl key => exact repairHost_setup.regs key
  | inr key =>
    cases key <;> simp [repairSetupSource, repairSetupTarget, repairExtraTarget,
      repairHost, SelectiveHost.map, placedSelectiveHost, repairRoutingRole, repairKey, repairBad]

theorem repairSetup_sources (key other : RepairSetupKey) :
    repairSetupSource key ≠ repairSetupTarget other := by
  cases key with
  | inl key =>
    cases other with
    | inl other => exact repairHost_setup.sources key other
    | inr other =>
      cases key <;> cases other <;>
        simp [repairSetupSource, repairSetupTarget, repairExtraTarget, repairRoutingConfig,
          placedSelectiveConfig, repairRoutingRole, repairKey, repairBad]
  | inr key =>
    cases other with
    | inl other =>
      cases other <;> simp [repairSetupSource, repairSetupTarget, SetupKey.target, repairHost,
        SelectiveHost.map, placedSelectiveHost, repairRoutingRole]
    | inr other =>
      cases other <;> simp [repairSetupSource, repairSetupTarget, repairExtraTarget, repairKey, repairBad]

theorem repairSetup_target_src (key : RepairSetupKey) : repairSetupTarget key ≠ repairHost.src := by
  cases key with
  | inl key =>
    intro he
    exact setupTargets_src repairHost repairHost_valid
      (List.mem_map.mpr ⟨key, setupKeys_mem key, he⟩)
  | inr key => cases key <;> simp [repairSetupTarget, repairExtraTarget, repairKey, repairBad]

end
end IntegerMultBounds.MathlibTM2.Routing
