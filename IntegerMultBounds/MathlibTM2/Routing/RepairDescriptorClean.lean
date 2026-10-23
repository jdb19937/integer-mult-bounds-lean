module

public import IntegerMultBounds.MathlibTM2.Routing.DescriptorClean
public import IntegerMultBounds.MathlibTM2.Routing.RepairDescriptorInstall
public import IntegerMultBounds.MathlibTM2.Routing.RepairInputFrame

/-! Erase the eleven generated R2 descriptors, retaining the repaired stream
and restoring every raw destination to its original blank state. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {Q A : ℕ} {P U : Type}
variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

theorem repairDescriptorJobs_nodup (L : Fin 11 → ℕ) :
    ((repairDescriptorJobs p X hG hK active s L).map DescriptorJob.dst).Nodup := by
  rw [repairDescriptorJobs, List.map_ofFn]
  apply List.nodup_ofFn.mpr
  exact descriptorCore_injective.comp repairDescriptorSource_injective

theorem repairDescriptorClean_exec
    (body : P → Pr P (repairT + (2 * 11 + 12)) Q A U) (L : Fin 11 → ℕ)
    (v : HS (repairT + (2 * 11 + 12)) Q A U) (S : Stacks (repairT + (2 * 11 + 12)) A)
    (out : List (Fin (A + 4)))
    (hblank : ∀ d, S.R (descriptorCore (repairDescriptorSource d)) = []) :
    let jobs := repairDescriptorJobs p X hG hK active s L
    ∃ v', v'.user = v.user ∧
      Exec body (metadataClean (jobs.map DescriptorJob.dst))
        (mk v { S with R := Function.update (descriptorBankGenerated S.R jobs) (descriptorCore repairHost.src) out })
        (descriptorEraseCost jobs) (mk v' { S with R := Function.update S.R (descriptorCore repairHost.src) out }) := by
  apply descriptorClean_exec body _ (repairDescriptorJobs_nodup p X hG hK active s L)
  · intro job hj
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hj
    apply descriptorCore_injective.ne
    change repairDescriptorSource (repairDescriptorKey j) ≠ repairHost.src
    rw [repairDescriptorSource_eq]
    exact repairSetup_source_src _
  · intro job hj
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hj
    exact hblank (repairDescriptorKey j)

end
end IntegerMultBounds.MathlibTM2.Routing
