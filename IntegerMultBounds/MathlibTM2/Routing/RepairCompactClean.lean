module

public import IntegerMultBounds.MathlibTM2.Routing.CompactDescriptorClean
public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactInstall
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

theorem repairCompactJobs_nodup (Lw Lg L : Fin 11 → ℕ) :
    ((repairCompactJobs p X hG hK active s Lw Lg L).map CompactDescriptorJob.dst).Nodup := by
  rw [repairCompactJobs, List.map_ofFn]
  apply List.nodup_ofFn.mpr
  exact compactDescriptorCore_injective.comp repairDescriptorSource_injective

theorem repairCompactClean_exec
    (body : P → Pr P repairCompactT Q A U) (Lw Lg L : Fin 11 → ℕ)
    (v : HS repairCompactT Q A U) (S : Stacks repairCompactT A)
    (out : List (Fin (A + 4)))
    (hblank : ∀ d, S.R (compactDescriptorCore (repairDescriptorSource d)) = []) :
    let jobs := repairCompactJobs p X hG hK active s Lw Lg L
    ∃ v', v'.user = v.user ∧
      Exec body (metadataClean (jobs.map CompactDescriptorJob.dst))
        (mk v { S with R := Function.update (compactDescriptorBankGenerated S.R jobs) (compactDescriptorCore repairHost.src) out })
        (compactDescriptorEraseCost jobs) (mk v' { S with R := Function.update S.R (compactDescriptorCore repairHost.src) out }) := by
  apply compactDescriptorClean_exec body _ (repairCompactJobs_nodup p X hG hK active s Lw Lg L)
  · intro job hj
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hj
    apply compactDescriptorCore_injective.ne
    change repairDescriptorSource (repairDescriptorKey j) ≠ repairHost.src
    rw [repairDescriptorSource_eq]
    exact repairSetup_source_src _
  · intro job hj
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hj
    exact hblank (repairDescriptorKey j)

end
end IntegerMultBounds.MathlibTM2.Routing
