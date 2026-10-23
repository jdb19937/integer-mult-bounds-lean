module

public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactHeaderFrame
public import IntegerMultBounds.MathlibTM2.Routing.RepairHeadersClean
public import IntegerMultBounds.MathlibTM2.Routing.RepairHeaderBank

/-! Erase all ten generated headers after repair, retaining the changed stream.
The exact cleanup price depends only on the ten canonical header lengths. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

def repairCompactGeneratedHeaderTargets : List (Fin repairCompactHeaderT) :=
  List.ofFn (fun j : Fin 10 => repairCompactHeaderRawCore (repairHeaderDestination j))

theorem repairCompactGeneratedHeaderTargets_nodup : repairCompactGeneratedHeaderTargets.Nodup :=
  List.nodup_ofFn.mpr (repairCompactHeaderRawCore_injective.comp repairHeaderDestination_injective)

theorem repairCompactGeneratedHeaderTargets_src : repairCompactHeaderRawCore repairHost.src ∉ repairCompactGeneratedHeaderTargets := by
  intro hm
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hm
  exact (repairSetup_source_src (.inl (.header (repairHeaderIndex j).1 (repairHeaderIndex j).2)))
    (repairCompactHeaderRawCore_injective hj)

theorem repairCompactHeadersClean_exec {Q A : ℕ} {P U : Type}
    (body : P → Pr P repairCompactHeaderT Q A U) (p : Par) (X rb R B : ℕ)
    (v : HS repairCompactHeaderT Q A U) (S : Stacks repairCompactHeaderT A) (records : List (Fin (A + 4)))
    (hblank : ∀ c k, S.R (repairCompactHeaderRawCore (repairRoutingConfig (.header c k))) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (metadataClean repairCompactGeneratedHeaderTargets)
        (mk v { S with R := Function.update (repairHeaderPairBank p X rb R B repairCompactSharedHeaderBank S.R) (repairCompactHeaderRawCore repairHost.src) records }) (repairHeaderErasePrice p X rb R B)
        (mk v' { S with R := Function.update S.R (repairCompactHeaderRawCore repairHost.src) records }) := by
  let generated := repairHeaderPairBank p X rb R B repairCompactSharedHeaderBank S.R
  let S₁ : Stacks repairCompactHeaderT A := { S with R := Function.update generated (repairCompactHeaderRawCore repairHost.src) records }
  obtain ⟨v', hu, he⟩ := metadataClean_exec body repairCompactGeneratedHeaderTargets repairCompactGeneratedHeaderTargets_nodup v S₁
  have hc : metadataCleanCost S₁.R repairCompactGeneratedHeaderTargets = repairHeaderErasePrice p X rb R B := by
    rw [metadataCleanCost_eq_sum]
    unfold repairCompactGeneratedHeaderTargets repairHeaderErasePrice
    rw [List.map_ofFn]
    apply congrArg (fun f : Fin 10 → ℕ => (List.ofFn f).sum + 1)
    funext j
    have hs : repairCompactHeaderRawCore (repairHeaderDestination j) ≠ repairCompactHeaderRawCore repairHost.src :=
      repairCompactHeaderRawCore_injective.ne (repairSetup_source_src (.inl (.header (repairHeaderIndex j).1 (repairHeaderIndex j).2)))
    dsimp only [Function.comp_apply, S₁]
    rw [Function.update_of_ne hs]
    dsimp only [generated, repairHeaderDestination]
    rw [repairCompactHeaderPairBank_raw_header, List.length_map]
  have hf : metadataCleared generated repairCompactGeneratedHeaderTargets = S.R := by
    funext i
    by_cases hi : i ∈ repairCompactGeneratedHeaderTargets
    · rw [metadataCleared_at _ _ i hi]
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
      exact (hblank (repairHeaderIndex j).1 (repairHeaderIndex j).2).symm
    · rw [metadataCleared_keep _ _ i hi]
      apply repairHeaderPairBank_keep
      intro c k heq
      obtain ⟨j, hj⟩ := repairHeaderIndex_surjective (c, k)
      apply hi
      apply List.mem_ofFn.mpr
      refine ⟨j, ?_⟩
      simpa only [repairHeaderDestination, hj, repairCompactSharedHeaderBank_header, repairCompactHeaderRawCore] using heq.symm
  have hfinal : metadataCleared S₁.R repairCompactGeneratedHeaderTargets =
      Function.update S.R (repairCompactHeaderRawCore repairHost.src) records := by
    rw [metadataCleared_update _ _ _ _ repairCompactGeneratedHeaderTargets_src, hf]
  rw [hc, hfinal] at he
  exact ⟨v', hu, he⟩

end
end IntegerMultBounds.MathlibTM2.Routing
