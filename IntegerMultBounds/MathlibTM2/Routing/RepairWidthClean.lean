module

public import IntegerMultBounds.MathlibTM2.Routing.RepairWidthFrame

/-! Erase generated raw row/mask words after exact repair. An arbitrary changed
record stream is retained, and every other tape returns to its initial value. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

noncomputable section

def repairWidthTargets : List (Fin (repairT + 6)) :=
  [fieldCore (repairSetupSource (.inr .row)), fieldCore (repairSetupSource (.inr .keyMask))]

theorem repairWidthClean_exec {Q A : ℕ} {P U : Type}
    (body : P → Pr P (repairT + 6) Q A U) (p : Layer.CompactGadget.Par) (rb : ℕ)
    (v : HS (repairT + 6) Q A U) (S : Stacks (repairT + 6) A)
    (records : List (Fin (A + 4)))
    (hrow : S.R (fieldCore (repairSetupSource (.inr .row))) = [])
    (hmask : S.R (fieldCore (repairSetupSource (.inr .keyMask))) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (metadataClean repairWidthTargets)
        (mk v { S with R := Function.update (repairWidthGenerated p rb S.R) (fieldCore repairHost.src) records })
        (2 * rb + 2 * p.wy + 5)
        (mk v' { S with R := Function.update S.R (fieldCore repairHost.src) records }) := by
  let row := fieldCore (repairSetupSource (.inr .row))
  let mask := fieldCore (repairSetupSource (.inr .keyMask))
  let src := fieldCore repairHost.src
  have hrm : row ≠ mask := by simp [row, mask, fieldCore_injective.eq_iff, repairSetupSource]
  have hrs : row ≠ src := fieldCore_injective.ne (repairSetup_source_src (.inr .row))
  have hms : mask ≠ src := fieldCore_injective.ne (repairSetup_source_src (.inr .keyMask))
  let S₁ : Stacks (repairT + 6) A := { S with R := Function.update (repairWidthGenerated p rb S.R) src records }
  obtain ⟨v', hu, he⟩ := metadataClean_exec body repairWidthTargets
    (by simp [repairWidthTargets, fieldCore_injective.eq_iff, repairSetupSource]) v S₁
  have hcost : metadataCleanCost S₁.R repairWidthTargets = 2 * rb + 2 * p.wy + 5 := by
    simp_all [metadataCleanCost, repairWidthTargets, S₁, repairWidthGenerated, row, mask, src]
    omega
  have hfinal : metadataCleared S₁.R repairWidthTargets = Function.update S.R src records := by
    funext j
    by_cases hj : j = row
    · subst j; simp_all [metadataCleared, repairWidthTargets, row, mask, src]
    · by_cases hk : j = mask
      · subst j; simp_all [metadataCleared, repairWidthTargets, row, mask, src]
      · by_cases hs : j = src
        · subst j; simp_all [metadataCleared, repairWidthTargets, S₁, row, mask, src]
        · simp_all [metadataCleared, repairWidthTargets, S₁, repairWidthGenerated, row, mask, src]
  rw [hcost, hfinal] at he
  exact ⟨v', hu, he⟩

end
end IntegerMultBounds.MathlibTM2.Routing
