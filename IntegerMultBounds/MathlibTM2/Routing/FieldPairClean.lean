module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryFieldPair
public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-! Erase generated raw row/mask words after exact repair. An arbitrary changed
record stream is retained, and every other tape returns to its initial value. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host



def fieldPairGenerated {N A : ℕ} (row mask : Fin N) (nr nm : ℕ)
    (R : Fin (N + 6) → List (Fin (A + 4))) :=
  Function.update (Function.update R (fieldCore row) (binSyms nr 0))
    (fieldCore mask) (binSyms nm (Layer.CompactMasks.maskVal nm id))

theorem fieldPairGenerated_project {N A : ℕ} (row mask : Fin N) (nr nm : ℕ)
    (R : Fin (N + 6) → List (Fin (A + 4))) :
    (fun i => fieldPairGenerated row mask nr nm R (fieldCore i)) =
      Function.update (Function.update (fun i => R (fieldCore i)) row (binSyms nr 0))
        mask (binSyms nm (Layer.CompactMasks.maskVal nm id)) := by
  funext i
  simp only [fieldPairGenerated, Function.update_apply, fieldCore_injective.eq_iff]

theorem fieldPairClean_exec {N Q A : ℕ} {P U : Type}
    (body : P → Pr P (N + 6) Q A U) (r m str : Fin N) (hrm₀ : r ≠ m) (hrs₀ : r ≠ str) (hms₀ : m ≠ str) (nr nm : ℕ)
    (v : HS (N + 6) Q A U) (S : Stacks (N + 6) A)
    (records : List (Fin (A + 4)))
    (hrow : S.R (fieldCore r) = [])
    (hmask : S.R (fieldCore m) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (metadataClean [fieldCore r, fieldCore m])
        (mk v { S with R := Function.update (fieldPairGenerated r m nr nm S.R) (fieldCore str) records })
        (2 * nr + 2 * nm + 5)
        (mk v' { S with R := Function.update S.R (fieldCore str) records }) := by
  let row := fieldCore r
  let mask := fieldCore m
  let src := fieldCore str
  have hrm : row ≠ mask := fieldCore_injective.ne hrm₀
  have hrs : row ≠ src := fieldCore_injective.ne hrs₀
  have hms : mask ≠ src := fieldCore_injective.ne hms₀
  let S₁ : Stacks (N + 6) A := { S with R := Function.update (fieldPairGenerated r m nr nm S.R) src records }
  obtain ⟨v', hu, he⟩ := metadataClean_exec body [fieldCore r, fieldCore m]
    (by simp [fieldCore_injective.eq_iff, hrm₀]) v S₁
  have hcost : metadataCleanCost S₁.R [fieldCore r, fieldCore m] = 2 * nr + 2 * nm + 5 := by
    simp_all [metadataCleanCost, S₁, fieldPairGenerated, row, mask, src]
    omega
  have hfinal : metadataCleared S₁.R [fieldCore r, fieldCore m] = Function.update S.R src records := by
    funext j
    by_cases hj : j = row
    · subst j; simp_all [metadataCleared, row, mask, src]
    · by_cases hk : j = mask
      · subst j; simp_all [metadataCleared, row, mask, src]
      · by_cases hs : j = src
        · subst j; simp_all [metadataCleared, S₁, row, mask, src]
        · simp_all [metadataCleared, S₁, fieldPairGenerated, row, mask, src]
  rw [hcost, hfinal] at he
  exact ⟨v', hu, he⟩

end IntegerMultBounds.MathlibTM2.Routing
