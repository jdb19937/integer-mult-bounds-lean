module

public import IntegerMultBounds.Machine.CompactRecursiveDependencyBudget
public import IntegerMultBounds.Machine.CompactGlobalRowPadding

/-! Genuine dependency paths retain the original root exponent. This pays
nested role divisibility and positive child rows from the single original
row padding, instead of assuming fresh divisibility at each recursive call. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexRecursivePathRows
open CompactComplexRecursiveGeometry (arity)
open CompactRecursiveDependencyBudget (Path)
open CompactGlobalRowPadding (depth rowsAt)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  Networks.ComplexRecursiveCallSchema.calls

/-- Descending reduces the node exponent once per actual dependency level. -/
theorem root_power_le {activeAxes nodeLeft nodeExponent dependencyLevels frameVolume returnedVolume : ℕ}
    (path : Path activeAxes nodeLeft nodeExponent dependencyLevels frameVolume returnedVolume) :
    arity^(nodeExponent+dependencyLevels) ≤ activeAxes := by
  induction path with
  | root piece =>
    have rootFits := CompactComplexRecursiveGeometry.piece_fits _ piece
    simp only [Nat.add_zero]
    omega
  | child prior call inductionHypothesis =>
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using inductionHypothesis

/-- Actual root dimensions bound the remaining exponent plus consumed depth. -/
theorem exponent_levels_le_depth {activeAxes globalDimension nodeLeft nodeExponent dependencyLevels frameVolume returnedVolume : ℕ}
    (path : Path activeAxes nodeLeft nodeExponent dependencyLevels frameVolume returnedVolume)
    (activeFitsDimension : activeAxes ≤ globalDimension) :
    nodeExponent+dependencyLevels ≤ depth arity globalDimension := by
  calc
    nodeExponent+dependencyLevels = Nat.clog arity (arity^(nodeExponent+dependencyLevels)) :=
      (Nat.clog_pow arity _ (by decide)).symm
    _ ≤ depth arity globalDimension :=
      Nat.clog_mono_right arity ((root_power_le path).trans activeFitsDimension)

/-- The parent and next two row counts derive from one original padding.
In particular, actual child rows themselves admit the next role split. -/
theorem recursive_row_guards {activeAxes globalDimension nodeLeft nodeExponent dependencyLevels frameVolume returnedVolume : ℕ}
    (path : Path activeAxes nodeLeft nodeExponent dependencyLevels frameVolume returnedVolume)
    (activeFitsDimension : activeAxes ≤ globalDimension)
    (roleCount polynomialChunkCount : ℕ) (rolesPositive : 0 < roleCount)
    (chunksPositive : 0 < polynomialChunkCount) (twoLevelsRemain : 2 ≤ nodeExponent) :
    let parentRows := rowsAt roleCount arity globalDimension polynomialChunkCount dependencyLevels
    let childRows := parentRows/roleCount
    roleCount ∣ parentRows ∧ 0 < parentRows ∧
      roleCount ∣ childRows ∧ 0 < childRows ∧ 0 < childRows/roleCount ∧
      childRows = rowsAt roleCount arity globalDimension polynomialChunkCount (dependencyLevels+1) ∧
      childRows/roleCount = rowsAt roleCount arity globalDimension polynomialChunkCount (dependencyLevels+2) := by
  have remainingDepth := exponent_levels_le_depth path activeFitsDimension
  have parentDepth : dependencyLevels < depth arity globalDimension := by omega
  have childDepth : dependencyLevels+1 < depth arity globalDimension := by omega
  have grandchildDepth : dependencyLevels+2 ≤ depth arity globalDimension := by omega
  dsimp only
  rw [CompactGlobalRowPadding.next_rows,CompactGlobalRowPadding.next_rows]
  exact ⟨CompactGlobalRowPadding.split_divides _ _ _ _ _ rolesPositive chunksPositive parentDepth,
    CompactGlobalRowPadding.rowsAt_positive _ _ _ _ _ rolesPositive chunksPositive parentDepth.le,
    CompactGlobalRowPadding.split_divides _ _ _ _ _ rolesPositive chunksPositive childDepth,
    CompactGlobalRowPadding.rowsAt_positive _ _ _ _ _ rolesPositive chunksPositive childDepth.le,
    CompactGlobalRowPadding.rowsAt_positive _ _ _ _ _ rolesPositive chunksPositive grandchildDepth,rfl,rfl⟩

end IntegerMultBounds.Machine.CompactComplexRecursivePathRows
