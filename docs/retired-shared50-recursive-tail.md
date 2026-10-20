# Retired Shared50 recursive tail

On 2026-10-20, 46 modules were removed, totaling 5,400 source lines. They are
leftovers of the [retired Shared50 recursive machine](retired-shared50-machine.md):
modules still imported by the completed theorem but contributing no constant
to it.

The [exact manifest](retired-shared50-recursive-tail.json) records the files
and recovery baseline `0ad8fbc2fa96b513ba2adca8524d93b44fee68d6`.

## Scope

A module was removed only if no constant it defines is reached from
`mulInTime` and `statement`, from any declaration of a module imported by the
compact and CRT checks, or from any declaration of the open `M6`, `M8`, `DFT`
and restored milestone modules (traced over `getUsedConstants`). Modules that
`PR589` imports were kept without tracing.

| Group | Modules |
| --- | ---: |
| `Machine/Shared50*` recursive call, node, root and budget modules | 37 |
| `Networks/` `FramedFactorExecution`, `GlobalCircuitBits`, `GlobalLabelsResiduals`, `TensorTerminalWeight` | 4 |
| `Machine/ArbitrarySlice*`, `ArbitraryWidthPieceBudget` built only on them | 5 |

Importers of a removed module import its own imports instead.

## Declarations removed from retained modules

- `ComplexFramedExecution.lowered`
- `Shared50OrderedPieces.stages`
- `RecursiveScalarSelection.description_rational`
- `Shared50RecursiveChildPermutation.child`, `child_spec`, `child_encoded`
- `ArbitraryWidthPieces.slice_shape`, `piece_shape`, `piece_view`
- `Shared50RecursiveBasePermutation.source_roles`, `source_roles_updated`
- `Shared50RecursiveBudgetBound.normalized`, `normalized_nonneg`,
  `budget_le_normalized`, `constant`, `constant_positive`, `normalized_bound`,
  `power_width_bound`; `tau_range`, `exponent_range` and `branching_bound` remain.

`scripts/s6/shared50_supplier_modules.txt` still lists some removed modules;
`apply_seam.py` skips missing files.
