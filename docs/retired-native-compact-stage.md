# Retired native compact stage machines

On 2026-10-19, 459 modules were removed, totaling 41,991 source lines. Since
the compact slot operations run on the Mathlib TM2 slot XOR
([record](retired-compact-slot.md)), nothing in the completed theorem or a
focused check imports the native compact stage machines any more.

The [exact manifest](retired-native-compact-stage.json) records the files and
recovery baseline `e3c9982c7f3c1756de71790a34656cf37882d3bb`. Recover
individual files and their root imports from that revision if the native route
is resumed.

## Boundary

| Directory | Modules |
| --- | ---: |
| `Machine/` | 446 |
| `MathlibTM2/Cost/` | 4 |
| `MathlibTM2/Node/` | 4 |
| `Compact/` | 4 |
| `Networks/` | 1 |

The `Machine/` modules are the `ActivePrefix*`, `ActiveRepair*` and
`ActiveTarget*` stage machines with their headers, budgets and repair layouts.

### Edges cut first

- **Native `Packed` theorems.** The native repair condition `Packed` and its
  caller theorems were used only by the compact control check. Their
  declarations, `Cost/CompactParameters.lean` and
  `Cost/CompactCallerUniformRuntime.lean` were removed.
- **Density arithmetic.** `Cost/CompactSlotPacking.lean` now proves its dyadic
  density bound from `Compact/RepairBounds` directly.
- **Live layout geometry.** `Node/CompactGeometryRecursive.lean` keeps only the
  live layout invariant and the selected-bit embedding. `Node/CompactGeometry.lean`
  and its native stage and ordinal mappings were removed.
- **Check-only modules.** `Node/CompactEncoding`, `Cost/CompactStage`,
  `Cost/CompactStageExec`, `Node/CompactRotStage` and `Node/CompactRotHost`
  were imported only by the compact control check, and were removed.

### Scope

A module was removed only if:
- it was unreachable from the theorem, the five focused checks and the legacy
  audits; and
- it had been reachable on `master` at `3e7d90a4`.

Modules already outside those closures on `master` remain. The Shared50
interchange supplier modules were kept here and retired later
([record](retired-shared50-machine.md)).

The compact control check no longer audits the 19 removed native contracts.
No retained theorem statement or proof limit was weakened.

## Validation

- Guarded library build passed: 11,475 jobs.
- `AxiomAudit.lean` passed for 93,910 declarations.
- `CompletedProofCheck.lean` passed for 6 declarations.
- `CompactControlCheck.lean` passed for 521 contracts.
