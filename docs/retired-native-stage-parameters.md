# Retired native stage parameter layer

On 2026-10-19, 303 modules were removed, totaling 35,350 source lines: 294
under `Machine/` and 9 under `Compact/`.

`Machine/CompactFramedScalarGrid.lean` imported
`Machine/ActivePrefixStageParameters.lean` without using it. Removing that
import left `ActivePrefixStageParameters` and the native modules reachable
only through it (the remaining `ActivePrefix*`/`ActiveTarget*` parameter
modules, `CompactGadget*`, and the `Binary*`, `CountedPacked*`,
`SelectedSource*` and `PackedOffset*` families) outside the theorem and the
focused checks. `Layer/NodeRSharp.lean` had obtained a `positivity`
extension through that import; its one use now proves the nonnegativity
directly.

The [exact manifest](retired-native-stage-parameters.json) records the files
and recovery baseline `6757934de093ae0908a8bb5480151a783521e1d3`, following the
[native compact stage record](retired-native-compact-stage.md). The same scope
rule applies: only modules reachable on `master` at `3e7d90a4` were removed,
and the Shared50 supplier modules remain.

## Validation

- Guarded library build passed: 11,172 jobs.
- `AxiomAudit.lean` passed for 87,505 declarations.
- `CompletedProofCheck.lean` passed for 6 declarations.
- `CompactControlCheck.lean` passed for 521 contracts.
