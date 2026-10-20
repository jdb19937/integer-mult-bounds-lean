# Retired native selection and reinsertion machines

On 2026-10-19, 5 modules under `Machine/` were removed, totaling 1,917 source
lines: `OrderedSelect`, `WordMoves`, `BinaryAccumulate`, `Partition` and
`Reinsert`.

## Edges cut first

- **Row selection.** `Resampling/RowSelect` proved the native ordered
  selection machine's tape contract (`rowSelect_hoare`, with `crossing_iff`,
  `q_eq_iff` and `selected_eq_filter`). The Mathlib TM2 resampling stages
  use only the index arithmetic (`q`, `q_lt`, `q_strictMono`,
  `rowIndexNat_eq`, `filter_range_eq_map`), so the machine section was
  removed.
- **Repair pipeline.** `Compact/RepairPipeline` used only the `Record`
  structure of `Machine/Partition` and the list function `Reinsert.fill`.
  Both are now defined in `Compact/RepairPipeline`.

The [exact manifest](retired-select-reinsert.json) records the files and
recovery baseline `5e86d444b6cde50a0384152656a041c4b1669b04`. The scope rule of the
[native compact stage record](retired-native-compact-stage.md) applies.

## Validation

- Guarded library build passed: 11,142 jobs.
- `AxiomAudit.lean` passed for 86,192 declarations.
- `CompletedProofCheck.lean` passed for 6 declarations.
- `CompactControlCheck.lean` passed for 521 contracts.
