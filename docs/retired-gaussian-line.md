# Retired native Gaussian line machine

On 2026-10-19, 16 modules were removed, totaling 5,034 source lines: 14 under
`Machine/`, `Compact/PowerTwoDigits.lean` and `Resampling/NeumannWords.lean`.

## Edges cut first

- **Resampling bridges.** `Resampling/WindowSum`, `OffDiagSum` and
  `TabledMaps` proved that the native Gaussian line machine's accumulators
  (`GaussianLine.accR`, `accI`) compute the resampling maps
  (`accumulators_eq`, `sum_re`, `sum_im`, `term_eq`,
  `accumulators_eq_W`). `NeumannWords` lifted them to the Neumann
  iteration. The Mathlib TM2 resampling stages use only the real-valued
  lemmas (`termW`, `offTermW`, `rhoC_real`, `floor_centre`, the tabled
  error bounds), so these bridges were removed. `WindowSum` now defines
  `centre` and `rho0_int` itself.
- **Row padding.** `Fast/CompactTopConfigPadding` used only
  `CompactRowPaddingRound.padded_bounds`; it is now
  `Compact.Layout.paddedRows_bounds`.
- **Reservation shape.** `Machine/CompactGadgetReservationShape` dropped its
  unused `rectangle_volume` and with it the import of
  `Machine/RadixRangePadding`. The compact reservation arithmetic
  (`CompactGadgetReservation*`, `CompactGlobal*`, `CompactReservationGrowth`,
  `CompactGuardGrowth`, `CompactScalarAllowances`) no longer imports any
  native machine.

The removed modules are the Gaussian line machine with its fixed-point word
library (`FixedMul`, `TwosComplement`, `BinaryMultiply`, `Gather`,
`Negate`, `SignExtendAdd`, the ruler and record tapes) and the row padding
machine.

The [exact manifest](retired-gaussian-line.json) records the files and recovery
baseline `a4235b3d77f019bb72844c774e28a97c12d1dbd3`. The scope rule of the
[native compact stage record](retired-native-compact-stage.md) applies. The
`DFT` corollary now counts as a root.

## Validation

- Guarded library build passed: 11,147 jobs.
- `AxiomAudit.lean` passed for 86,534 declarations.
- `CompletedProofCheck.lean` passed for 6 declarations.
- `CompactControlCheck.lean` passed for 521 contracts.
