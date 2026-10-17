# Review of the October 17 pruning

Commit `c7b1ba9e` removed 669 modules that the `2^-33` theorem and its checks
do not import. This review lists the parts worth restoring for the remaining
milestones (PLAN.md M3–M8). Restore with `git checkout 8fb31454 -- <paths>`.
Nothing here has been rebuilt against the current tree.

## Restore first

| Milestone | Modules | Key results | Why |
| --- | --- | --- | --- |
| M7 | `NLogN/ToeplitzApply`, `ToeplitzRounded`, `ToeplitzScaled`, `PhaseCellInteriorCover`, `PhaseCellInteriorSolve`, `PhaseCellRoundedCell`, `PhaseCellWeightRange` | `apply_four`, `rounded_apply`, `rounded_block`, `interior_cover`, `cell_solve`, `rounded_cell`, `selected_similarity_range` | Checked rounded Gaussian-inverse work that PLAN M7 counts as done; dependencies are still live. |
| M3 | `MathlibTM2/Fast/CompactStopped*` (28), `Cost/CompactStoppedReservation{,Ready}`, `Fast/CompactTopAdapterContract` | `compactGlobalCutoff_leaf_bound`, `compactStoppedGlobalPipeline`, `compactStoppedReservedPcs_exp_sum`, `compactStopped_reserved_cost_split` | Checked scanner, cutoff and reservation work PLAN M3 lists; needs porting onto the `R` top and layer step. |
| M7, M8 | `NLogN/Primes` | `primeChain`, `exists_primes_chain`, `primeChain_prod_bounds` | Coprime prime supply without axioms. |
| M6, M4 | `MathlibTM2/Layer/OccurrenceRecurrence` | `cost_le_potential`, `rank_moment_le`, `cost_le_rank_power` | Generic variable-rank recurrence; imports only Mathlib. |
| M6, M8 | `MathlibTM2/Cost/CompactSupplierCeiling`, `CompactGaussianRoute` | `supplier_saving`, `saving_lt_ceiling`, `layer_lt_ceiling` | Shows the current supplier caps the saving near `2^-33`/`2^-31`; the next gain needs M6. |

## Useful templates

- **M7 tape execution.** The `Machine/Recover*` family (about 35 modules, with the `Gamma*`, `Ruler*`, `RawMsbDescriptor` and `RawBitWordReset` helpers) is a complete exact-recovery tape machine with a linear cost. Also `Machine/NeumannLoop*`, `NeumannStepLemmas`, `GaussianLineFast` and `SubPass`, which need `Schoenhage/FixedMulPlaced`. Plus `Machine/PackedMultiplierPolylogBudget` and `Resampling/FloorStep`, `LineCost`, `Fast/BandFactorFits`, `Spec/SyntheticConvolutionFacts`.
- **M5 routing.**
  - `Machine/ActivePrefixStage{Pair,NativePair}{Schedule,Inverse,Coordinates}` and `ActivePrefixStageNativeConjugation`: a reverse word restores spectators at the forward cost.
  - `Machine/ButterflyInverseAxis*`, `ButterflyAxisWalsh`, `ButterflySpectator*`, `ButterflyIndependentGuard*`.
  - `LayoutCost`, including `exists_swap_list`.
  - `Schoenhage/LayoutMoves`, `LayoutSwapScan`, `PaperSigma`, `PaperLayout`, `DifLayout`, `DifOpposite*`.
  - `Resampling/FlatTensor`, `PaddedTensor`, `Sandwich`.
  - `Machine/PublicHadamardAddressBridge`, `RationalTranslationAffineBridge`.
- **M3 control and repair.**
  - `Machine/FiniteFlow*`, `GuardedFiniteReturn*`, `FiniteReturn{Guard,Flow}`: path composition and returning child calls.
  - `Machine/CompactReservation{Cutoff,Rate}`, `CompactFallback*`.
  - `Machine/ActiveRepairLayout{Global,Records}Allowance`.
  - `Machine/CountedTapeRepair{Endpoint,Linear}`, `CountedLate*Repair*`; first check the live `CountedTapeRepairDensity`.
  - `Machine/CompactGlobalRow*`, `CompactReservationPadding*`.
- **M4 precision and stock.**
  - `Machine/NativeSignedGap*`, `NativeSignedReturn*`, `SignedRadixExactReturn`: single-scan precision changes for returning children.
  - `Machine/CompactChildHeadersStack`, `BinaryPairFrame`.
  - `Schoenhage/PrefixRounds`, `PrefixRoundMath`.
- **Generic tape glue.** `Machine/EqualWordSwap`, `WordBankSwap`, `ContiguousBankPlacement`, `TapeAlphabet`, `FiniteTapeKernelDispatch`, `GuardedMapCopy`, `Schoenhage/OfHoare`, `ProgPrim`.

## Not worth restoring

- **Superseded by live replacements.**
  - The paper-format `Schoenhage` transform and convolution pipeline (`Driver*`, `Transform*`, `Script*`, `Conv*`, `FixedMul*` and similar) is replaced by `MathlibTM2/Fast` and `Host/SSMul`.
  - The Resampling tape modules are replaced by the `Fast/Table*`, `ResampA*` and `ResampB*` modules.
  - `Machine/UnitPhase*`, `Sparse*Phase*`, `Chirp*` codecs, `Binary*Offset*` and `ButterflyRecord/Stream` have live equivalents.
- **Callers of the old layout.** The old compact caller wiring (`Layer*`, `CompactReserved*`, `CompactGadgetReservation*`, `Packed{Early,Prefix}*`) is specific to that layout.
- **Old retuning experiments.** `CompactSharp*`, `CompactParameterWidth`, `CompactEighthRoom` and `CompactDyadicDimension*`.
- **Bundles.** The milestone wrapper files.
