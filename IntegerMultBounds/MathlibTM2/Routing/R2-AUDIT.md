# R2 completion audit

R2 requires executed classification, complete destination keys, exceptional
extraction/sorting/reinsertion, clean scratch and the cost derived from R1's
physical bad-set density. Its acceptance gate is in PLAN.md and DESIGN.md.
The public entry point is `exactSelective_exec` in ExactSelective.lean.

| Requirement | Authoritative Lean evidence |
| --- | --- |
| Ideal selective XOR on every address, not only guarded addresses | `selectiveIdealIdx_involutive`, `selectiveIdealPerm`, `selectiveIdeal_view` |
| Actual arbitrary ordered source reads remain valid, including inactive low bits and active upper bits | `slotView_xor_targetWord`, `source_xor_targetWord`, `targetWord_xor`; R1's actual source interpreter is used during routing |
| Exact ideal preserves the physical bad set; actual agrees off it and preserves it too | `selectiveIdeal_good`, `selectivePerm_agrees`, `selectivePerm_bad` |
| Reuse existing exact repair mathematics | `selectiveRepair_partition` instantiates `repair_good_of` and `repair_bad_of`, ultimately the existing RepairPipeline stable-sort identities |
| Actual flag/classification of the physical predicate | `badClassifier_spec` supplies an executed `CodeSpec` for `selectiveBadCode` |
| Zero target suffix width supported | `selectiveBadCode_padded`, `paddedCopy_exec`, `spreadPadded_exec`; actual classifier scans one additional zero column |
| Arbitrary-source target key emitted by tape programs | `headerRead_exec`, `patternKey_exec`, `selectiveKeyPattern_value`, `selectiveKeyTarget_exec` |
| Complete destination ranks, including row bits; no key collisions from truncation | `selectiveKey_digit`, `selectiveKey_row`, `selectiveKeyBits_ideal`, `selectiveKeyedFrom`, `selectiveKey_rank_bound` with `R ≤ 2^rb` |
| Executed whole-stream keying, payload copy, stream-order restoration and counter reset | `keyRecord_exec`, `keyRecordLoop_exec`, `keyStream_exec`, concretely instantiated by `selectiveKeyEmitter_spec` and `selectiveKeyPass_exec` |
| Actual exceptional extraction, radix sorting, merge/reinsertion, key stripping and resets | `selectiveRepair_exec` instantiates the existing executed `repairAtC_exec`; `repairCore_exec` supplies its concrete classifier and all partition hypotheses |
| Exact extraction count is R1's physical bad-rank count | `selectiveBad_records` |
| Concrete shared register placement for every phase | `repairHost_valid`, `repairHost_setup`, `repairKey_driver`, `repair_scan_index_separate`, `repair_scan_regs`, `repair_sort_separate`, `repair_sort_injective`, `repair_sort_fields` and field/length-counter separation |
| All phases run on the same stream and physical counter bank | `repairKey_cf`, `repairBad_cf`; `repairCore_exec` composes their actual programs on that bank |
| Actual installation of all metadata and all counters | `repairSetupJob`, `repairSetup_exec`: 34 words, including zero row counter, binary-to-unary lengths, descriptor/mask copies and both canonical swap header banks |
| Raw inputs and installer scratch restored; installed words do not overwrite blank work | `repairSetup_regs`, `repairSetup_sources`, `repairSetup_target_blank`, `repairSetup_prepared`, `repairSetup_exec` |
| Full cleanup restores the original metadata destinations | `metadataClean_exec`, `metadataClean_restore`, instantiated in `repairProgram_exec` |
| One complete all-address execution from raw configuration, with no prepared execution oracle | `repairProgram_exec`; specialized to canonical headers and concrete guards in `exactSelective_exec` |
| Every register except stream restored; all borrowed address fields and complete spectators preserved | Final state in `exactSelective_exec` is the original stack configuration with only `S.R stream` updated; `selectiveIdeal_view` and sparse `targetWord_bit`/`targetWord_other_bit` identify the exact physical destination |
| All setup, keying, routing, classification, scan/sort/merge/strip/reset and cleanup costs included | `metadataInstallCost + repairDensityCoreCost + metadataCleanCost` in `exactSelective_exec`; `repairCoreCost`/`repairScanCost` retain the exact earlier phase bounds |
| Cost genuinely derived from the same physical density used by classification | `selectiveRepair_sortCost_density`, `repairScanCost_density`, `repairCoreCost_density`; `routingParameters_radices` instantiates both radix inequalities in `exactSelective_exec` |
| Fixed finite program, not source/dimension-specific unrolling | `repairSetup_eq`; `repairProgram` has fixed keying, routing and repair program structure on finite `repairT` |

The final theorem's assumptions describe raw input and the fixed host interface:
positive record count/length and scale, enough finite control states/alphabet,
`n ≤ scale`, row count fitting its binary width, allowed source coordinates,
correct raw configuration tapes, empty installed metadata/work scratch/left
stacks, and the complete rectangular list of bit-encoded records. No `Good`
assumption is required. The address fields borrowed by the gadget range over all
values in that rectangle; they are not initialized address bits. The empty host
metadata counters are a different, explicitly constructed machine resource.

`RepairSetupData` specifies raw binary words and descriptor/mask/header bits.
Their copying, separator installation and zero/unary-counter construction are
executed and charged. Uniform generation of these input descriptors/headers is
still R3's input-compiler obligation, as already assigned in the R1 design.
This theorem does not silently treat input generation or metadata amortization
as free. R3 also owns matching/reservoir scheduling, permutation decomposition
and the short-record fallback; R4 owns complete-router and multiplication
integration. The multiplication kappa is unchanged.

Verification for completion: guarded checks of metadata bank/data/blankness,
setup, complete program, density costs and final entry point; guarded public-root
build; complete standard-axiom audit; plan-status and whitespace checks. The
public build also rechecks the refactored R1 prepared-word constructor and all
existing consumers. No new axioms, proof holes, native finite decisions or raised
proof limits are used. New setup/final modules check near 2.1 GiB each.
