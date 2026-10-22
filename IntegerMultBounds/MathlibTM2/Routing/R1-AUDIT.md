# R1 completion audit

R1 is the selective-update primitive, including physical good-set correctness and
complete priced host execution. Its acceptance gate is in PLAN.md and DESIGN.md.
This audit does not claim completion of exact repair, the full router or an
improvement to the multiplication theorem.

| Requirement | Authoritative Lean evidence |
| --- | --- |
| Arbitrary ordered sources outside active target bits; no source injectivity or increasing-order promise | `SlotSource.Allowed`, `slotRead_eq_physical`, `SelectiveRouter.selectiveRouting_exec` |
| Ideal global coordinate bijection and arbitrary dirty-control identity | `shearPerm`, `shear_involutive`, `borrowedShear_eq` in Shear.lean |
| Actual intermediate source reads, including inactive low bits and active upper bits | `selectiveRun_dynamic_good`, `selectiveRun_sources_good`, `slotRead_eq_physical` |
| Same actual host permutation and physical good-set XOR | `selectiveProgramPerm_good`, bundled in `selectiveRouting_exec` |
| Only active physical target bits change | `targetWord_bit`, `targetWord_other_bit`, plus the final `setDigit` equality |
| Arbitrary borrowed address fields, complete spectators and higher address bits restored | `selectiveRunIdx_good`, `selectiveRunIdx_div`, and the physical endpoint in `selectiveRouting_exec` |
| Global actual permutation, including exceptional addresses | `listPerm (selectivePerm ...) progW`, an `Equiv.Perm` on the complete finite record index |
| Concrete placement, not hypothetical separation | `placedSelectiveHost_valid`, `placedSelectiveHost_setup`, `placedSelectiveHost_swapT`, instantiated in `selectiveRouting_exec` |
| Actual metadata installation from raw inputs; all copies and counter construction charged | `MetadataJob.exec`, `metadataInstall_exec`, `selectiveSetup_exec` |
| All 12 rotations and 12 swaps executed in the original schedule, including symbol conversion, callback setup and cleanup | `selectivePass_exec`, `selectivePrepared_exec`, `selectiveCost_sum` |
| Final metadata cleanup, with exact cost and full register frame | `metadataClean_exec`, `metadataClean_restore`, `selectiveProgram_exec` |
| One complete execution changing only the record stream; input configuration and scratch restored | `selectiveRouting_exec`, whose final right-stack bank is an update of the original bank only at the stream register; left stacks and other stack fields unchanged |
| Fixed program structure, no numerical/source-list unrolling | `selectiveSetup_eq`, `selectiveProgram`, the fixed `progW` and fixed 27-key setup bank |
| Explicit canonical header values and guard widths | `routingHeaders`, `routingParameters_guards`, instantiated in `selectiveRouting_exec` |
| Density of the same physical good set, with all spectators included | `selectiveBad_card_le`, `selectiveBad_fraction_le`, `routingParameters_clog_density`, bundled in `selectiveRouting_exec` |

The entry point is `SelectiveRouter.selectiveRouting_exec`. Its remaining
hypotheses describe the input: positive record dimensions and scale, enough finite
control states, allowed source coordinates, the full rectangular record list,
binary configuration data, empty working tapes and empty left stacks. It does
not assume installed headers/counters, placement separation or unproved density
inequalities. Canonical header bits are specific raw configuration data, not an
arbitrary header oracle; their copies and separator installation are executed.

The cost is the explicit sum of metadata installation, all pass costs and final
cleanup. It does not assert that metadata generation or its amortization is free.
Uniform descriptor/header generation, matching/reservoir scheduling, permutation
decomposition and the short-record fallback belong to R3. R2 must execute the
exceptional-record extraction, sorting and reinsertion; R4 must integrate the
router into multiplication. None is silently counted as completed R1 work.

Verification: guarded checks of the placement, density and final entry point;
guarded public-root build; standard-axiom audit; plan-status and whitespace checks.
No new axioms, proof holes, native finite decisions or raised proof limits.
