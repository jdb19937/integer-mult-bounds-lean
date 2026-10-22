# Arbitrary-source coordinate routing

This is the R1–R4 work stream in [PLAN.md](../../../PLAN.md). Its target is a
fixed-tape program routing a complete rectangular record stream by a described
coordinate permutation, preserving arbitrary spectators and restoring scratch,
with cost `C V (p^tau polylog p + 1) + poly p`. The exponent comes from the
ordinary BIT supplier; no particular supplier or dimension is fixed here.

## First checked boundary: logical selective updates

`Shear.lean` defines a simultaneous XOR on a finite set of target coordinates.
For each selected target its source must lie outside that target set. Sources
need not be contiguous or earlier than targets. Source injectivity is unnecessary
for this identity; the later matching scheduler must supply whatever additional
disjointness its physical placement requires.

The module proves:

- `toggle_source`: every source read is preserved by a target update;
- `shear_involutive`, `shearPerm`: the ideal map is a permutation on all addresses;
- `load_toggle`: the loads read the same source values before and after toggling;
- `borrowedShear_eq`: toggle, load, toggle, unload realizes the shear and restores
  every borrowed-control bit, for arbitrary initial controls. The unload reads
  the actual final data, not a saved or hypothetical original input.

This is a logical address specification. Its function application at `source i`
does not implement tape access. The borrowed control vector is a logical field,
not an allocation or zero-initialization promise. No tape-time claim follows yet.

## Checked packed-field bridge

`PackedShear.lean` places the existing packed modular program over one fixed-width
rectangle, with its source bits read from a separate, unchanged field. That field
may also contain arbitrary spectator data. The length of the source list is fixed
for every source value, and each entry is proved to be zero or one.

- `program_source` preserves the complete source/spectator field on all addresses,
  including those outside the guarded region.
- `program_endpoint` proves that on the guarded region the actual packed program
  restores both borrowed fields, preserves every target digit above its low bit,
  and changes the low-bit list by XOR with the source list.
- `program_bad` proves that the exceptional set is preserved by the actual program.
- `repair_program` instantiates the existing exact-repair theorem on this rectangle.
  It is the destination-map identity, not a tape implementation of repair.

The endpoint is a structural statement over arbitrary list lengths and values;
no concrete addresses are enumerated. The guarded packed-module check peaks at
about 804 MiB.

## Checked coordinates, physical bits and source gathering

`Coordinates.lean` uses a complete equivalence between logical coordinates and
selected digit indices plus untouched coordinates. The explicit source descriptor
reads only the untouched factor. `program_decode` identifies the actual packed
program on good addresses with `Shear.shear`; `program_borrowed` connects it to the
logical dirty-control construction. This equivalence is not an implemented field move.

`PhysicalBits.lean` proves that width-`K` radix digit parities are the physical bits
at `K*j`, or `rho + K*j` after a lower prefix. The placement is injective and fits
inside the middle field. `program_physical` gives the actual program's XOR at each
physical target bit when `2*L = 2^K`. Upper digits and borrowed fields are preserved
by the full `PackedShear.program_endpoint` contract.

`SourceGather.lean` supplies real host execution for an increasing source-position
descriptor, including irregular gaps. It reuses `gather` and `gsProg`, then clears
the gathered temporary. `sourceOffset_exec` changes only its output register and
costs at most `8 W + 8 n G + 2 n + 18` steps, where `W` is the source width and `n G`
the compact width. `packed_read_eq` identifies this physical offset with the radix
pack of `Coordinates.read`, the value required by the modular load. The source and
both masks must already be present; constructing them and clearing the output after
consumption belong to the caller. Register-disjointness hypotheses must also be
instantiated there. This is not yet a complete rotation pass.

## Checked self-reading loads

`SelfRead.lean` closes the address-level source-stability obligation for upper
bits inside target digits. `earlyPass_good_upper` shows that each complete early
pass restores those bits, even though individual rotations may change them.
`selfRead` loads and unloads from the actual current upper digits. Both operations
are global permutations because their offsets do not depend on the rotated
control field. `selfRead_eq_frozen` proves agreement with the old constant-source
composition on the early good set, using the *newly loaded* controls in the second
pass. `selfRead_endpoint` restores both borrowed fields and all upper target bits.
The variable-source ideal is globally involutive, preserves guards, and supplies
`selfRead_bad` and `repair_selfRead`; no source copy or initialized field is assumed.
The reader may capture additional unchanged source/spectator values as parameters.

`SourceBits.lean` instantiates this reader with arbitrary ordered pairs of digit
indices and upper-bit indices. `selfRead_physical` proves the actual destination
bit at `K*j` is XORed with the specified physical source bit
`K*sourceDigit + upperBit + 1`. All indices are structural; there is no exhaustive
address enumeration. The checks peak at 804 MiB and 824 MiB respectively.

## Checked active-target masks

`Mask.lean` makes the active-target mask part of the modular program. `visible`
retains upper digits at active targets and the complete digit at inactive ones.
`maskedEarly_endpoint` preserves this source observation after each complete early
pass. `control_load_digits` proves no carries between loaded control digits on the
good set. `maskedFrozen_good` proves that two masked passes cancel arbitrary dirty
controls and implement exactly the active part of the requested source XOR.

`MaskedSelfRead.lean` reads the actual current `sourceView` for load and unload.
`maskedSelfRead_good` proves the selective endpoint, so sources can include low bits
of inactive digits. The ideal is globally involutive, the actual program preserves
the exceptional set, and `repair_maskedSelfRead` supplies the repair identity.
This is still address arithmetic. The complete masked physical-coordinate decoder
and its host field layout must be instantiated at the caller.

## Checked arbitrary-order source interpreter

`ReadRow.lean` scans one descriptor row while saving the source and descriptor bits,
then restores the source, in exactly `4 W + 4` host steps. `ReadRows.lean` composes
rows in their given order and restores the entire descriptor and output order.
Its execution theorem proves that only the output changes; all scan scratch returns
empty. `ReadOrdered.lean` instantiates rows with singleton masks of arbitrary source
positions. Repetitions and nonmonotone order are allowed. `readOrdered_exec` charges
exactly `n (6 W + 8) + 6` host steps for `n` requested bits in a width-`W` source.
The code is fixed; all source positions are descriptor data.

`ReadOffset.lean` composes that interpreter with spreading to compact digit starts
and clearing the gathered temporary. `readOffset_exec` charges at most
`n (6 W + 10) + 8 n G + 16` steps and changes only the compact output register.
`readOffset_value` identifies that word with the radix-packed source list used by
the arithmetic gadget. Source, descriptor, compact mask and scratch invariants are
explicit inputs. The caller must prepare the current source header, supply and
charge mask setup, consume/clear the output, and instantiate register disjointness.
The increasing-order reader in `SourceGather` remains available at its lower cost.

The masked-address checks peak near 810 MiB; the new host-reader checks peak
between 1,184 and 1,211 MiB. The public-root build and full axiom audit pass.

These are polynomial costs on address metadata. Their amortization against long
records, and the short-record fallback, remain caller/R3 obligations; no per-record
polynomial computation is silently charged as linear stream work. In particular,
repeated scans of the small header do not justify repeated elementary bit moves
of the entire record stream. Descriptor construction belongs to the uniform
router; no descriptor-specific unrolled program substitutes for this interpreter.

`Density.lean` proves that a complete nonempty source/spectator factor leaves the
exceptional fraction unchanged, and that a complete address equivalence preserves
it. `encoded_repair_density` imports the existing uniform bound under explicit
radix/gap inequalities. The concrete dyadic widths are now discharged by `SelectiveDensity`; the older
encoded statement remains available under its explicit inequalities at the caller. No initialized spectator or borrowed values are assumed.

Checks peak at approximately 817 MiB for coordinates, 814 MiB for physical bits,
1,197 MiB for source gathering, and 858 MiB for density.

## Existing building blocks and their boundaries

- `Compact/DirtyControl`: the four integer updates and dirty later-source parity
  identity. Reuse these rather than proving a second scalar gadget.
- `Compact/PackedControl` and `Compact/Permutations`: actual packed modular updates,
  no-carry correctness and global permutations. Their control lists do not by
  themselves identify arbitrary physical source coordinates in the router.
- `Compact/ExactRepair`: packed ideal maps and good-set agreement.
- `Compact/Repair` and `RepairPipeline`: generic exceptional-address repair and
  list-level extraction/sorting/reinsertion correctness. The pipeline explicitly
  does not supply tape execution of the scan.
- `MathlibTM2/Fast/CRTControl*`, `LayoutMove`, and the retained sorting programs:
  candidate physical rotations, placements and scans. Prove their exact headers,
  address layout, frame and cost hypotheses at each new call site.

## Checked physical masks and source-controlled host rotations

`MaskedBits.lean` instantiates the selective source observation with physical digit
and bit indices. `maskedRead_physical` permits inactive digit starts as sources and
excludes active starts. `maskedSelfRead_physical` proves the actual modular program
changes each physical target bit by precisely the active-mask/source XOR. Arbitrary
ordered descriptors are allowed. The check peaks at 828 MiB.

`SourceCode.lean` makes the ordered source reader a concrete `CodeSpec`, with a
fixed bank of index fields, descriptor, mask and scratch. Its `SourceInv` follows
the *current* index as routing and merging advance; no original source word is
saved. `sourceCode_spec` restores all stacks, clears the prepared offset, and
charges `n (6 W + 10) + 16 n G + 22` steps for source interpretation, spreading,
code evaluation and cleanup. It works over an arbitrary finite field bank.

`SourceRot.lean` instantiates both wrap-class callbacks with those actual programs.
`sourceRotate_exec` is a complete record-stream rotation pass. Its source field
must be above its compact target field, its record rectangle is complete, and its
cost is the existing `classMoveCost` with both source-code costs included. It
restores every register except the stream, including zeroed index counters, masks,
descriptors and scratch. This prices prepared source-controlled load/unload passes;
it does not assume callback execution as a hypothesis. The checks peak near
1,214 MiB for callbacks and 1,196 MiB for the rotation.

`SourceRotAlgebra.lean` identifies the executed target-digit rank map with signed
addition of the exact radix-packed source list modulo the compact field. Both
load and unload are identified on all addresses, without good-set assumptions.

## Checked live-header field-bank execution

`HeaderCode.headerCode_spec` gives the actual field-bank callback invariant:
all physical counters hold the live index, the metadata header starts/ends empty,
and descriptors/scratch are preserved. Its reindex proof follows actual counter
increments without changing their decomposition. The full callback cost is
`6 W + 6 count + 1 + L (12 W + 38) + 24 + 2 W + 2`, charging construction,
both interpreted patterns, the gate/carry code pass and header cleanup.
`HeaderRot.headerRotate_exec` supplies full record-stream execution with both
input/output callback costs and restoration of every stack except the record stream.

`HeaderFields` structurally enumerates every field above a target and proves both
contiguity and relative source-window bounds; gaps and spectators remain present,
and zero-width fields are allowed. `PlainPatterns` completes the Z/Y descriptors.
`HeaderOffsets` identifies executed A/Z/Y/YZ offsets with actual gadget field digits
and arbitrary ordered load/unload selectors with actual current address bits.
The optional zero sentinel remains metadata only; no physical borrowed field is
initialized or restricted. Parameter instantiation, setup and complete schedule
composition remain separate obligations.

## Checked complete masked instruction endpoint

`MaskedGadget` defines the actual masked instructions and projects each early pass
to the existing `CompactGadget.run_E` proof. The physical controls stay arbitrary;
only offset evaluation sees masked parities. `MaskedSlot` proves range, guard and
complete source-observation preservation, including prefix/suffix spectators,
active upper bits and complete inactive digits.

`MaskedSchedule` retains the actual twelve-rotation/twelve-interchange schedule.
`MaskedEndpoint` proves the fixed-source endpoint using the existing no-carry and
later-source identities; `MaskedDynamic` proves both loads read the actual current
source observation and therefore gives the complete dynamic-source endpoint.
`SlotSources` instantiates arbitrary ordered/repeated physical sources in the prefix,
target digits, suffix or an arbitrary-width outer spectator word. Active target low
bits are the only forbidden internal sources.

`SelectiveXor` identifies the whole endpoint with XOR by the exact sparse word of
actual source bits. `SelectiveIndex.selectiveRunIdx_good` transports the full
instruction schedule to one fixed physical record-index bank, least significant
first: b, y, t, u, spectator. It restores all borrowed fields and complete spectators,
including every bit above the bank. This is a checked instruction/rank theorem;
it does not yet compose the host programs or charge metadata transitions and setup.

## Checked complete prepared host execution

`SelectiveLayout` computes the actual source wires and suffix-header widths of the
fixed bank. `SelectivePatterns` identifies all five concrete descriptor tables with
the instruction rank offsets. `SelectiveRotations.selectiveRotate_exec` executes
and prices each rotation, including both live-header callbacks.
`SelectiveSwaps.selectiveSwap_exec` executes each actual b/t or b/u interchange,
including symbol/bit conversion, canonical header values, the full register frame
and the supplier-exponent bound.

`SelectivePrepared` retains one static descriptor bank per offset type and two
canonical interchange banks. There are no descriptor-specific unrolled programs
or repeated descriptor transitions; preparation and cleanup of all retained banks
still belong in the final wrapper and must be charged. The physical field bank
never changes its decomposition.

`SelectivePasses.selectivePrepared_exec` proves one actual `Exec` of the complete
schedule, changing only the record stream and restoring every prepared register.
The composed permutation has the physical good-set endpoint by
`selectiveProgramPerm_good`. `selectiveCost_sum` checks its actual multiplicities:
four A rotations, two each of Z/Y/YZ/X, eight b/t swaps and four b/u swaps, plus
one terminal sequence step. This is a full prepared execution, not an execution
oracle for individual passes. It still assumes prepared metadata and hence does
not close R1's setup/cleanup acceptance gate.

## Metadata installation and cleanup

`MetadataJob`, `MetadataInstall` and `MetadataClean` execute and price structural
installation and clearing of a fixed metadata bank. The concrete `SelectiveSetup`
installs 27 words: five field counters, ten descriptor words, two unary stream/block
counters and ten interchange headers. All source configuration tapes are restored.
The program reads binary counters; their numerical proof annotations do not alter
its structure. Setup establishes every `SelectivePrepared` condition.

`SelectiveProgram` composes setup, the complete prepared schedule and cleanup;
the complete execution and its physical good-set endpoint are checked. Its final register file differs from the
original only at the stream, and its bound adds all three phases. Stream separation
from metadata follows from `SelectiveHost.Valid`.

Raw descriptor words and canonical header bits remain input configuration, not
installed working metadata. Their generation is an R3 compiler obligation and
must be included in the eventual full router's cost.

## Completed concrete selective primitive

`SelectivePlacement` enumerates a fixed finite role bank. Every field, callback
scratch register, move register, swap-bank register and configuration source has
its own role; only each callback's target aliases its intended live field.
`placedSelectiveHost_valid`, `placedSelectiveHost_setup` and
`placedSelectiveHost_swapT` discharge the complete placement requirements.

`SelectiveDensity` uses the original compact all-ones-window count, generalized
to require only the three field lengths actually used. No width assumption is
made on the spectator field. The count is for `Good p (selectiveView p X i)`, the
same physical predicate as the executed endpoint, rather than a separately
encoded rectangle. `routingParameters` chooses `G = 4g + 6`, `K = 8g + 17`, with
`g = Nat.clog 2 scale`. For positive scale and `n ≤ scale`,
`routingParameters_clog_density` bounds the actual exceptional count by
`5 / (128 scale³)` times the complete record count, including every spectator value.

`SelectiveRouter.selectiveRouting_exec` joins concrete placement, canonical
interchange values, explicit guard widths, full setup/routing/cleanup execution,
its total cost, the physical XOR endpoint and the exceptional-count bound.
It has no abstract placement, prepared-header, prepared-counter, guard-gap or
radix-density assumption. Its raw configuration input remains explicit.
The program structure is independent of source order, dimensions and record count.

R1 is complete at this boundary; see the [requirement audit](R1-AUDIT.md).
R2 supplies the exact exceptional-record repair described below. R3 must generate configuration,
compose matchings and permutations, amortize the metadata cost and supply the
short-record fallback. R4 integrates the complete router and support contract.

Use the older [routing construction](../Balanced/DESIGN.md#b-the-selected-construction)
for the gadget and matching decomposition, and the pinned
[new outer support contract](https://github.com/zxv/integer-mult-bounds/blob/da637c87c89482bc4c86be36bd0071b3d400dbed/research/kappa-rebuild/transfer-audit/OUTER-TRANSFER-AUDIT.md#5-the-changed-row-reserve-fits-the-support-local-outer-wrapper)
for reserved chunks, complete spectators and exposure restoration. The old note's
parameter values and time estimates are historical, not current requirements.

The following R2 checkpoints describe the intermediate interfaces; the completed
entry point is `exactSelective_exec`, described after them.

## R2 checkpoint: exact selective repair from classified keyed input

`SelectiveIdeal` defines the desired physical sparse XOR on every index, including
failed guards. The source observation is invariant under this XOR without any
no-carry assumption (`slotView_xor_targetWord`). Allowed physical source reads
therefore remain unchanged. `selectiveIdealIdx_involutive` and
`selectiveIdealPerm` supply the all-address ideal permutation;
`selectiveIdeal_good` proves preservation of the same physical exceptional set.

`SelectiveRepairSpec` proves actual/ideal agreement on good ranks and bad-set
invariance of the actual schedule. `selectiveRepair_partition` instantiates the
existing repair mathematics: good records agree with the ideal stream, and a
stable radix sort of the exceptional destination keys gives exactly its bad
records. `selectiveBad_records` identifies extraction length with R1's physical
bad-rank count, without assumptions on payload values.

`SelectiveRepairPass.lean`’s `selectiveRepair_exec` instantiates the existing actual `repairAtC` scan/sort/merge/strip
program, restoring every register except the stream. Its explicit cost counts all
scan, sort, merge, key stripping and index-reset work. The exceptional-sort term
is bounded by `selectiveRepair_sortCost_density` using R1's physical density.

This is a prepared repair boundary, not completed R2. It requires an executed
classifier contract, already keyed input, initialized counters and register
separation. Next: implement the classifier and arbitrary-source destination key
pass, instantiate placement, execute and price setup/cleanup, and compose keying,
R1 and repair. The classifier must handle zero suffix width: the older `badC_eval`
requires a positive suffix to flush its final segment, while the R1 contract
allows zero. `selectiveBadCode_padded` now proves the value-level fix: one extra
column flushes the final segment, and neither the phase mask nor the guard
predicate depends on that padding. Its concrete tape execution is now supplied by `BadClassifier` below.

## R2 checkpoint: executed padded physical classifier

`paddedCopy_exec` in `PaddedCopy.lean` copies the actual target counter into an empty work
register with one high zero, charging the push and full binary copy.
`spreadPadded_exec` in `PaddedSpread.lean` spreads each borrowed counter into a word of
width `p.wy + 1`, preserving its source, mask and scan scratch. The extra column
is a mathematical/tape scan pad, not an added physical address field.

`badClassifier_spec` in `BadClassifier.lean`
executes the target copy, both spreads, the existing `badC` automaton and all three
word cleanups. It proves `CodeSpec` for exactly `selectiveBadCode p X`, on the actual
five-field bank with arbitrary spectator width. Every register is restored; the
scan slot carries the computed code. The explicit bound is `34 * p.wy + 62`,
including all word preparation and cleanup, and the check peaks near 2.1 GiB.

This removes the executed-classifier obligation at the prepared repair boundary.
Its two masks and field counters remain explicit invariant inputs: their charged
installation/cleanup and concrete shared placement belong to R2's final
composition. The later keying and final installation/composition sections discharge those
remaining obligations; this classifier alone is not the complete R2 primitive.

## R2 checkpoint: complete key layout and executed target digit

`SelectiveKeyLayout` appends one high row counter to the existing five-field
bank. `selectiveKey_digit` proves original digits are unchanged, and
`selectiveKeyDig_ideal` proves every proposed key digit is the ideal destination
digit, including its row. `selectiveKeyBits_ideal` and `selectiveKeyedFrom` identify
the full binary key with the exact `keyRecs` representation required by repair.
`selectiveKey_rank_bound` proves the complete rank fits when the row counter fits;
keys from different rows are not silently truncated to their in-row address.

`SelectiveKeyPattern` describes the sparse target word as one executable optional
source table over the current y/t/u/spectator header. Active targets read their
specified source, inactive targets request zero. `selectiveKeyPattern_value`
identifies its interpreted value with the actual `targetWord` used by the ideal
permutation, with no source-order or source-injectivity assumption.

`headerRead_exec` in `HeaderRead.lean` builds that header from current counters,
interprets the table and clears the header. `patternKey_exec` in `PatternKey.lean`
then emits the XOR digit through the existing `xorF`, restoring its full mask,
all source counters, descriptor and scratch, and clears the source-word temporary.
`selectiveKeyTarget_exec` instantiates this on the physical five-field bank.
Its fixed cost is `wy * (6 * W + 25) + 8 * W + 45`, where
`W = wy + 2 * wc + X`; it includes every header copy, interpreter scan, XOR and
cleanup. All new modules check at about 1.2 GiB.

This target-emitter boundary is composed with copies of all other fields,
including the row, by the complete key pass below. That pass executes the record
loop, restores forward stream order and resets every index counter. The
key/header descriptor and full mask remain configuration inputs whose installation
and cleanup belong to the final R2 composition.

## R2 checkpoint: executed whole-stream destination keying

`KeyEmission` factors the old concrete key-loop construction around
`KeyEmissionSpec`, the contract of an executed key emitter. `keyRecord_exec`
performs key emission, the actual payload transfer, counter increment and source
peek. `keyRecordLoop_exec` proves the structural loop, including its exit step.
`keyStream_exec` moves the accumulator back to forward stream order and resets
all field counters; its final stack bank differs from the initial bank only at
the source stream. It charges every loop, copy, move and reset.

`SelectiveKeyEmitter` supplies the concrete emitter for all six key fields.
Only the target digit uses descriptor interpretation and XOR; the other five,
including the row, use the existing executed field-copy program. The emitter
shape is independent of all dimensions and source descriptors. Static descriptors
and all scratch survive every iteration through `KeyPatternInv`.

`selectiveKeyPass_exec` in `SelectiveKeyPass.lean` combines these checked programs
into the complete executed selective key pass. Its output is exactly
`keyRecs (fieldsLen (selectiveKeyLen ...)) (selectiveIdealPerm ...) l` and its cost
is the explicit `selectiveKeyPassCost`. This supplies full stream keying rather
than only destination arithmetic or a hypothetical key callback. The existing
`selectiveKey_rank_bound` must be used with the row-width bound before sorting,
so distinct full ranks are not truncated to equal keys.

The whole-stream key pass checks near 1.2 GiB. Its prepared key/classifier
invariants are discharged by the shared placement and final executed metadata
installation described below. The full primitive also includes their cleanup
and the all-address, density-priced composition.

## R2 checkpoint: one concrete shared key/route/repair core

`HostEmbedding` transports `SelectiveHost.Valid` and `SetupLayout` through an
injective register embedding. `RepairPlacement` then embeds the old finite R1
bank in a larger fixed role bank. Its five physical counters are also the first
five key counters and all classifier counters; only keying has the sixth row
counter. All other key/classifier scratch has separate roles. The payload-length
and key-length counters are distinct from routing's keyed-record-length counter.

The checked placement discharges the key-driver contract, every scan/merge register
separation, classifier index isolation, sort scratch injection and sort/field
separation. It also preserves the original routing setup contract and proves the
swap banks fit. No phase-specific counter bank is substituted at composition.

`RepairPrepared` in `RepairCore.lean` states the simultaneous prepared invariant:
routing metadata for records of length `keyWidth + B`, the complete key-emitter
and physical-classifier invariants, original payload/key-length counters and an
empty accumulator. `repairCore_exec` executes keying, the entire actual R1
schedule, and `repairAtC` with `badClassifier`. Its result is the exact ideal stream
on every address and its full register file is restored except for the source
stream. `R ≤ 2^rb` supplies the complete-key rank bound for the sort. Its real cost
is the explicit sum of full key-pass, routing-pass and repair-scan costs, including
the physical exceptional-sort term. The core checks near 2.1 GiB.

This is still a prepared boundary. The final R2 primitive must install and clear
all routing and extra metadata with actual charged programs, initialize the row
and payload/key counters, use concrete canonical headers and guard widths, and
combine the physical density estimate with the complete cost. Descriptor/header
generation remains the documented later R3 input-compiler obligation; installation
and cleanup are required here. Do not close R2 on `repairCore_exec` alone.

## Completed R2 primitive: installation, exact execution and cleanup

`RepairSetupBank` enumerates the fixed 34 metadata destinations: routing's 27 and
seven extra words for the row, key descriptor/full mask, classifier masks and
payload/key-length counters. It proves destination uniqueness and separation of
all raw sources, installer temporaries and the stream. `RepairSetupBlank` proves
that no installed word replaces required blank scratch in any phase.

`RepairSetupData` states the raw configuration and the fixed installation jobs.
The row is constructed as a zero binary counter; payload and key-length unary
counters are constructed from binary inputs. Descriptor/mask copies and canonical
header separator installation are real programs. `repairSetup_eq` proves that
all numerical annotations leave the program structure unchanged.

`repairSetup_exec` in `RepairSetup.lean` executes and prices the complete installer,
restores its raw inputs/scratch and establishes every `RepairPrepared` condition.
The shared `selectivePrepared_of_words` constructor factors the original R1 proof;
the R1 setup theorem and its interface are preserved.

`repairProgram_exec` in `RepairProgram.lean` surrounds the concrete key/route/repair
core with installation and final metadata clearing. Its complete register file is
an update of the original bank only at the stream. No prepared classifier, key,
metadata, placement or per-phase execution assumption crosses this boundary.
Its bound adds all installer, key-pass, routing-pass, classifier/scan/sort/merge/
strip/reset and cleanup costs.

`RepairDensity` replaces the actual exceptional-sort count in that total by the
physical `5 / (128 scale³)` density estimate. The count is for the same predicate
used by the executed classifier, over all rows and spectator values. `ExactSelective`
fixes canonical interchange header values and ceiling-logarithm guard widths;
`exactSelective_exec` proves exact ideal output on **every** address under this
fully priced density bound. All new setup/final modules check near 2.1 GiB.

R2 is complete at this boundary; see the [requirement audit](R2-AUDIT.md).
Raw configuration generation is still the R3 input-compiler obligation, not a
free generation claim. R3 must also compose matchings, reservoir placement and
permutation decomposition and supply the short-record fallback. R4 integrates
the complete router and support contract into multiplication; kappa is unchanged.

## R3 logical schedule checkpoint

`ReservoirPartition` assigns every matching edge to the first of three disjoint
reservoirs missing both endpoints. Each class fixes its reservoir.
`MatchingShears` orients edges by coordinate order and implements each class with
three directional XORs. `ReservoirSchedule` proves their nine-shear composition.
`ReservoirBudget` constructs three consecutive banks of width `3H`, with
`H = (n / (64G) + 1)G`; they fit whenever `64G ≤ n`. This harmless extra block
also covers exact divisibility. Router parameters use `K = 64G`; the generic R2
execution and density proofs already permit this wider spacing.

`PermutationMatchings` uses bounded orbit traversal and the least orbit coordinate
to compute cycle reflections. Its exponent search is proved less than the total
coordinate count. The two reflections are involutions whose composition is the
original permutation; `permutationReservoirSchedule_eq` proves the resulting
eighteen-shear address identity.

`ResidueShears` proves source-preserving composition for any finite partition,
then instantiates all residues. `SparseProfiles` uses exactly `(n-r)/K` slots for
residue `r`: each has a complete segment and quotient/remainder recover every
such coordinate. `ProfileCompiler` fixes prefix and suffix widths to preserve the
entire target field; its borrowed width fits the common reservoir. `SourceCoordinates`
encodes any preserved target-field bit using R2's low/digit/high constructors.
Active descriptors read their requested source; inactive slots read themselves,
which satisfies R2's source condition even when unused original descriptors would
have pointed at active targets. This is a computable descriptor construction,
not its executed tape generator.

`TerminalShears` partitions targets into complete-segment and terminal regions.
The terminal set has at most `K` elements, and its singleton-XOR schedule composes
with the residue passes to give the complete original shear. Thus the last segment
is explicitly accounted for rather than dropped.

The target-field-only profiles above do not by themselves allocate borrowed
fields inside the original record. `RouterGeometry` resolves that constraint:
choose a common digit count `d = (n-K)/(K+3G)` and compact width `w=dG`. The target
field has width `n-3w`; every residue uses the same `d` digits, with prefix `r` and
suffix `routerTail-r`. Division with remainder proves the total field bank is
exactly `n` bits and the elementary suffix is shorter than `2K+3G`, hence `131G`
for `K=64G`. Every bulk coordinate occurs in a fixed-count profile, whose targets
all stay outside that suffix. The compact width fits the common reservoir.

`BlockExchange` gives an explicit involutive equal-width interval permutation.
`ReservoirPlacement` first exchanges the complete selected reservoir with the
front bank (or does nothing for bank zero), then moves two compact slices to the
end. It proves every borrowed position of the resulting `b,y,t,u` layout originates
in that reservoir. `PlacementShear` conjugates both source and target coordinates,
proves the original shear after unplacing, and preserves arbitrary reservoir
contents. Transported matchings still fix the reservoir and cannot read into it
from live coordinates.

`BlockExchangeIndex` identifies the actual digit-interchange rank map bit by bit
with `blockExchangePerm`, preserving the row above the record. `BlockExchangeExec`
specializes the existing uniform host program, including conversion, movement,
private scratch restoration and supplier-exponent cost. `BlockExchangeChain`
executes a structural list of exchanges from initially prepared banks: each actual
call restores every register except the shared stream, preserving later headers
and their cost terms. No per-stage execution oracle is assumed.

`ReservoirExchangeSchedule` specifies the three concrete exchanges, including a
zero-width first call for reservoir zero so the program shape is fixed. Its rank
action is exactly `reservoirPlacement`. `reservoirPlacement_exec` executes both
forward and reverse schedules and charges every call, leaving only the stream
changed. Canonical header banks are still initially prepared inputs; generation,
installation and final cleanup remain unproved at this boundary.

Complete composition with executed R2 calls and terminal-coordinate operations,
uniform configuration generation and amortization also remain open. Those and the short-record fallback remain mandatory R3 gates.
In particular, computable Lean functions are not yet a priced tape compiler.

## Completion gates

R1 ends with packed good-set semantics and priced host calls; R2 supplies exact
all-address repair and its cost. R3 composes matchings/reservoir placement,
permutation decomposition and the short-record fallback into a complete router.
R4 replaces forward/inverse layout movement and proves the support contract for
grouped resampling. A cheaper symbolic layout bound alone completes none of these.

Keep all finite checking structural and split certificates by declaration. Use
the guarded Lean scripts and the standard-axiom audit. The existing multiplication
theorem remains the public result until the new programs and all costs are integrated.
