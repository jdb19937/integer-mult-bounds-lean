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
radix/gap inequalities. The chosen dyadic widths must still discharge those
inequalities at the caller. No initialized spectator or borrowed values are assumed.

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

## R1 next: complete the priced host program

1. Bind the complete physical field layout, including prefix/suffix spectators,
   to the masked arithmetic rectangle and the actual source-index descriptors.
2. Implement and price the masked and mixed-control callbacks for both early
   passes. Plain source-controlled rotations are now implemented. The temporary-
   times-control and masked-XOR offsets still need concrete callbacks. A fixed
   source interpreter with a temporary zero sentinel in its *metadata* source
   word can supply zero at inactive control positions, restoring the source word
   afterwards; never initialize or restrict a physical borrowed field for this.
3. Bind the field interchanges with their actual order, width and canonical header
   hypotheses. A different decomposition of index-counter fields must be backed
   by priced counter setup/reset; it is not a record-coordinate move.
4. Charge descriptor/mask/counter setup, every rotation and interchange, and
   cleanup. Instantiate radix widths and the density inequalities. Compose one
   host `Exec` theorem and total cost for the complete good-set shear. R2 then
   supplies all-address repair.

Use the older [routing construction](../Balanced/DESIGN.md#b-the-selected-construction)
for the gadget and matching decomposition, and the pinned
[new outer support contract](https://github.com/zxv/integer-mult-bounds/blob/da637c87c89482bc4c86be36bd0071b3d400dbed/research/kappa-rebuild/transfer-audit/OUTER-TRANSFER-AUDIT.md#5-the-changed-row-reserve-fits-the-support-local-outer-wrapper)
for reserved chunks, complete spectators and exposure restoration. The old note's
parameter values and time estimates are historical, not current requirements.

## Completion gates

R1 ends with packed good-set semantics and priced host calls; R2 supplies exact
all-address repair and its cost. R3 composes matchings/reservoir placement,
permutation decomposition and the short-record fallback into a complete router.
R4 replaces forward/inverse layout movement and proves the support contract for
grouped resampling. A cheaper symbolic layout bound alone completes none of these.

Keep all finite checking structural and split certificates by declaration. Use
the guarded Lean scripts and the standard-axiom audit. The existing multiplication
theorem remains the public result until the new programs and all costs are integrated.
