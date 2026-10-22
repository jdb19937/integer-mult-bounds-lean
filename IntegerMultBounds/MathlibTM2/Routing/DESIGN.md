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

**Sources inside the target field remain an obligation.** The current packed
reader depends on a separate unchanged factor. A general shear may read unselected
upper bits of target digits themselves. Those bits return to their original values
after each complete dirty-control pass, but can change during its rotations. The
load must read the actual intermediate state, and its stability must be proved;
copying those bits into the separate source factor is not a free solution.

**Ordering is a real remaining obligation.** A mask scanner emits sources in
increasing physical order. It does not implement an arbitrary `Fin n -> coordinate`
ordering. The general mathematical endpoint accepts arbitrary ordering, but the
host reader currently proves only increasing order. The next source-order bridge
must supply and price reordering or an appropriate physical placement. Relabeling
logical coordinates alone does not implement that placement on a record stream.

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

## R1 next: complete the priced host program

1. Generalize the load to read preserved upper target bits from the actual
   intermediate state, and prove source-read stability after each dirty-control
   pass. Then close source ordering: connect arbitrary source descriptors to an executable
   arrangement or reorder, while retaining the complete spectator tensor. The
   ordered mask scan alone is insufficient.
2. Bind the packed fields to physical record-index fields and implement their
   interchanges. Instantiate actual field order, width and header hypotheses;
   a coordinate equivalence is not a tape program.
3. Feed the concrete source offset into the modular load/unload rotations. Reuse
   existing wrap-class automata and `cxRot_exec` where their hypotheses apply;
   generalize the source code program where they do not. Compose both dirty-control
   passes with all loads, moves and inverses, proving scratch and spectator frames.
4. Charge source/mask setup, every rotation and interchange, and cleanup. Instantiate
   radix widths and the density inequalities. End with one host `Exec` theorem and
   its cost on the good set. R2 then supplies all-address repair execution.

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
