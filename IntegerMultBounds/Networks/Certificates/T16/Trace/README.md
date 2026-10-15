# Exact T16 native event traces

This isolated checkpoint imports the R480 local supplier's complete forward
and backward native event lists, preserving their order, rational numerators
and denominators, climb/center records, adapters, residual wrappers, and phase
markers. It does not replace the separately committed finite-charge certificate.

`Model.lean` defines the source-specific checked label transition system.
The scalar convention is target-first. Add and scale check every touched
wire's declared frame. Copy checks its source frame and overwrites private
scratch; clear actually zeros private scratch and assigns its declared label.
Climb and center transitions check old labels, new-label bounds, and ranks.
Adapter and residual records remain explicitly checked metadata; no identity
operator is inferred from them. Phase markers enforce the exact ten-phase order.

Labels use a finite binary trie, with each low index bit selecting a branch.
Every generated state has ten levels, covering all 712 registers. The initial
704 local labels come from the canonical start profile; the eight private labels
start at zero. These labels do not assert that any stored scalar input is zero.
Chunk boundary snapshots and successful runs are checked by Lean's kernel.
`Properties.lean` spells out the touched-frame consequences and the decomposition
of successful runs into successful individual transitions.

The generated orientation modules expose their complete event list, scalar
erasure, initial/final states, and a successful-run theorem. The source-specific
`Valid` predicate means that every retained native event passes its transition
checks. The importer also independently replays all labels and compares the
local final profile with the canonical final profile before emitting files.

This checkpoint does **not** supply frame linear equivalences, prove rank or
frame independence, interpret physical adapter operators, verify the full
rational matrix, or prove the dirty scalar routing identity. In particular,
private clears do not restore arbitrary dirty private inputs. It also does not
provide physical tape allocation, global scheduling, or a tape-cost bound.

Regenerate with `python3 scripts/generate_t16_trace.py SOURCE_DIRECTORY`.
The importer reads only the hash-pinned compressed JSON and notice files; it
executes no supplier program. `trace-provenance.json` records the pins and
representation. Original licenses and notices are retained byte-for-byte.

## Verification checkpoint

All 56 Lean modules in this directory passed guarded single-file checks with
default proof limits. The focused namespace audit checked 27,443 declarations
and found only the standard permitted axioms. Deterministic regeneration matched
all 60 generated files. A separate parser reconstructed both emitted event lists
and matched all 24,767 source events per orientation exactly. Corrupt source hashes
were rejected before output creation. No full build or main-graph import was used.
