# Exact T16 source extension matrices

This separate finite import instantiates the frozen binary-tableau theorem
checkpoint with all 1,004 selected frame extensions. It does not modify that
checkpoint or the frozen geometry and trace certificates.

`scripts/generate_t16_tableau_frames.py` reads hash-pinned canonical frame data
and verifies the hash of the inspected Clifford compiler. It never imports or
executes supplier code. It reconstructs `basis_extend` by keeping the original
ordered columns and then greedily adding standard unit vectors in increasing
bit order whenever the candidate lies outside the accumulated XOR span. The
source's criterion is a rank increase; an independent Gaussian-rank replay
checks that the emitted matrices match that criterion exactly.

Each literal nine-column matrix has nine literal dual masks.
`TableauFramesModel.lean` proves that the checked pairings provide a left
inverse, hence an actual invertible address map, and turns literal retained
column equations into the `FrameExtension` interface. The dual masks are the
actual inverse rows. These finite equations use ordinary kernel-checked
`decide`, with no imported supplier theorem, `native_decide`, or proof-limit
increase.

`TableauFrames0.lean` through `TableauFrames31.lean` contain the exact matrix
witnesses. `TableauFramesCatalog.lean` selects them by original frame ID and
proves that its frame component agrees with the committed geometry catalog.
IDs outside the native range share that catalog's empty-frame fallback.
`nativeTableau` then applies the actual source recipe, including its identity
and full-C branches at ranks zero and nine.

`TableauNative.lean` proves the unconditional inverse-Z identity for every
selected matrix and the actual relative X-block rank for every retained native
climb and center event, in both orientations. Forward descending centers use
rank symmetry while retaining the actual old-to-next operator order. Scalar,
adapter, and wrapper events add no rank assertion. The original committed
trace definitions are used directly.

This certifies binary tableaus and their actual X-block ranks. Complex Pauli
conjugation, phase-aware operator equality, serialized monomial factors,
adapter semantics, dirty scalar routing, private-scratch restoration, physical
hosting and tape costs remain open as described in `TableauREADME.md`.

Regenerate with `python3 scripts/generate_t16_tableau_frames.py SOURCE_DIRECTORY`.
`--output DIRECTORY` supports deterministic comparison; `--probe` emits the
first matrix batch only. Pins and source conventions are recorded in
`tableau-frames-provenance.json`. Original byte-identical licenses and notices
remain beside the frozen Trace certificate for this same source package.

## Verification

All 35 new Lean modules passed guarded checks with default proof limits and no
warnings. The combined binary-tableau namespace audit passed for 5,185
declarations, allowing only `propext`, `Quot.sound`, and `Classical.choice`.
Peak module RSS was 1,199.0 MiB; audit RSS was 1,145.6 MiB.

All 34 generated files reproduced byte-for-byte. Independent parsing verified
all 1,004 ordered extension matrices against a separate Gaussian-rank greedy
reconstruction, and their dual masks against Gaussian-eliminated inverse rows.
Corrupt pins and Python optimization were rejected. The frozen 185-file geometry
manifest and five-file tableau-theorem manifest remained unchanged.
