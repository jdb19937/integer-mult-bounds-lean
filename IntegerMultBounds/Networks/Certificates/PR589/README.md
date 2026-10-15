# Complete selected PR589 scalar word

The pinned 5583-instruction word executes on 661 registers over `ZMod 2`.
`DirtyEndpoint.lean` proves its complete scalar action on arbitrary dirty stored
inputs: the 111 sources and 439 helpers are restored, and each of the 111 targets
receives its original value plus its corresponding original source.
`FiniteWord.lean` restricts the literal program to `Fin 661`, retaining all 5583
instructions and proving the same dirty endpoint. `Counts.lean` certifies 24305
elementary source additions; a multi-source instruction is not one tape step.

The proof uses a deduplicated mask bank and 235 independently checked replay
chunks, composed across D, A, scatter, B and C. Every chunk, section composition,
full replay and endpoint passed guarded checks with default proof limits. The
complete scalar namespace audit covers 14586 declarations and permits only
`propext`, `Classical.choice` and `Quot.sound`; the four finite-adapter contracts
passed a separate standard-axiom audit. No full build was used.

This proves the scalar program only. Retained frame metadata is not yet a frame
interpretation or rank certificate. In particular, the scatter boundary needs
its literal COPY interpretation in the framed construction; scalar endpoint
correctness does not justify a common-frame substitution there. Geometric ranks,
nesting, physical hosting, tape costs and the primitive exponent remain open.
The running multiplication theorem does not import this checkpoint.

The pinned source digest, generator and original licenses/notices accompany the
literal word. No source supplier program is executed during import.

## Checked frame-state compiler bridge

`Frames/` now tracks every physical register's frame through D/A, the literal
527-incidence logical scatter boundary, B/C and final alignment. The complete29250 phase
incidences are retained, including identity transitions. The exact old/new
frame pair lists and phase endpoints are identified with the existing
`FramedCircuit` compiler for any supplied frame interpretation. Scatter sources
keep their frames510–518 and targets use frame0; no common-frame replacement
is assumed. All230 non-scatter replay chunks, section composition, generic
compilation and boundary modules pass guarded checks. The focused namespace
audit covers1760 declarations using only the standard three axioms.

These are exact frame-state and compiler identities. They do not supply
the selected rational E8 frame operators, their compatibility with binary
scalar data, distinct-frame COPY execution, geometric ranks, physical hosting
or tape costs. Those remain prerequisites for a primitive-bound improvement.

The logical scatter incidences are not physical COPY counts: the source uses
nine COPY/ERASE buffer lifecycles through temporary register661, with527
intervening frame-zero ADD incidences. Those charged buffer lifecycles have
not yet been implemented by this frame-state checkpoint.
