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
