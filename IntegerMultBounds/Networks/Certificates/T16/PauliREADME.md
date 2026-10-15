# Exact complex C/P/D primitive realization

This checkpoint connects source primitive gates to genuine complex linear
equivalences on the 512-dimensional state space. It proves phase-exact
conjugation identities for every Pauli, rather than inferring operator equality
from a binary tableau.

## Source conventions and exact operators

The source compiler and its pinned hash are recorded in `TableauREADME.md`.
Its Pauli convention is `i^p X^x Z^z`, with X acting after Z, and its `then`
method applies the left gate first. `Pauli.lean` retains the full Z/4 phase in
`Label`; `operator` implements that convention on complex arrays.
`operator_multiply` proves the source multiplication correction
`p + q + 2 (z · x')`.

The actual C operator is the existing `BinaryWalsh.kernel 1 q`, packaged as
an equivalence whose inverse is `kernel (-1) q`. Its coefficients are exactly
`(1+i)/2` and `(1-i)/2`; the inverse swaps them. `PauliC.lean` proves that
conjugation sends `(x,z,p)` to
`(x + (q·z)q, z, p - bitLift(q·z))`. The inverse adds the phase correction.
`PauliGenerators.lean` checks that affected Z generators receive the source's
stored exponent 3, while X generators remain unchanged. The binary projection
is the actual rank-one shear `cBinary`.

The actual permutation is `f ↦ f ∘ G⁻¹`, with inverse `f ↦ f ∘ G`.
Conjugation sends `(x,z,p)` to `(Gx,G⁻ᵀz,p)`, including zero added phase.
Both forward and inverse conjugation are proved, and the binary projection
agrees with the frozen `Tableau.perm`.

The actual D gate multiplies each state amplitude by the source polynomial's
fourth-root phase. `PauliDiagonal.lean` defines
`sum alpha_i bitLift(x_i) + 2 sum_{i<j} Q_ij x_i x_j` modulo four.
`qValue_source` proves equality with the literal product-of-bit-lifts formula.
For symmetric Q and the source alpha parity condition, its polarization is
proved directly by finite sums. `PauliDiagonalAction.lean` then proves exact
conjugation
`(x,z,p) ↦ (x,z+Qx,p+qValue(x))`, with the opposite phase for the inverse.
The source X-generator phase is exactly `alpha_i`; Z generators are fixed.
The binary projection is the frozen `Tableau.diagonal Q.mulVecLin`.
`alpha_compatible_iff` proves that the compatibility hypothesis is precisely
the source test `alpha_i.val % 2 = Q_ii.val`; `defaultAlpha` is its standard
zero-or-one diagonal choice.

## Composition and global phase

`PauliSource.lean` packages actual complex operators, full phase-bearing Pauli
label maps, binary equivalences, and both correctness proofs in `Realization`.
Composition and finite words preserve all these facts in the source's order.
`PauliInverse.lean` provides inverse C/P/D realizations and an actual uniform
global-phase operator. Its conjugation is explicitly proved invisible to Pauli
labels, while its scalar operator is still retained. This is why the record
must not be interpreted as a tableau-completeness theorem.

## Remaining obligations

The complete canonical word has not yet been assembled from these primitives,
nor linked to every selected native tableau through its exact quadratic matrix
and partial-C word. Serialized monomial-factor decoding and equality of whole
complex residual recipes remain open. Equality of tableaux plus a zero-state
vector has not been proved complete. Adapter semantics, dirty scalar routing,
private-scratch restoration, hosting and tape costs remain separate.

No frozen finite geometry, binary tableau theorem, or literal extension import
file is changed by this checkpoint. No nondegeneracy assumption on a selected
frame restriction is used.

## Verification

All seven new Lean modules passed the memory-guarded single-file checker with
zero warnings and unchanged default proof limits. The namespace axiom audit
passed for 164 declarations, allowing only `propext`, `Quot.sound`, and
`Classical.choice`. The largest recorded module peak was 1158.2 MiB; the audit
peak was 1130.8 MiB. A source hygiene scan found no proof placeholders, new
axioms, unsafe declarations, native decision shortcuts, or option overrides.

The 65-file trace, 185-file geometry, five-file tableau theorem, and 38-file
literal-extension checkpoints were verified byte-identical to their manifests.
This checkpoint freezes the seven `Pauli*.lean` modules and this README.
