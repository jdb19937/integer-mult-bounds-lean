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

## Canonical words

`PauliCanonical.lean` assembles the source recipe `K C_r K⁻¹` as an explicit
word of these realizations: `D_Q⁻¹`, `P_G⁻¹`, the C gates on axes `0..r-1` in
increasing order, `P_G`, `D_Q`. The quadratic matrix is the exact matrix of
`Q = I + G⁻ᵀ G⁻¹`, proved symmetric for the binary dot product, with the
source's default alpha. `canonicalRealization_binary` proves that the word's
binary projection is exactly `Tableau.canonical G r`;
`sourceCanonicalRealization` follows all three `canonical_frame` branches and
projects to `sourceCanonical`. `nativeRealization i` is the word at selected
frame `i`; it projects to `nativeTableau i`, so its inverse-Z image is that
frame's Lagrangian. The scalar operators and phase-bearing label maps of these
words are genuine and exact, but no particular phase on the image of a given
Pauli is asserted beyond what the realization fields state.

## Soundness of the source equality test

`PauliSchur.lean` proves Pauli irreducibility on the 512-dimensional state
space: a linear map commuting with every X label and every Z generator is the
scalar `M |0⟩ (0)`. Consequently `Realization.scalar_eq_smul` shows that two
realizations whose label maps agree on the eighteen generators have scalar
operators differing by one global constant, and `Realization.scalar_eq` shows
that agreement on the zero basis state as well makes them equal. This is
exactly the source's `compiled.tab == op.tab and compiled.zero_state() ==
op.zero_state()` test, with the tableau comparison read phase-exactly on
generators.

## Generic Clifford elimination

The 2,896 serialized child recipes are replaced by a generic theorem.

- `PauliCorrection.lean`: realization label maps are multiplicative, a Pauli
  operator determines its label, and two realizations with the same binary
  tableau differ by a Pauli operator and a global scalar
  (`Realization.eq_pauli_smul`).
- `BinaryElimination.lean`: every symplectic map is a monomial (address
  permutation, then symmetric quadratic shear), the coordinate Hadamard
  `S C_r S` on `r = dim xRange` axes, and another monomial
  (`Tableau.elimination`). Z-preserving symplectic maps are monomial, and every
  subspace is a frame space.
- `PauliLowering.lean`: realization tableaus are symplectic, realizations
  have exact inverses, and `Realization.lowering` combines the two results.
  `edgeRealization a b` is the exact transition `T_b T_a⁻¹`; `edge_lowering`
  writes it, up to a global scalar, as monomial, `S C_r S`, monomial and Pauli
  operator, with `r` the relative X-block rank that the native trace theorems
  identify with each certified climb and centre rank.

The global scalar is not yet pinned to `±1, ±i`; the source's per-recipe
`phase` field is therefore not reproduced. Monomial and Pauli factors are
address permutations with fourth-root phases (plus that scalar), so they make
no child call.

## Remaining obligations

Serialized monomial-factor decoding and equality of whole
complex residual recipes remain open. Adapter semantics, dirty scalar routing,
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
