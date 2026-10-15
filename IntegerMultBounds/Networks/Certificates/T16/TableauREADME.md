# T16 canonical binary tableau theorem checkpoint

This checkpoint defines actual linear equivalences on the doubled nine-bit
address space. It proves the inverse-Z subspace identity for the explicit
canonical recipe and derives the actual relative-tableau X-block rank by
transporting its kernel and applying rank-nullity. It does not assume an
inverse-Z identity as an input theorem.

## Exact source convention

The inspected supplier source is
`research/complex-sw4-frame8/vendor/main/research/complex-k492-owner-repair/vendor/multicold/vendor/pr558/vendor/pr552/complex-global/vendor531/vendor/clifford/clifford_exact.py`,
SHA-256 `2982ead07721e83358dc67c6f49c2b4c16a236a6bebdfd72f58221be1f5d0962`.
Its `perm`, `diag`, `cgate`, `fourier`, and `canonical_frame` definitions occur
at lines 102–126; `lower_child` computes the X-block rank at lines 133–149.
No supplier code is executed for these proofs.

The source encodes Paulis as `i^p X^x Z^z`. This checkpoint deliberately forgets
`p`. Its `then` method applies the left argument first, as does Lean's
`LinearEquiv.trans`. The binary coordinate C gate sends `(a,b)` to
`(a + P_r b,b)`; it is not a Walsh coordinate swap. The complex source gate is
`((1+i)/2) I + ((1-i)/2) X`.

`Tableau.lean` implements:

- the actual transpose via the nondegenerate ambient binary dot-product dual;
- `perm G : (a,b) ↦ (G a,G⁻ᵀ b)`;
- `diagonal Q : (a,b) ↦ (a,b + Q a)`;
- `partialC r : (a,b) ↦ (a + P_r b,b)`;
- `quadratic G = I + G⁻ᵀ G⁻¹`, `conjugator G = D_Q P_G`;
- `canonical G r = K C_r K⁻¹`.

It proves the direct Z-column formula and
`canonical_inverse_Z`: the inverse image of the standard Z subspace is
`L_U = {(u,u+v) : u ∈ U, v ∈ U⊥}`, where
`U = range (G ∘ P_r)`. This works when the restriction of the dot product to
`U` is degenerate or isotropic.

`TableauSource.lean` follows all branches of `canonical_frame`: rank zero uses
the identity, rank nine uses the full coordinate C gate, and intermediate
ranks use conjugation. Its `sourceCanonical_inverse_Z` proves the same exact
subspace identity in each case. The full-rank branch matters: for arbitrary
nonstandard `G`, the generic conjugation need not equal the full C gate.

## Relative rank and retained frames

`TableauRank.lean` defines the actual relative tableau `B A⁻¹` and its X block
on the standard Z generators. It proves
`rank Bblock = 9 - dim(A⁻¹ Z ∩ B⁻¹ Z)` by an explicit injective kernel map with
that intersection as its range. Combined with the previously certified
Lagrangian intersection theorem, the explicit canonical recipes on nested
frame spaces have X-block rank `dim V - dim U`.

`TableauCertificate.lean` provides `FrameExtension`: an invertible address
matrix plus a proof that its initial columns retain the original ordered mask
vectors. `FrameExtension.space` proves that its initial-column space equals
the certified frame's actual span. Native climb and center rank theorems then
apply to both retained event lists; forward descending centers use the proved
symmetry of relative X-block rank. These theorems explicitly take extension
witnesses. This checkpoint does not supply the source's 1,004 literal greedy
extension matrices; their separate finite import must satisfy this API.

## Scope still open

No complex operator realization, Pauli conjugation soundness/completeness,
serialized monomial-factor identity, or global-phase statement is proved here.
In particular, the source's equality test using a tableau and a zero-state
vector has not been justified in Lean. Adapter semantics, full dirty scalar
routing, arbitrary private-scratch restoration, physical hosting and tape costs
remain separate obligations. No assumption of nondegeneracy on a selected
frame restriction is introduced.

## Verification

All four Lean modules passed guarded targeted checks with default proof limits
and no warnings. The focused namespace audit passed for 104 declarations using
only `propext`, `Quot.sound`, and `Classical.choice`. Peak final module RSS was
1,140.0 MiB; audit peak RSS was 1,137.2 MiB. The frozen 185-file geometry
checkpoint remains byte-identical.
