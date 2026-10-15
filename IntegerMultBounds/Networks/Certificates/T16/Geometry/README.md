# Exact T16 finite binary geometry

This separate checkpoint gives the selected R480/T16 frame catalog its actual
binary linear-algebra meaning. Each original ordered list of nine-bit masks
is decoded, low bit first, into vectors in `Fin 9 → ZMod 2`. The original 1,004
frame IDs and ordered masks are retained exactly.

`Model.lean` proves that checked dual functionals imply linear independence,
that the span's finite dimension equals the literal basis length, and that
checked XOR combinations imply actual submodule inclusion. The generator supplies
finite dual and XOR witnesses; Lean checks their equations with default proof
limits. No supplier program is executed to establish a proof.

`Catalog.lean` exposes certified frames. `catalogBasis` in `Certificate.lean`
turns each retained ordered vector family into a basis of its actual span and
proves that the basis retains those vectors. The catalog uses frame zero outside
the native ID range; all native IDs are already bounded in the trace certificate.

The 2,888 distinct oriented edge certificates prove actual span inclusion,
actual finite-dimension difference equal to the declared positive rank, and
positivity. The event checks run over the **committed literal trace definitions**,
not a replacement event list. Climbs ascend in both orientations; forward
centers descend and backward centers ascend. Every one of the 24,767 retained
native events per orientation is checked, with scalar and wrapper events imposing
no additional geometric assertion here. Trace label continuity and scalar
incidence remain provided by the separate committed trace certificate.

This does not construct ambient frame operators or interpret adapters, prove the
full dirty scalar routing identity, restore arbitrary private scratch, or provide
physical hosting or tape costs. Independence does not imply restricted
nondegeneracy: selected frame 2 contains the mask 30, a nonzero isotropic direction
for `Labels.binary 9`. Consequently the existing projection interfaces requiring
nondegenerate restrictions cannot be applied to this whole catalog without a
separate, correct operator construction matching the supplier convention.

Regenerate with `python3 scripts/generate_t16_geometry.py SOURCE_DIRECTORY`.
`--output DIRECTORY` supports independent deterministic comparison. Input pins,
counts, conventions and scope are recorded in `geometry-provenance.json`.
Original byte-identical license and notice files are retained beside the committed
trace certificate and referenced by its provenance; this checkpoint extends the
same exact hash-pinned source data.

## Source operator convention and remaining bridge

The supplier Clifford compiler uses `i^p X^x Z^z` Paulis and the coordinate gate
`C = ((1+i)/2) I + ((1-i)/2) X`, matching `BinaryWalsh.kernel 1`.
For the selected ordered frame `U`, its binary basis extension gives `G`,
`Q = I + G⁻ᵀ G⁻¹`, `K = D_Q P_G`, and the canonical frame operator is
`T_U = K C_[dim U] K⁻¹`. Its phase checker identifies the inverse-Z subspace as
`L_U = {(u,u+v) : u ∈ U, v ∈ U⊥}` in the doubled binary symplectic space.
The source width is the rank of the X block of the images of Z generators;
it is not the complex rank of the invertible operator or a projector rank.

The elementary doubled-space formulas are isolated in `Lagrangian.lean`:
the shear image is isotropic and has dimension nine, and for `U ≤ V` the
intersection is the shear image of `U × V⊥`, of dimension
`dim U + (9 - dim V)`. `LagrangianCertificate.lean` binds its dimension deficit
to the exact native climb/center width declarations.
They require no nondegeneracy of the restriction to `U`. Identifying these
subspaces with the actual canonical Clifford recipes, proving the symplectic
B-block rank correspondence, and validating global phases of the serialized
monomial factors remain separate obligations. The source's tableau plus
zero-state equality test needs a Lean soundness/completeness bridge; the finite
binary certificate does not assume that test establishes operator equality.

## Verification

All 182 Lean modules in this directory passed targeted guarded checks with
normal proof limits and no warnings. The 178 generated files reproduced
byte-for-byte in an independent output directory. An independent parser checked
all 1,004 ordered frame/dual lists and 2,888 oriented inclusion/XOR witnesses
against the pinned source data. Corrupt hashes and disabled Python assertions
were rejected before output creation.
The final focused namespace audit passed for 16,310 declarations, allowing only
`propext`, `Quot.sound`, and `Classical.choice`. The finite-only audit covered
16,283 declarations. Peak resumed module RSS was 1,201.9 MiB; the final audit
used 1,137.6 MiB. No ambient operator or tableau assertion is included.
