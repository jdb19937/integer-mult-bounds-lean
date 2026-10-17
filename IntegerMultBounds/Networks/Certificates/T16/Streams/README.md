# Selected T16 eight-stream data composition

This checkpoint certifies the global data composition of the selected T16
supplier (PR1094) for all 16 replicas and 112 ports, operator-exactly and for
every Fourier character at once.

## Model

For one replica and port, the data families `X_0, Y_0, ..., X_3, Y_3` are eight
streams. Every event of the global template acts on them as a phase (an
operator `M c` for a coefficient vector `c : Fin 73 → ZMod 4`), a ±1 shear, or
the terminal signed exchange `(X, Y) ↦ (Y, -X)`. Coefficients are over the port's
orthonormal basis `B_q ⊕ I`: index 0 is `q`, indices 1..8 the other low basis
vectors, and index `j ≥ 9` the coordinate vector `e_j`. Local sweeps move a pair
between canonical levels `wt(u ∧ [0, 9+8s)) - side·[u·q]`; hosted helper slices
and idle remainder children add their axes; idle children add their stored
translations; the terminal `Y` translation removes `X_q`. Upstream's
`stream_check.py` uses the same event semantics on sampled characters.

`Model.lean` defines stream programs for an arbitrary homomorphism
`M : Multiplicative (Fin 73 → ZMod 4) →* Module.End ℂ S` and a kernel check that
tracks each stream's frame as a packed coefficient vector together with the
integer scalar chain. Shears and exchanges must meet equal frames, so they
commute with the frame operators. `Sound.lean` proves `run_of_accepts`: an
accepted program is `M target` on every stream, for every `M` and every stream
value. `Kernels.lean` gives the T16 interpretation `basisOp B`, the commuting
product of translation kernels `kernel (c k) (B k)`, which is `C_{B k}` at
coefficient one.

## Data and checks

`scripts/generate_t16_streams.py UPSTREAM` reads the pinned selected replay
archive (global template, idle remainder frames, data phases) and the PR1094
owner records, and writes `Template.lean`, `Ports.lean` and `Groups0-15.lean`.
No upstream code runs; input hashes are in `streams-provenance.json`. The
generator checks that each port basis is orthonormal and that every hosted or
idle axis is a basis vector. `Check0-15.lean` run the stream check on all 112
ports of each replica with `decide +kernel`, and `All.lean` combines them into
`all_accepts`. Whatever the generator wrote, these theorems are about the
emitted data; nothing generated is trusted.

The cover class `g` is handled by applying `run_of_accepts` to the conjugated
homomorphism `P_g (M ·) P_g⁻¹`; its identification with the physical node, the
`X_δ(g)` correction, the local-word frames, adapters, wrappers, hosting charts
and the route lift are separate obligations.
