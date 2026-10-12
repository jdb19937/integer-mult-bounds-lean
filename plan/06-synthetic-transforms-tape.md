# 6. Synthetic transforms and their tape layout (§6)

Part of the [plan](../PLAN.md). See [COMPONENTS.md](../COMPONENTS.md) for what each file proves.

## How the proof goes

Section 6 supplies the transforms the main recursion applies along each axis: discrete Fourier transforms over the synthetic ring `ℂ[y]/(y^r + 1)`, where multiplication by powers of `y` gives cheap shift twiddles, together with the bookkeeping that places them on tapes within the cost table.

1. Synthetic ring and FFT (`SynthConv`, `SynthFFT`, `SynthMultiD`): principal roots of unity in `ℂ[y]/(y^r + 1)` make a fast transform whose twiddles are shifts, in one and `d` dimensions, with accumulated error `n ε`.
2. Embedding (`SynthEmbed`): a twisted embedding of complex vectors into synthetic ones is an isometry, so complex transforms reduce to synthetic ones without loss of precision.
3. Bluestein reduction (`Bluestein`, `BluesteinApprox`): transforms of arbitrary length become convolutions, exactly and with controlled numerical error.
4. Layout and costs (`LayoutCost`): prefix slots, chunk reordering by address exchanges, the number of rounds and their error growth, and descriptor length are bounded so that one transform bracket matches four cost-table rows.

## Sub-problems

### Synthetic ring and synthetic FFT

Builds the ring with shift twiddles, its multidimensional FFT with error bounds, and the isometric embedding of complex vectors.

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Principal roots and synthetic ring | `SynthConv` | ✅ | — | `ℂ[y]/(yʳ + 1)` |
| Synthetic FFT with shift twiddles | `SynthFFT`, `SynthMultiD` | ✅ | ⬜ | One and `d` dimensions, error `n ε` |
| Complex-to-synthetic embedding | `SynthEmbed` | ✅ | — | Twist is an isometry |

### Bluestein reduction

Reduces arbitrary-length transforms to convolutions, exactly and approximately.

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Bluestein reduction | `Bluestein`, `BluesteinApprox` | ✅ | ⬜ | |

### Tape layout and cost bracket

Bounds slots, reordering exchanges, rounds, error and descriptors so a transform costs four cost-table rows.

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Tape layout and costs | `LayoutCost` | ✅ | ⬜ | Prefix slots `≤ dK`, chunk reorder by `≤ Dq−1` exchanges costing `≤ dℓK^(τ−1)`, exactly `ℓ` rounds with error `ℓ√2·2^(-p)` in the disk, descriptor length `≤ C_desc p`, bracket equals four cost-table rows; `K < ℓ` eventually |
