# 6. Synthetic transforms and their tape layout (§6)

Part of the [plan](../PLAN.md). See [COMPONENTS.md](../COMPONENTS.md) for what each file proves.

## How the proof goes

Section 6 supplies the transforms the main recursion applies along each axis: discrete Fourier transforms over the synthetic ring `ℂ[y]/(y^r + 1)`, where multiplication by powers of `y` gives cheap shift twiddles, together with the bookkeeping that places them on tapes within the cost table.

1. Synthetic ring and FFT (`SynthConv`, `SynthFFT`, `SynthMultiD`): principal roots of unity in `ℂ[y]/(y^r + 1)` make a fast transform whose twiddles are shifts, in one and `d` dimensions, with accumulated error `n ε`.
2. Embedding (`SynthEmbed`): a twisted embedding of complex vectors into synthetic ones is an isometry, so complex transforms reduce to synthetic ones without loss of precision.
3. Layout and costs (`LayoutCost`): prefix slots, chunk reordering by address exchanges, the number of rounds and their error growth, and descriptor length are bounded so that one transform bracket matches four cost-table rows.

## Sub-problems

### Synthetic ring and synthetic FFT

Builds the ring with shift twiddles, its multidimensional FFT with error bounds, and the isometric embedding of complex vectors.

- Math milestone: `IntegerMultBounds.NLogN.synth_transform_bounds` — Over C[y]/(y^r+1) with shift twiddles the 1- and d-dimensional synthetic DFTs satisfy the convolution theorem and inversion, the radix-2 FFT with per-level error eps is within n*eps of them in one and d dimensions, and the twisted embedding is an isometry carrying complex convolution to synthetic convolution. Combines `NLogN.synthDFT_conv`, `NLogN.synthDFTInv_synthDFT`, `NLogN.synth_fft_err`, `NLogN.synthDFTD_conv`, `NLogN.synthDFTDInv_synthDFTD`, `NLogN.approxMap_synthDFTDNumC`, `NLogN.norm_twist`, `NLogN.synthConvG_toSynth`.
- Tape milestone: `IntegerMultBounds.Spec.SignedRingProduct.transform_target` — For valid transform parameters P, transformTarget P holds: fixed literal programs run the forward and opposite synthetic transforms on tapes in the paper's formats with per-coefficient error below sqrt2*l*2^(-p) within the transformTarget cost.

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Principal roots and synthetic ring | `SynthConv` | ✅ | — | `ℂ[y]/(yʳ + 1)` |
| Synthetic FFT with shift twiddles | `SynthFFT`, `SynthMultiD` | ✅ | ⬜ | One and `d` dimensions, error `n ε` |
| Complex-to-synthetic embedding | `SynthEmbed` | ✅ | — | Twist is an isometry |
| Stored-order forward and opposite schedules (`eq:stored-opposite`) | `Schoenhage/Dif`, `Schoenhage/DifAxes`, `Schoenhage/DifGroup`, `Schoenhage/DifRound`, `Schoenhage/DifSchedule`, `Schoenhage/DifLayout`, `Schoenhage/PaperLayout`, `Schoenhage/DifOpposite` | ✅ | ⬜ | On any bit layout the slot-major forward rounds compute `L B F⁻` (`fwdSchedule_fwdExact`) and the reversed opposite rounds (inverse monomial, then butterfly) compute `F⁺ B⁻¹ L⁻¹` in the same layout (`oppSchedule_eq`), via `H₀² = I/2`; tape execution open |
### Tape layout and cost bracket

Bounds slots, reordering exchanges, rounds, error and descriptors so a transform costs four cost-table rows.

- Math milestone: `IntegerMultBounds.LayoutCost.transform_layout_bracket` — Eventually: prefix slots are at most dK, chunk reordering needs at most Dq-1 exchanges costing at most d l K^(tau-1), there are exactly l rounds with error l*sqrt2*2^(-p) staying in the disk, descriptors have length at most C_desc p, K < l, and the resulting bracket equals the sum of the four cost-table rows. Combines `LayoutCost.prefix_slots_le`, `LayoutCost.chunk_exchanges_le`, `LayoutCost.exchange_cost_le`, `LayoutCost.rounds_eq`, `LayoutCost.compIter_error`, `LayoutCost.compIter_disk`, `LayoutCost.descriptor_length_le`, `LayoutCost.eventually_K_lt_ℓ`, `LayoutCost.bracket_eq_rows`.
- Tape milestone: `IntegerMultBounds.LayoutCost.transform_runs_le_bracket` — The literal forward and opposite transform programs, with the prefix-slot layout and chunk reordering by address exchanges, halt within T p times the bracket, hence within the four cost-table rows.

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Tape layout and costs | `LayoutCost` | ✅ | ⬜ | Prefix slots `≤ dK`, chunk reorder by `≤ Dq−1` exchanges costing `≤ dℓK^(τ−1)`, exactly `ℓ` rounds with error `ℓ√2·2^(-p)` in the disk, descriptor length `≤ C_desc p`, bracket equals four cost-table rows; `K < ℓ` eventually |
