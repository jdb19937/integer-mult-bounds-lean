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
| Grouped rounds as layer calls, and their rounding error | `Schoenhage/DifHadamard` | ✅ | ⬜ | The layer operator `hadamard D K ρ (2^s)` is the butterfly on physical bits `s + jK + ρ` (`hadamard_eq_bflys`); grid rounding commutes with the exact twist (`roundArr_twist`, `roundArr_slotRound`); rounding every grouped slot round keeps the computed forward schedule within `√2 H 2^(-p)` of `L B F⁻ z` per coefficient and in the unit disk (`compSchedule_close`); the opposite computed schedule and the tape execution are open |
| Grouped opposite rounds and their rounding error | `Schoenhage/DifOppositeRounds` | ✅ | ⬜ | The opposite round of a slot (inverse monomial of the summed exponent, then the slot butterflies) equals its per-axis opposite rounds (`axisOppRounds_eq`); the opposite schedule runs these from the bottom slot up (`oppSchedule_oppSlotRounds`); rounding after every slot round stays within `√2 H 2^(-p)` of `F⁺ B⁻¹ L⁻¹` and in the disk (`compOppSchedule_close`) |
| Width of the prefix-slot rounds | `Schoenhage/PrefixRounds` | ✅ | ⬜ | Evaluated exactly, a forward or opposite slot round of a disk array on the `2^(-p)` grid stays in the disk on the `2^(-(p+s))` grid, `s ≤ D` (`slotRound_width`, `oppSlotRound_width`), so `p + D + O(1)` bits per component suffice before the single rounding; the error bounds already round after every slot round of either kind |
| Chunk-group round on tapes | `Schoenhage/TransformRounds` (planned) | — | ⬜ | Tape task 4: given a program meeting `MeetsLayer` for the call, the layer call followed by `TwistArray` returns the rounded `paper_slotRound_chunk` output within layer cost plus `O(Mrw)` (`chunkRound_hoare`) |
| Prefix-slot round on tapes | `Schoenhage/TransformRounds` (planned) | — | ⬜ | Tape task 5: exact half-sums and half-differences at width `p+D+O(1)`, one truncation, then the twist (`prefixRound_hoare`) |
| Forward and opposite drivers | `Schoenhage/TransformDriver` (planned) | — | ⬜ | Tape task 6: layout moves, then the rounds slot by slot (forward), or the opposite rounds then the inverse moves, meet `MeetsForward`/`MeetsOpposite` given `layerTarget` (`forward_meets`, `opposite_meets`) |
| Conditional transform target | `Schoenhage/TransformDriver` (planned) | — | ⬜ | Tape task 7: `layerTarget LP → transformTarget P` for the compatible constants `C_M = Cℓ + 1`, `C_desc = 32(Cℓ + Cw + 1)` (`transform_target_of_layer`); unconditional once §5 proves `layerTarget` |

### Tape layout and cost bracket

Bounds slots, reordering exchanges, rounds, error and descriptors so a transform costs four cost-table rows.

- Math milestone: `IntegerMultBounds.LayoutCost.transform_layout_bracket` — Eventually: prefix slots are at most dK, chunk reordering needs at most Dq-1 exchanges costing at most d l K^(tau-1), there are exactly l rounds with error l*sqrt2*2^(-p) staying in the disk, descriptors have length at most C_desc p, K < l, and the resulting bracket equals the sum of the four cost-table rows. Combines `LayoutCost.prefix_slots_le`, `LayoutCost.chunk_exchanges_le`, `LayoutCost.exchange_cost_le`, `LayoutCost.rounds_eq`, `LayoutCost.compIter_error`, `LayoutCost.compIter_disk`, `LayoutCost.descriptor_length_le`, `LayoutCost.eventually_K_lt_ℓ`, `LayoutCost.bracket_eq_rows`.
- Tape milestone: `IntegerMultBounds.LayoutCost.transform_runs_le_bracket` — The literal forward and opposite transform programs, with the prefix-slot layout and chunk reordering by address exchanges, halt within T p times the bracket, hence within the four cost-table rows.

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Tape layout and costs | `LayoutCost` | ✅ | ⬜ | Prefix slots `≤ dK`, chunk reorder by `≤ Dq−1` exchanges costing `≤ dℓK^(τ−1)`, exactly `ℓ` rounds with error `ℓ√2·2^(-p)` in the disk, descriptor length `≤ C_desc p`, bracket equals four cost-table rows; `K < ℓ` eventually |
| Chunk-group rounds as layer calls in the paper layout | `Schoenhage/PaperRounds` | ✅ | ⬜ | Slot `b + cK + ρ` of axis `i` sits at physical bit `cDK + (D-1-i)K + ρ` (`paperPerm_σ_chunk`); its round is the layer operator `ℋ` on `[P] × [2^K]^D × [2^(cDK)]` with offset `ρ`, then one twist (`paper_slotRound_chunk`); the other slots are the prefix slots `h < b` and `ℓ - 1` (`slot_cases`) |
| Record-level chunk exchange | `Schoenhage/ChunkSwapRecords` | — | ✅ | Tape task 1: the interchange payload effect `SwapPrim.swapList` with suffix `B·2rw` on a record array is the record list with two address fields exchanged, re-flattened (`swapList_array`, via `swapList_flatMap` for any equal-length blocks), so one `SwapPrim.prim` call moves whole records |
| Layout moves realize `L` | `Schoenhage/LayoutMoves`, `Schoenhage/LayoutMovesTape` (planned) | ✅ | ⬜ | Tape task 2. As reorderings of slot names the paper's moves reach its layout: moving the `Lg + bD` prefix slots in turn leaves the chunks axis by axis (`movePrefix_paper`), the left-to-right scan reaches chunk-major order with at most `Dq − 1` exchanges (`chunkExchanges_paper`), and the result is the paper's physical order (`paper_order`, combined in `layout_moves_eq`). Open: running the moves on the record array (digit moves with radix 2 for the prefix, `SwapPrim` for exchanges) and identifying the result with `(paperPerm hL).toPerm`, within `O(Tp(dK + pK^(τ−1)))` |
| Layout moves on the record array | `Schoenhage/LayoutArray` | ✅ | ⬜ | Tape task 2, array semantics: an array stored with its physical address bits holding the logical bits `ps` (`stored`) is moved by a single-bit move (`moveOp`, the record-level `RadixDigitMoveBlockRows.unmove` with `Q = 2`) or a chunk exchange (`swapOp`, the record-level `swapRecs`) into the same array stored in the reordered order (`moveOp_stored`, `swapOp_stored`); the moves of `movePrefix` and the exchanges of `applySwaps` act accordingly (`runMoves_prefix`, `runSwaps_apply`); on the array in natural order the paper's moves give `fun y => z ((paperPerm hL).logi y)` (`layoutOps_paper`), and the reversed inverse moves undo them (`layoutOps_undo`). The machines' payload maps are these moves: the radix-2 digit move's `unmove` (`unmove_eq_onTop`) and the interchange's `swapList` (`swapList_eq_onTop`) act above a suffix, and on flattened records with the suffix times the record length (`onTop_flatten`). Open: composing the machine runs with their per-move descriptors and the cost bound |
| Round headers and twist descriptors | `Schoenhage/RoundDescriptors` (planned) | — | ⬜ | Tape task 3: from the transform header, write each round's layer header `Γ(p)Γ(d)Γ(r)Γ(D)Γ(P)Γ(S)Γ(K)Γ(ρ+1)Γ(w)` and the per-record twist descriptors of `slotExp`, within `O(Tp)` per round (`runs_roundDescriptors`) |
