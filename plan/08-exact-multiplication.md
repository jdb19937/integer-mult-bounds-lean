# 8. Exact integer multiplication and its cost (§8)

Part of the [plan](../PLAN.md). See [COMPONENTS.md](../COMPONENTS.md) for what each file proves.

## How the proof goes

Section 8 (the manuscript's §8) turns the approximate transforms into an exact multiplier and accounts for the total time. Parameters are chosen with enough slack that the accumulated transform error is below one half, so rounding recovers the integer coefficients exactly; the cost table then sums every component's rows to the target bound.

1. Parameters (`Parameters`, `Asymptotics`, `Primes`): parameter slacks and assembly margins, asymptotic estimates and the finite-depth recurrence, and odd pairwise coprime source lengths in the required intervals, which replace the manuscript's short-interval primes.
2. Exact recovery (`Carry`, `MainReduction`, `ExactRecovery`, `ExactRecoveryOutput`): the precision chain from transform errors to the exact product, rounding and carry propagation, and an output of exactly twice the input length even for nondivisible chunk widths.
3. Time bound (`PackedMultiplierPolylogBudget`, `TimeBound`, `Sizes`, `CostTable`): the polylog overhead of the packed multiplier is absorbed by the packed-product margin, and the size relations and every cost-table row assemble into `O(n (lg n)^(1-κ))` with `κ = 83/10^12`, given the components' row costs.

## Sub-problems

### Parameters, asymptotics and coprime source lengths

Fixes parameter margins, proves the asymptotic estimates, and supplies the primes the construction needs.

- Math milestone: `IntegerMultBounds.Sizes.eventually_coprime_lengths` — For all large n and every t_i ∈ {r/2, r} there are odd, pairwise coprime s_i with (1-2η) t_i < s_i ≤ (1-η) t_i, η = 1/(4d). This replaces the short-interval primes of Harvey–van der Hoeven Lemma 5.1, since the assembly only uses that the s_i are odd and pairwise coprime.
- Tape milestone: —

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Parameter slacks and assembly margins | `Parameters` | ✅ | — | Log enclosure proved in Lean |
| Asymptotics and finite-depth recurrence | `Asymptotics` | ✅ | — | |
| Coprime source lengths | `CoprimeLengths`, `SourceLengths` | ✅ | — | Lengths `1 + k·M` with `M = 2·d!` and an offset divisible by `∏_{m<4d}(1 + mM)` are odd and pairwise coprime in every interval once `X ≥ 2^(84 d³)`, which holds eventually because `ℓ ≥ p/(12d)` and `d ≤ p^ε`. No short-interval prime theorem is needed. Bertrand chains remain in `Primes` |

### Exact recovery of the product

Shows rounding and carries recover the exact product with exactly twice-length output.

- Math milestone: `IntegerMultBounds.ExactRecoveryOutput.eventually_outputCorrect_of_sizes` — For all large digit widths k, if the transform pipeline at precision 6k has scaled errors at most 9·2^γ·T·levels with S ≤ T < 2^k, 1 ≤ levels < k and γ ≤ k/4, the rounded, carried output has exactly 2n bits and value x·y, and installing it at tape zero satisfies the EndToEnd output contract. The error margins are derived from these size relations (`margins_of_sizes`), not assumed.
- Tape milestone: `IntegerMultBounds.Machine.RecoverPublicOutput.runs_computed` — A fixed literal program extracts real coefficients from the contiguous public signed transform record, rounds and propagates carries, installs the exactly 2n-bit product word at tape zero, and reclaims all workspace within a cost linear in the original record volume. The actual computed-transform guarantees and numerator readout supply coefficient correctness; unary controls are supplied.

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Exact coefficient arithmetic, rounding, carries | `Carry`, `MainReduction`, `ExactRecovery`, `Machine/RecoverCoefficientRound`, `Machine/RecoverCarryStep`, `Machine/RecoverMagnitude`, `Machine/RecoverCoefficientStep`, `Machine/RecoverPrecisionSplit`, `Machine/RecoverSignedCoefficient`, `Machine/RecoverWorkspace`, `Machine/RecoverIterationFinish`, `Machine/RecoverIteration`, `Machine/RecoverLoad`, `Machine/RecoverArray`, `Machine/RecoverOutputSerialize`, `Machine/RecoverArrayCleanup`, `Machine/RecoverCarryFlush`, `Machine/RecoverOutput`, `Machine/RecoverNumericalBridge`, `Machine/RulerReverseCopy`, `Machine/RecoverRecordFormat`, `Machine/RecoverRecordField`, `Machine/RecoverRecordArray`, `Machine/RecoverRecordReady`, `Machine/RecoverPublicOutput` | ✅ | ✅ | `Machine.RecoverOutput.runs_recover` executes a fixed twelve-tape, 127-state native program from the signed dyadic coefficient array, supplied unary chunk/precision rulers, the original left operand as an output-length clock, and blank work. It loads/rounds/carries all records, publishes chunks with a uniform carry-width invariant, flushes the final carry without extra coefficient records, erases the array/terminal carry/rulers, serializes exactly twice the input length in MSB order, and erases every remaining source/clock tape. The original signed half-unit margins and coefficient packing/product identity give the exact product on the same halted bank; `runs_correct` gives the EndToEnd output contract and every non-output tape entirely blank with head zero. No recovered output, prepared decoded fields, execution callback or final-cleanliness premise is supplied. Cost is at most `160 * (sourceCellVolume + wordWidth + inputLength + 1)`, or `640 * sourceCellVolume` for a nonempty array paying the clock from source volume. No coefficient-count output-capacity assumption is needed. Empty arrays, zero/padded coefficients, negative near-zero approximations, carry overflow, excess high padding and nondivisible chunk widths are covered. `Machine/RecoverNumericalBridge` now derives all coefficient margins from normalized-convolution approximation (or the computed-transform contraction/error guarantees) and derives the coefficient/product identity from the original input digits; its `runs_correct` yields the same actual halted recovery execution. Physical word lengths and the scaled readout equation remain interface premises. `Machine/RecoverRecordArray.runs_public` now physically selects/reverses every real field from the contiguous public signed complex record, skips imaginary fields, and inserts native separators within `(8w+21)` times coordinate count. `RecoverRecordFormat.records_good_public_computed` proves these exact words have the required margins; for power-of-two convolution lengths the final scaling reduces the precision ruler instead of multiplying the numerators. `Machine/RecoverRecordReady` now rewinds the native array and reclaims the consumed public source/width ruler. `Machine/RecoverPublicOutput.runs_computed` composes that adapter with native recovery in one fixed fourteen-tape, 159-state program, proving the same actual halted `outputCorrect` bank and every non-output tape/head blank. Its total cost is at most `200 * (originalPublicRecordLength + wordWidth + inputLength + 1)`. At precision `6k`, positive/fitting recovery rulers are derived from `k ≥ 3`, `ℓ ≤ k` and sufficient public word width; the final numerical error margin is discharged by existing size-bound mathematics. Synthesizing supplied controls and connecting the actual transform procedure’s whole-bank output and numerator readout remain upstream fast-program assembly obligations. |
| Exact-width recovered output | `ExactRecoveryOutput` | ✅ | — | Direct numerical recovery yields exactly twice the input length in bits, including nondivisible chunk widths; leading-padding removal preserves the product. Physical native coefficient recovery and exact-width MSB serialization are proved by `Machine/RecoverOutput`; the original mathematical output installer is also proved below. |
| Install recovered output and reclaim workspace | `Machine/RecoverOutputInstall`, `Schoenhage/RecoveryCleanupGenerated`, `Schoenhage/CertifiedSequence` | ✅ | ✅ | A fixed four-tape machine copies an already recovered separator-terminated MSB word from tape one to blank tape zero without copying its separator, then clears the source and two arbitrary word-format scratch tapes, resetting their heads. `runs_install` gives the exact final bank within `3 * word.length + 2 * clen scratchA.words + 2 * clen scratchB.words + 13` steps, including empty words. `runs_recovered` connects this same execution to `ExactRecoveryOutput.output_spec`, giving the exact multiplication output contract and cost `6n` plus charged scratch cleanup and 13 steps. The cleanup is generated from three existing clear contracts. The standalone installer consumes an already recovered word; `Machine/RecoverOutput` now separately proves the full native rounding/carry/output pipeline. |

### Cost table and time bound

Assembles the cost-table rows, including the packed multiplier overhead, into O(n (lg n)^(1-κ)).

- Math milestone: `IntegerMultBounds.CostTable.fastCost_le_table` — The fast path's total cost, summed from the row costs the components prove, is eventually at most V n * tableRows n plus polynomial setup and bounded overheads (the htotal hypothesis of endToEnd_of_table).
- Tape milestone: `IntegerMultBounds.Assembly.fastProgram_steps_le` — On every n-bit input pair the literal fast program's step count is at most the fast-path cost function bounded by fastCost_le_table.

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| PackedMultiplierPolylogBudget | `PackedMultiplierPolylogBudget` | ✅ | — | At the actual packed product size, every fixed nonnegative power of the clamped log-log overhead is bounded by a fixed multiple of a power of log precision. The existing packed-product margin absorbs it into the exact certified final time exponent; the physical fast subroutine still must provide its execution and bit-cost bound. |
| Complete time bound | `TimeBound`, `Sizes`, `CostTable` | 🟡 | ⬜ | Size relations, every table row as a multiple of `p^(1-margin)`, and the assembly into `O(n (lg n)^(1-κ))` at `κ = 83/10^12` proved; the components must still supply the row costs |

### Chirp (Bluestein) reduction

Reduces arbitrary-length transforms to convolutions, exactly and approximately.

The chirp identity is the manuscript's `lem:chirp-permutation` (§7); the chirp procedures that use it are §8 "Chirp and source-transform procedures".

- Math milestone: `IntegerMultBounds.NLogN.bluesteinD_exact_approx` — The d-dimensional DFT of even lengths equals the chirp-convolution-chirp pipeline exactly, and with approximate chirps (eps_a) and approximate normalized convolution (eps_M) the pipeline has scaled error at most eps_M + 3 eps_a + 4. Combines `NLogN.bluesteinD`, `NLogN.bluesteinApproxD_err`.
- Tape milestone: `IntegerMultBounds.Spec.SignedRingProduct.bluestein_meets` — A fixed literal program multiplies each record by the chirp, calls the synthetic convolution, and multiplies by the conjugate chirp, outputting the arbitrary-length transform within the bluesteinApproxD_err error and the chirps row plus the convolution cost.

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Bluestein reduction | `Bluestein`, `BluesteinApprox` | ✅ | ⬜ | |
