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

- Math milestone: `IntegerMultBounds.ExactRecoveryOutput.eventually_outputCorrect_of_sizes` — For all large k, under the size relations, the rounded, carried output computed from the approximate pipeline has exactly 2n bits and value x*y, so installing it at tape zero satisfies outputCorrect. Combines `ExactRecoveryOutput.outputCorrect_of_computed`, `ExactRecoveryOutput.computed_output_spec`, `ExactRecovery.margins_of_sizes`, `ExactRecovery.eventually_threshold`.
- Tape milestone: `IntegerMultBounds.Machine.RecoverOutput.runs_recover` — A fixed literal program rounds the computed convolution coefficients, propagates carries, and installs the exactly 2n-bit product word at tape zero within a cost linear in the volume.

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Exact coefficient arithmetic, rounding, carries | `Carry`, `MainReduction`, `ExactRecovery` | ✅ | ⬜ | Carries and packing at the list level; the §8 precision chain from transform errors `E_s` to the exact product, with the margins from the size relations for all large `k` |
| Exact-width recovered output | `ExactRecoveryOutput` | ✅ | — | Direct numerical recovery yields exactly twice the input length in bits, including nondivisible chunk widths; leading-padding removal preserves the product, and the literal machine output contract follows once that word is installed. Physical carry normalization and installation remain open. |

### Cost table and time bound

Assembles the cost-table rows, including the packed multiplier overhead, into O(n (lg n)^(1-κ)).

- Math milestone: `IntegerMultBounds.CostTable.fastCost_le_table` — The fast path's total cost, summed from the row costs the components prove, is eventually at most V n * tableRows n plus polynomial setup and bounded overheads (the htotal hypothesis of endToEnd_of_table).
- Tape milestone: `IntegerMultBounds.Assembly.fastProgram_steps_le` — On every n-bit input pair the literal fast program's step count is at most the fast-path cost function bounded by fastCost_le_table.

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| PackedMultiplierPolylogBudget | `PackedMultiplierPolylogBudget` | ✅ | — | At the actual packed product size, every fixed nonnegative power of the clamped log-log overhead is bounded by a fixed multiple of a power of log precision. The existing packed-product margin absorbs it into the exact certified final time exponent; the physical fast subroutine still must provide its execution and bit-cost bound. |
| Complete time bound | `TimeBound`, `Sizes`, `CostTable` | 🟡 | ⬜ | Size relations, every table row as a multiple of `p^(1-margin)`, and the assembly into `O(n (lg n)^(1-κ))` at `κ = 83/10^12` proved; the components must still supply the row costs |
