# 9. Exact multiplication, parameters, time bound (§8)

Part of the [plan](../PLAN.md). See [COMPONENTS.md](../COMPONENTS.md) for what each file proves.

## How the proof goes

Section 9 (the manuscript's §8) turns the approximate transforms into an exact multiplier and accounts for the total time. Parameters are chosen with enough slack that the accumulated transform error is below one half, so rounding recovers the integer coefficients exactly; the cost table then sums every component's rows to the target bound.

1. Parameters (`Parameters`, `Asymptotics`, `Primes`): parameter slacks and assembly margins, asymptotic estimates and the finite-depth recurrence, and the existence of suitable primes (short-interval primes still open).
2. Exact recovery (`Carry`, `MainReduction`, `ExactRecovery`, `ExactRecoveryOutput`): the precision chain from transform errors to the exact product, rounding and carry propagation, and an output of exactly twice the input length even for nondivisible chunk widths.
3. Time bound (`PackedMultiplierPolylogBudget`, `TimeBound`, `Sizes`, `CostTable`): the polylog overhead of the packed multiplier is absorbed by the packed-product margin, and the size relations and every cost-table row assemble into `O(n (lg n)^(1-κ))` with `κ = 83/10^12`, given the components' row costs.

## Sub-problems

### Parameters, asymptotics and prime existence

Fixes parameter margins, proves the asymptotic estimates, and supplies the primes the construction needs.

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Parameter slacks and assembly margins | `Parameters` | ✅ | — | Log enclosure proved in Lean |
| Asymptotics and finite-depth recurrence | `Asymptotics` | ✅ | — | |
| Prime existence | `Primes` | 🟡 | — | Short-interval primes open |

### Exact recovery of the product

Shows rounding and carries recover the exact product with exactly twice-length output.

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Exact coefficient arithmetic, rounding, carries | `Carry`, `MainReduction`, `ExactRecovery` | ✅ | ⬜ | Carries and packing at the list level; the §8 precision chain from transform errors `E_s` to the exact product, with the margins from the size relations for all large `k` |
| Exact-width recovered output | `ExactRecoveryOutput` | ✅ | — | Direct numerical recovery yields exactly twice the input length in bits, including nondivisible chunk widths; leading-padding removal preserves the product, and the literal machine output contract follows once that word is installed. Physical carry normalization and installation remain open. |

### Cost table and time bound

Assembles the cost-table rows, including the packed multiplier overhead, into O(n (lg n)^(1-κ)).

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| PackedMultiplierPolylogBudget | `PackedMultiplierPolylogBudget` | ✅ | — | At the actual packed product size, every fixed nonnegative power of the clamped log-log overhead is bounded by a fixed multiple of a power of log precision. The existing packed-product margin absorbs it into the exact certified final time exponent; the physical fast subroutine still must provide its execution and bit-cost bound. |
| Complete time bound | `TimeBound`, `Sizes`, `CostTable` | 🟡 | ⬜ | Size relations, every table row as a multiple of `p^(1-margin)`, and the assembly into `O(n (lg n)^(1-κ))` at `κ = 83/10^12` proved; the components must still supply the row costs |
