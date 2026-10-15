# Archived native-machine roadmap

Historical snapshot from `bbb14231`, archived on 2026-10-15. These tables
track the original native-machine route and its stronger specified exponent,
not unfinished obligations of the completed Mathlib theorem. They are no longer
regenerated or used as the active work queue. See [the current plan](../../PLAN.md).

**Multiplication below `n log n` is proved:**
`IntegerMultBounds.MathlibTM2.statement` supplies an unconditional fixed finite
Mathlib machine and worst-case bound with positive saving
`296 / (10^11 * 2^131)`. [Part C](../C-mathlib-end-to-end.md) records this
completed route. Parts 2–B retain the original native-machine interfaces and
the stronger `83/10^12` compact-control target; their open entries do not
invalidate the completed Mathlib theorem.

[Retention audit](../../docs/proof-retention.md): the completed route is primary;
651 retired native-controller modules and wrappers have been removed; 864 conservative
candidates remain. The completed proof, its public interfaces and every
focused audit dependency are preserved. See the [controller retirement](../../docs/retired-compact-complex.md) and
[actual-stage retirement](../../docs/retired-compact-actual.md) records.

✅ done · 🟡 partial · ⬜ not started · 🚧 drafted, not yet in the build.

## Overview

| Part of the proof | Source | Mathematics | Tape | Files |
| --- | --- | --- | --- | --- |
| [The machine model and elementary streams](02-machine-model-streams.md) | §2 | ✅ 9/9 | ✅ 9/9 | 258 |
| [Two finite networks with a rank saving](03-finite-networks-rank.md) | §3 | ✅ 8/8 | 🟡 2/6 | 358 |
| [Faster interchange of address chunks](04-faster-interchange-address.md) | §4 | ✅ 10/10 | ✅ 9/9 | 376 |
| [Fast simultaneous synthetic butterfly layers](05-simultaneous-butterfly-layers.md) | §5, §11, CrocSwap | 🟡 3/5 | 🟡 0/7 | 1167 |
| [Synthetic transforms and their tape layout](06-synthetic-transforms-tape.md) | §6 | ✅ 2/2 | 🟡 0/2 | 79 |
| [Resampling with the permutations left in the transform](07-gaussian-resampling.md) | §7 | ✅ 6/6 | 🟡 3/4 | 79 |
| [Exact integer multiplication and its cost](08-exact-multiplication.md) | §8 | 🟡 3/4 | 🟡 1/3 | 108 |
| [Fast multiplication subroutine](A-schoenhage-strassen.md) | Schönhage–Strassen | ✅ 6/6 | 🟡 3/4 | 96 |
| [End-to-end theorem `EndToEnd`](B-end-to-end.md) | — | 🟡 2/3 | 🟡 2/3 | 6 |

These tables record the native route's status at the archival revision.
A green milestone had a named theorem in the library; yellow marked an
unfinished native interface. Files counts included existing and planned
components. These historical counts are frozen and must not be interpreted
as current proof obligations or refreshed with the active status generator.


## 2. The machine model and elementary streams (§2)

Details: [02-machine-model-streams.md](02-machine-model-streams.md)

| Sub-problem | Mathematics | Tape | Files |
| --- | --- | --- | --- |
| Machine model and target statement | ✅ | ✅ | 1 |
| Axiom audit | — | — | 1 |
| Machine combinators and frames | ✅ | ✅ | 14 |
| Counters and counted loops | ✅ | ✅ | 28 |
| Binary and radix arithmetic machines | ✅ | ✅ | 51 |
| Rational scaling of one coordinate | ✅ | ✅ | 46 |
| Controlled shift of one coordinate | ✅ | ✅ | 36 |
| Common coordinates and schedule assembly | ✅ | ✅ | 56 |
| Packed-line and window gadgets | ✅ | ✅ | 9 |
| Tape radix sort | ✅ | ✅ | 17 |

## 3. Two finite networks with a rank saving (§3)

Details: [03-finite-networks-rank.md](03-finite-networks-rank.md)

| Sub-problem | Mathematics | Tape | Files |
| --- | --- | --- | --- |
| Scalar shear and bank exchange circuits | ✅ | ⬜ | 8 |
| Wire counts and bilinear label spaces | ✅ | — | 9 |
| Grouped gates and binary residual units | ✅ | ⬜ | 15 |
| Projection-rank trace and h=25 saving | ✅ | ⬜ | 15 |
| Shared-point h=50 network and compilation | ✅ | ✅ | 251 |
| Optimized global rank trace | ✅ | — | 22 |
| Optimized physical program and interchange | ✅ | ✅ | 22 |
| Tape realization of the network | ✅ | 🟡 1/3 rows | 18 |

## 4. Faster interchange of address chunks (§4)

Details: [04-faster-interchange-address.md](04-faster-interchange-address.md)

| Sub-problem | Mathematics | Tape | Files |
| --- | --- | --- | --- |
| Interchange recurrence and padding arithmetic | ✅ | — | 2 |
| Triangular factorization and shear (Lemmas 4.1-4.2) | ✅ | ✅ | 4 |
| Tape primitives: role transport, stacks, descriptors | ✅ | ✅ | 37 |
| Single-digit base case | ✅ | ✅ | 11 |
| Recursive node operations | ✅ | ✅ | 59 |
| Recursive call protocol and child headers | ✅ | ✅ | 34 |
| Power-width recursive machine (Prop 4.3) | ✅ | ✅ | 60 |
| Row/range padding and radix digit movement | ✅ | ✅ | 34 |
| Arbitrary-width piece dispatcher (Lemma 4.4) | ✅ | ✅ | 120 |
| Binary interchange wrapper | ✅ | ✅ | 17 |

## 5. Fast simultaneous synthetic butterfly layers (§5, §11, CrocSwap)

Details: [05-simultaneous-butterfly-layers.md](05-simultaneous-butterfly-layers.md)

| Sub-problem | Mathematics | Tape | Files |
| --- | --- | --- | --- |
| Packed arithmetic and fixed control gadgets | 🟡 | 🟡 | 192 |
| Active-target compact controls | ✅ | 🟡 193/194 rows | 274 |
| Exceptional-address destination repair | ✅ | 🟡 | 256 |
| Row padding, reservation and allowances | — | 🟡 56/57 rows | 69 |
| Binary basis stages and phase schedules | 🟡 | 🟡 | 83 |
| Butterfly and unit-phase record arithmetic | — | 🟡 | 133 |
| Butterfly axes, spectators and native roles | — | 🟡 | 78 |
| Recursive geometry, controller and child headers | — | — | 5 |
| Exact scalar grids and stopped calls | — | — | 22 |
| Nonleaf calls and the fixed node table | — | — | 2 |
| Source-ready table, orientation and endpoints | ✅ | — | 17 |
| Full recursive execution and runtime | — | — | 37 |

## 6. Synthetic transforms and their tape layout (§6)

Details: [06-synthetic-transforms-tape.md](06-synthetic-transforms-tape.md)

| Sub-problem | Mathematics | Tape | Files |
| --- | --- | --- | --- |
| Synthetic ring and synthetic FFT | ✅ | 🟡 6/12 rows | 46 |
| Tape layout and cost bracket | ✅ | 🟡 12/17 rows | 34 |

## 7. Resampling with the permutations left in the transform (§7)

Details: [07-gaussian-resampling.md](07-gaussian-resampling.md)

| Sub-problem | Mathematics | Tape | Files |
| --- | --- | --- | --- |
| Exact Gaussian resampling factorization | ✅ | — | 8 |
| Numerical resampling maps and error bounds | ✅ | — | 11 |
| Fixed-point word and record layer | ✅ | ✅ | 12 |
| Gaussian weight tables on tapes | ✅ | ✅ | 12 |
| Resampling maps on tapes | ✅ | ✅ | 13 |
| Tensor interface line costs | ✅ | 🟡 0/2 rows | 23 |

## 8. Exact integer multiplication and its cost (§8)

Details: [08-exact-multiplication.md](08-exact-multiplication.md)

| Sub-problem | Mathematics | Tape | Files |
| --- | --- | --- | --- |
| Parameters, asymptotics and coprime source lengths | ✅ | — | 5 |
| Exact recovery of the product | ✅ | ✅ | 58 |
| Cost table and time bound | 🟡 1/2 rows | ⬜ | 5 |
| Chirp (Bluestein) reduction | ✅ | 🟡 0/1 rows | 40 |

## A. Fast multiplication subroutine (Schönhage–Strassen)

Details: [A-schoenhage-strassen.md](A-schoenhage-strassen.md)

| Sub-problem | Mathematics | Tape | Files |
| --- | --- | --- | --- |
| Fourier and fixed-point foundations | ✅ | — | 25 |
| Schönhage–Strassen level, schedule and cost | ✅ | — | 4 |
| Word-tape programming layer | ✅ | ✅ | 10 |
| Schönhage–Strassen multiplier on tapes | ✅ | ✅ | 15 |
| Packed signed ring products | ✅ | ✅ | 28 |
| Paper-format transform layer statements | ✅ | 🟡 2/5 rows | 14 |

## B. End-to-end theorem `EndToEnd`

Details: [B-end-to-end.md](B-end-to-end.md)

| Sub-problem | Mathematics | Tape | Files |
| --- | --- | --- | --- |
| Literal input front end | ✅ | ✅ | 1 |
| Quadratic fallback multiplier | ✅ | ✅ | 4 |
| Fast program assembly and final bound | 🟡 0/3 rows | 🟡 0/3 rows | 2 |
## Remaining work for the stronger compact-control target

The sub-n-log-n existence result is complete through part C. The items below
belong to the original route and its stronger specified exponent.

- Assemble synthesized piece descriptors with repeated scaling, repeat inverse scaling, then compose signed rational scales and computed varying-offset translations.

- Compute repair keys and run extraction, sorting and reinsertion on tapes, with the `RepairPipeline` composition as the specification.
- Compile the proved optimized h=50 modular physical network and its fixed rational control schedule to literal tape execution and prove its recursive time bound.
- Account for complex endpoint corrections in the tape implementation.
- Finish the `NegacyclicKronecker` subroutine component.
- Compose the proved rational digit arithmetic into matrix routines and compile the finite network address permutations to literal tape steps.
