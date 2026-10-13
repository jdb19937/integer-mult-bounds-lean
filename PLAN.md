# Plan and progress

A detailed breakdown of the [README](README.md) status table. Each section
matches one README row and splits it into subcomponents. *Mathematics* means
the statements the algorithm relies on are proved in Lean. *Tape* means a
program in the literal machine model is proved correct with a runtime bound.
See [COMPONENTS.md](COMPONENTS.md) for what each file proves.

✅ done · 🟡 partial · ⬜ not started · 🚧 drafted, not yet in the build.

## Overview

| Part of the proof | Source | Mathematics | Tape | Files |
| --- | --- | --- | --- | --- |
| [The machine model and elementary streams](plan/02-machine-model-streams.md) | §2 | ✅ 9/9 | ✅ 9/9 | 257 |
| [Two finite networks with a rank saving](plan/03-finite-networks-rank.md) | §3 | ✅ 8/8 | 🟡 2/6 | 358 |
| [Faster interchange of address chunks](plan/04-faster-interchange-address.md) | §4 | ✅ 10/10 | ✅ 9/9 | 375 |
| [Fast simultaneous synthetic butterfly layers](plan/05-simultaneous-butterfly-layers.md) | §5, §11, CrocSwap | 🟡 6/12 | 🟡 0/12 | 1741 |
| [Synthetic transforms and their tape layout](plan/06-synthetic-transforms-tape.md) | §6 | ✅ 2/2 | 🟡 0/2 | 71 |
| [Resampling with the permutations left in the transform](plan/07-gaussian-resampling.md) | §7 | ✅ 6/6 | 🟡 3/4 | 79 |
| [Exact integer multiplication and its cost](plan/08-exact-multiplication.md) | §8 | 🟡 3/4 | ⬜ 0/3 | 15 |
| [Fast multiplication subroutine](plan/A-schoenhage-strassen.md) | Schönhage–Strassen | ✅ 6/6 | 🟡 3/4 | 94 |
| [End-to-end theorem `EndToEnd`](plan/B-end-to-end.md) | — | 🟡 1/3 | 🟡 2/3 | 6 |

Every sub-problem has a math milestone and a tape milestone: one named Lean
theorem stating that part is done, listed in its section's detail file under
`plan/`. A milestone is ✅ once that theorem is declared in the library, which
the axiom audit keeps sorry-free. An open milestone shows 🟡, with its
finished-row count when some rows are still open. The overview counts proved
milestones per section; Files counts the Lean files, existing or planned,
behind each part. Each detail file also outlines the section's proof and keeps
the full per-row status. Add new rows to the detail file under the matching
sub-problem, then run `python3 scripts/plan-status.py` to refresh the tables
here.


## 2. The machine model and elementary streams (§2)

Details: [plan/02-machine-model-streams.md](plan/02-machine-model-streams.md)

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
| Tape radix sort | ✅ | ✅ | 16 |

## 3. Two finite networks with a rank saving (§3)

Details: [plan/03-finite-networks-rank.md](plan/03-finite-networks-rank.md)

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

Details: [plan/04-faster-interchange-address.md](plan/04-faster-interchange-address.md)

| Sub-problem | Mathematics | Tape | Files |
| --- | --- | --- | --- |
| Interchange recurrence and padding arithmetic | ✅ | — | 1 |
| Triangular factorization and shear (Lemmas 4.1-4.2) | ✅ | ✅ | 4 |
| Tape primitives: role transport, stacks, descriptors | ✅ | ✅ | 37 |
| Single-digit base case | ✅ | ✅ | 11 |
| Recursive node operations | ✅ | ✅ | 59 |
| Recursive call protocol and child headers | ✅ | ✅ | 34 |
| Power-width recursive machine (Prop 4.3) | ✅ | ✅ | 60 |
| Row/range padding and radix digit movement | ✅ | ✅ | 34 |
| Arbitrary-width piece dispatcher (Lemma 4.4) | ✅ | ✅ | 120 |
| Binary interchange wrapper | ✅ | ✅ | 16 |

## 5. Fast simultaneous synthetic butterfly layers (§5, §11, CrocSwap)

Details: [plan/05-simultaneous-butterfly-layers.md](plan/05-simultaneous-butterfly-layers.md)

| Sub-problem | Mathematics | Tape | Files |
| --- | --- | --- | --- |
| Packed arithmetic and fixed control gadgets | 🟡 | 🟡 | 191 |
| Active-target compact controls | ✅ | 🟡 193/194 rows | 274 |
| Exceptional-address destination repair | ✅ | 🟡 | 256 |
| Row padding, reservation and allowances | 🟡 | 🟡 56/57 rows | 72 |
| Binary basis stages and phase schedules | ✅ | 🟡 | 104 |
| Butterfly and unit-phase record arithmetic | 🟡 | 🟡 | 207 |
| Butterfly axes, spectators and native roles | 🟡 | 🟡 | 140 |
| Recursive geometry, controller and child headers | ✅ | 🟡 | 45 |
| Exact scalar grids and stopped calls | ✅ | 🟡 | 96 |
| Nonleaf calls and the fixed node table | 🟡 | 🟡 | 48 |
| Source-ready table, orientation and endpoints | ✅ | 🟡 | 168 |
| Full recursive execution and runtime | 🟡 | 🟡 70/71 rows | 142 |

## 6. Synthetic transforms and their tape layout (§6)

Details: [plan/06-synthetic-transforms-tape.md](plan/06-synthetic-transforms-tape.md)

| Sub-problem | Mathematics | Tape | Files |
| --- | --- | --- | --- |
| Synthetic ring and synthetic FFT | ✅ | 🟡 5/10 rows | 38 |
| Tape layout and cost bracket | ✅ | 🟡 12/17 rows | 34 |

## 7. Resampling with the permutations left in the transform (§7)

Details: [plan/07-gaussian-resampling.md](plan/07-gaussian-resampling.md)

| Sub-problem | Mathematics | Tape | Files |
| --- | --- | --- | --- |
| Exact Gaussian resampling factorization | ✅ | — | 8 |
| Numerical resampling maps and error bounds | ✅ | — | 11 |
| Fixed-point word and record layer | ✅ | ✅ | 12 |
| Gaussian weight tables on tapes | ✅ | ✅ | 12 |
| Resampling maps on tapes | ✅ | ✅ | 13 |
| Tensor interface line costs | ✅ | 🟡 0/2 rows | 23 |

## 8. Exact integer multiplication and its cost (§8)

Details: [plan/08-exact-multiplication.md](plan/08-exact-multiplication.md)

| Sub-problem | Mathematics | Tape | Files |
| --- | --- | --- | --- |
| Parameters, asymptotics and coprime source lengths | ✅ | — | 4 |
| Exact recovery of the product | ✅ | ⬜ | 5 |
| Cost table and time bound | 🟡 1/2 rows | ⬜ | 4 |
| Chirp (Bluestein) reduction | ✅ | ⬜ | 2 |

## A. Fast multiplication subroutine (Schönhage–Strassen)

Details: [plan/A-schoenhage-strassen.md](plan/A-schoenhage-strassen.md)

| Sub-problem | Mathematics | Tape | Files |
| --- | --- | --- | --- |
| Fourier and fixed-point foundations | ✅ | — | 23 |
| Schönhage–Strassen level, schedule and cost | ✅ | — | 4 |
| Word-tape programming layer | ✅ | ✅ | 10 |
| Schönhage–Strassen multiplier on tapes | ✅ | ✅ | 15 |
| Packed signed ring products | ✅ | ✅ | 28 |
| Paper-format transform layer statements | ✅ | 🟡 2/5 rows | 14 |

## B. End-to-end theorem `EndToEnd`

Details: [plan/B-end-to-end.md](plan/B-end-to-end.md)

| Sub-problem | Mathematics | Tape | Files |
| --- | --- | --- | --- |
| Literal input front end | ✅ | ✅ | 1 |
| Quadratic fallback multiplier | 🟡 | ✅ | 4 |
| Fast program assembly and final bound | 🟡 0/3 rows | 🟡 0/3 rows | 2 |
## Next steps

- Assemble synthesized piece descriptors with repeated scaling, repeat inverse scaling, then compose signed rational scales and computed varying-offset translations.

- Compute repair keys and run extraction, sorting and reinsertion on tapes, with the `RepairPipeline` composition as the specification.
- Compile the proved optimized h=50 modular physical network and its fixed rational control schedule to literal tape execution and prove its recursive time bound.
- Account for complex endpoint corrections in the tape implementation.
- Finish the `NegacyclicKronecker` subroutine component.
- Compose the proved rational digit arithmetic into matrix routines and compile the finite network address permutations to literal tape steps.
