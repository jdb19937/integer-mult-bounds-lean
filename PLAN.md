# Plan and progress

A detailed breakdown of the [README](README.md) status table. Each section
matches one README row and splits it into subcomponents. *Mathematics* means
the statements the algorithm relies on are proved in Lean. *Tape* means a
program in the literal machine model is proved correct with a runtime bound.
See [COMPONENTS.md](COMPONENTS.md) for what each file proves.

✅ done · 🟡 partial · ⬜ not started · 🚧 drafted, not yet in the build.

Mathematics and Tape count finished rows of the detail tables out of all rows
that apply (— rows excluded). Files counts the Lean files, existing or planned,
behind each part. Each section has a detail file under `plan/` with an outline
of its proof and the full per-row status. Add new rows to the detail file under
the matching sub-problem, then run `python3 scripts/plan-status.py` to refresh
the tables here.

## Overview

| Part of the proof | Source | Mathematics | Tape | Files |
| --- | --- | --- | --- | --- |
| [Machine model and target statement](plan/01-machine-model-target.md) | §2 | ✅ 3/3 | ✅ 2/2 | 2 |
| [Composition, loops, frames, elementary streams](plan/02-composition-loops-frames.md) | §2 | 🟡 153/154 | 🟡 136/147 | 254 |
| [Finite networks with a rank saving](plan/03-finite-networks-rank.md) | §3 | ✅ 66/66 | 🟡 1/42 | 358 |
| [Faster interchange of address chunks](plan/04-faster-interchange-address.md) | §4 | ✅ 129/129 | ✅ 126/126 | 375 |
| [Simultaneous butterfly layers with compact control](plan/05-simultaneous-butterfly-layers.md) | §5, §11, CrocSwap | ✅ 1641/1641 | 🟡 1266/1270 | 1654 |
| [Synthetic transforms and their tape layout](plan/06-synthetic-transforms-tape.md) | §6 | ✅ 5/5 | ⬜ 0/3 | 7 |
| [Gaussian resampling](plan/07-gaussian-resampling.md) | §7 | ✅ 17/17 | 🟡 8/9 | 59 |
| [Fast multiplication subroutine](plan/08-fast-multiplication-subroutine.md) | Schönhage–Strassen | ✅ 22/22 | 🟡 11/15 | 85 |
| [Exact multiplication, parameters, time bound](plan/09-exact-multiplication-parameters.md) | §8 | 🟡 5/7 | ⬜ 0/2 | 11 |
| [End-to-end theorem `EndToEnd`](plan/10-end-to-end.md) | — | 🟡 5/8 | 🟡 5/8 | 6 |

## 1. Machine model and target statement (§2)

Details: [plan/01-machine-model-target.md](plan/01-machine-model-target.md)

| Sub-problem | Mathematics | Tape | Files |
| --- | --- | --- | --- |
| Machine model and target statement | ✅ 2/2 | ✅ 2/2 | 1 |
| Axiom audit | ✅ 1/1 | — | 1 |

## 2. Composition, loops, frames, elementary streams (§2)

Details: [plan/02-composition-loops-frames.md](plan/02-composition-loops-frames.md)

| Sub-problem | Mathematics | Tape | Files |
| --- | --- | --- | --- |
| Machine combinators and frames | ✅ 7/7 | ✅ 7/7 | 13 |
| Counters and counted loops | 🟡 14/15 | 🟡 14/15 | 28 |
| Binary and radix arithmetic machines | ✅ 35/35 | 🟡 34/35 | 51 |
| Rational scaling of one coordinate | ✅ 29/29 | 🟡 22/29 | 46 |
| Controlled shift of one coordinate | ✅ 25/25 | ✅ 23/23 | 36 |
| Common coordinates and schedule assembly | ✅ 27/27 | 🟡 21/23 | 56 |
| Packed-line and window gadgets | ✅ 6/6 | ✅ 6/6 | 9 |
| Tape radix sort | ✅ 10/10 | ✅ 9/9 | 16 |

## 3. Finite networks with a rank saving (§3)

Details: [plan/03-finite-networks-rank.md](plan/03-finite-networks-rank.md)

| Sub-problem | Mathematics | Tape | Files |
| --- | --- | --- | --- |
| Scalar shear and bank exchange circuits | ✅ 6/6 | ⬜ 0/6 | 8 |
| Wire counts and bilinear label spaces | ✅ 7/7 | — | 9 |
| Grouped gates and binary residual units | ✅ 13/13 | ⬜ 0/9 | 15 |
| Projection-rank trace and h=25 saving | ✅ 10/10 | ⬜ 0/1 | 15 |
| Shared-point h=50 network and compilation | ✅ 14/14 | ⬜ 0/11 | 251 |
| Optimized global rank trace | ✅ 6/6 | ⬜ 0/5 | 22 |
| Optimized physical program and interchange | ✅ 7/7 | ⬜ 0/7 | 22 |
| Tape realization of the network | ✅ 3/3 | 🟡 1/3 | 18 |

## 4. Faster interchange of address chunks (§4)

Details: [plan/04-faster-interchange-address.md](plan/04-faster-interchange-address.md)

| Sub-problem | Mathematics | Tape | Files |
| --- | --- | --- | --- |
| Interchange recurrence and padding arithmetic | ✅ 1/1 | — | 1 |
| Triangular factorization and shear (Lemmas 4.1-4.2) | ✅ 2/2 | ✅ 1/1 | 4 |
| Tape primitives: role transport, stacks, descriptors | ✅ 12/12 | ✅ 12/12 | 37 |
| Single-digit base case | ✅ 4/4 | ✅ 4/4 | 11 |
| Recursive node operations | ✅ 15/15 | ✅ 15/15 | 59 |
| Recursive call protocol and child headers | ✅ 14/14 | ✅ 13/13 | 34 |
| Power-width recursive machine (Prop 4.3) | ✅ 19/19 | ✅ 19/19 | 60 |
| Row/range padding and radix digit movement | ✅ 11/11 | ✅ 11/11 | 34 |
| Arbitrary-width piece dispatcher (Lemma 4.4) | ✅ 41/41 | ✅ 41/41 | 120 |
| Binary interchange wrapper | ✅ 10/10 | ✅ 10/10 | 16 |

## 5. Simultaneous butterfly layers with compact control (§5, §11, CrocSwap)

Details: [plan/05-simultaneous-butterfly-layers.md](plan/05-simultaneous-butterfly-layers.md)

| Sub-problem | Mathematics | Tape | Files |
| --- | --- | --- | --- |
| Packed arithmetic and fixed control gadgets | ✅ 185/185 | ✅ 177/177 | 191 |
| Active-target compact controls | ✅ 273/273 | 🟡 193/194 | 273 |
| Exceptional-address destination repair | ✅ 247/247 | ✅ 190/190 | 255 |
| Row padding, reservation and allowances | ✅ 72/72 | 🟡 56/57 | 72 |
| Binary basis stages and phase schedules | ✅ 103/103 | ✅ 64/64 | 103 |
| Butterfly and unit-phase record arithmetic | ✅ 207/207 | ✅ 164/164 | 207 |
| Butterfly axes, spectators and native roles | ✅ 140/140 | ✅ 98/98 | 140 |
| Recursive geometry, controller and child headers | ✅ 44/44 | ✅ 38/38 | 44 |
| Exact scalar grids and stopped calls | ✅ 92/92 | ✅ 72/72 | 92 |
| Nonleaf calls and the fixed node table | ✅ 48/48 | ✅ 46/46 | 48 |
| Source-ready table, orientation and endpoints | ✅ 155/155 | ✅ 133/133 | 155 |
| Full recursive execution and runtime | ✅ 75/75 | 🟡 35/37 | 77 |

## 6. Synthetic transforms and their tape layout (§6)

Details: [plan/06-synthetic-transforms-tape.md](plan/06-synthetic-transforms-tape.md)

| Sub-problem | Mathematics | Tape | Files |
| --- | --- | --- | --- |
| Synthetic ring and synthetic FFT | ✅ 3/3 | ⬜ 0/1 | 4 |
| Bluestein reduction | ✅ 1/1 | ⬜ 0/1 | 2 |
| Tape layout and cost bracket | ✅ 1/1 | ⬜ 0/1 | 1 |

## 7. Gaussian resampling (§7)

Details: [plan/07-gaussian-resampling.md](plan/07-gaussian-resampling.md)

| Sub-problem | Mathematics | Tape | Files |
| --- | --- | --- | --- |
| Exact Gaussian resampling factorization | ✅ 5/5 | — | 8 |
| Numerical resampling maps and error bounds | ✅ 3/3 | — | 11 |
| Fixed-point word and record layer | ✅ 2/2 | ✅ 2/2 | 12 |
| Gaussian weight tables on tapes | ✅ 1/1 | ✅ 1/1 | 12 |
| Resampling maps on tapes | ✅ 5/5 | ✅ 5/5 | 13 |
| Tensor interface line costs | ✅ 1/1 | 🟡 0/1 | 3 |

## 8. Fast multiplication subroutine (Schönhage–Strassen)

Details: [plan/08-fast-multiplication-subroutine.md](plan/08-fast-multiplication-subroutine.md)

| Sub-problem | Mathematics | Tape | Files |
| --- | --- | --- | --- |
| Fourier and fixed-point foundations | ✅ 7/7 | — | 23 |
| Schönhage–Strassen level, schedule and cost | ✅ 3/3 | — | 4 |
| Word-tape programming layer | ✅ 1/1 | ✅ 4/4 | 10 |
| Schönhage–Strassen multiplier on tapes | ✅ 4/4 | 🟡 3/4 | 14 |
| Packed signed ring products | ✅ 3/3 | ✅ 3/3 | 28 |
| Paper-format transform layer statements | ✅ 4/4 | 🟡 1/4 | 6 |

## 9. Exact multiplication, parameters, time bound (§8)

Details: [plan/09-exact-multiplication-parameters.md](plan/09-exact-multiplication-parameters.md)

| Sub-problem | Mathematics | Tape | Files |
| --- | --- | --- | --- |
| Parameters, asymptotics and prime existence | 🟡 2/3 | — | 3 |
| Exact recovery of the product | ✅ 2/2 | ⬜ 0/1 | 4 |
| Cost table and time bound | 🟡 1/2 | ⬜ 0/1 | 4 |

## 10. End-to-end theorem `EndToEnd`

Details: [plan/10-end-to-end.md](plan/10-end-to-end.md)

| Sub-problem | Mathematics | Tape | Files |
| --- | --- | --- | --- |
| Literal input front end | ✅ 1/1 | ✅ 1/1 | 1 |
| Quadratic fallback multiplier | ✅ 4/4 | ✅ 4/4 | 4 |
| Fast program assembly and final bound | 🟡 0/3 | 🟡 0/3 | 2 |

## Next steps

- Assemble synthesized piece descriptors with repeated scaling, repeat inverse scaling, then compose signed rational scales and computed varying-offset translations.

- Compute repair keys and run extraction, sorting and reinsertion on tapes, with the `RepairPipeline` composition as the specification.
- Compile the proved optimized h=50 modular physical network and its fixed rational control schedule to literal tape execution and prove its recursive time bound.
- Account for complex endpoint corrections in the tape implementation.
- Finish the `NegacyclicKronecker` subroutine component.
- Compose the proved rational digit arithmetic into matrix routines and compile the finite network address permutations to literal tape steps.
