# M5: balanced positional transforms and coordinate routing

M5 removes the multiplicative layout loss of the synthetic transforms (plan
`plan/D-sharper-bound.md`, §6, "M5"). It has two independent parts:

* **M5a, the balanced positional layout.** The prefix charge `T p d K` becomes `T p d`, so the
  prefix margin moves from `1 - ε(1+c)` to `1 - ε`. It uses only the existing layout and its
  single-bit moves and equal-width chunk interchanges, at a chunk width chosen from `n = ℓ - 1`.
* **M5b, arbitrary-source coordinate routing.** The layout charge `T p · p K^(τ-1)` becomes
  `T p · p^τ polylog p`, so the layout margin moves from `ε c a_b` to `a_b`. It needs a new
  routing machine.

## 0. What M5 is worth

Write `a_b = 1 - τ`, `a_c = 1 - σ`. The compact route's stage margins are (`CompactInterim.margin`,
`CompactStageGrowth.exp_facts`):

| charge | margin now | after M5a | after M5b |
| --- | --- | --- | --- |
| prefix moves and prefix rounds `T p d K` | `1 - 2ε` (through `K ≤ d`) | `1 - ε` | `1 - ε` |
| chunk exchanges `T p · p K^(τ-1)` | `ε c a_b` | `ε c a_b` | `a_b` |
| compact layer `T p ℓ d^λ'` | `ε (1 - λ')` | unchanged | unchanged |
| CRT and resampling exposures | `(1 - ε) a_b` | unchanged | unchanged |

At the current parameters (`ε = 31/64`, `c = 7/8`, `a_b = 2.96·10^-9`, `a_c = 2.5·10^-9`) the layer
margin binds, so M5 does not change κ today. With the selected suppliers of M6
(`a_c = 7/4178`, `a_b = 10/5769`) and `ε < 1/2`, M5b lifts the layout margin from
`ε c a_b ≈ 7.3·10^-4` to the layer margin `ε a_c ≈ 8.1·10^-4`, about 0.15 bits. The larger gain
comes with `ε → 1`, which the selected construction reaches only with all of:

* M7, the faster Gaussian inverse and bulk exposure (margin `a_b` for the exposures);
* a prime supply in short intervals for the `d` moduli (`prime_interval_packing`);
* M5a, because `ε(1+c) < 1` with `ε → 1` forces `c → 0`, and without balancing the prefix margin
  `1 - ε(1+c)` falls below the compact-layer margin `ε q`;
* M5b, because with `c → 0` the chunk exchanges cost `ε c a_b ≈ ε a_b^2`.

Then the binding margin is `ε q → a/(1+a)`, the selected target `0.00167 ≈ 2^-9.2`, compared with
`≈ 2^-10.4` from the same suppliers on the present layout at `c = 7/8`.

## (a) The current schedule and its charge

The logical record address of a transform is the concatenation of `D = d - 1` axes of
`aᵢ ∈ {ℓ - 1, ℓ}` bits (`LayHyp`, `Fast/LayoutMath.lean`). Bit `h` of axis `i` is
`off es i + h`.

**The layout `L = layPerm es ℓ K`** (`Fast/LayoutMath.lean`):

* `layB ℓ K = (ℓ - 1) % K`, `layQ ℓ K = (ℓ - 1) / K`.
* `layPre`: the top slot of each long axis, then the slots `h < b` of every axis.
* `layMoves = layPreMoves … (layPre …) ++ layXcMoves K (laySwaps (D q) (layTr D q))`: single-bit
  moves to the prefix, then the scan of `layTr D q` (axis-major to chunk-major) as chunk
  exchanges.
* Host form (`Fast/Layout.lean`): `layBits` (the bit moves as position pairs) and `layXcs` (the
  exchanges with headers).

**The machines** (`Fast/LayoutMove.lean`):

* `layMoveBit`, `layMoveBit_exec`: one single-bit move costs `layMvCost N B = O(V)`.
* `layXchg`, `layXchg_exec`, `layXchg_exec_le`: one exchange of two width-`K` chunks at arbitrary
  offsets costs `3 C_swap (T + 12 swapT t₀ + 5) 2^n B max(1,K)^τ`. This is `swapPass` with
  `BinaryInterchangeRun`, the bit supplier at width `K`.

**The layout programs** (`Fast/SynLayPre.lean`, `SynLayFwd.lean`, `SynLayOpp.lean`,
`SynLayUnapply.lean`, `SynLayKit.lean`, `SynLayRegs.lean`):

* `slyFwd`, `slyOpp`: setup `slySetup`, then the writer of the description streams
  (`ldgWriter … ldxCode`), then `layApply` or the reversal plus `layUnapply`, then `slyClean`.
* Costs: `slyFwdCost`, `slyOppCost`; contracts `slyFwd_lay`, `slyOpp_lay`; specifications
  `slyFwd_spec_br`, `slyOpp_spec_br` (`SynLaySpec.lean`).

**The rounds** (`Fast/SynFwd.lean`, `Fast/SynRec.lean`, `Fast/SynSel.lean`):

* `synFwd`, `synOpp`: one loop over `nRounds a` rounds; the records stay in the physical order
  `synPi L`.
* `synChunk ℓ K h` (`h + 1 < ℓ ∧ layB ℓ K ≤ h`) marks a chunk round. `synOS` is the selected
  offset. `synPcs`/`synCfg` are the layer pieces.
* `synSel_chunk`, `synSel_top`, `synSel_low` relate the selected bits to the physical layout.

**The charges**:

* `Cost/MatchSynLay.lean`, `ml_stage_le`: at most `d K` bit moves and `d q` exchanges give
  `C T p (d K + p K^(τ-1))`.
* `Cost/MatchLayout.lean`: `mt_lay_stage_le`, `mt_lay_stage_le_conv`.
* `Cost/MatchSynLoop.lean`: `mr_rounds_split` (at most `b + 1 ≤ K` prefix rounds),
  `mr_prefix_layer_le`, `mr_chunk_layer_le`, `mr_loop_cost_le`.
* `Cost/MatchSynPcs.lean`, `mrP_pieces_le`: the layer pieces, `d^λ'`.
* The compact route repeats these bounds in `Cost/CompactRetunedLayoutMatch.lean`
  (`compactRetuned_ml_stage_le`, `compactRetuned_ml_lay_cost_le_gen`) and
  `Fast/CompactSourceCost.lean`. It absorbs them in `CompactTotal.conv`
  (`T p (d K + p K^(τ-1) + ℓ d^λ' + grLogLog (r p))`, `Cost/CompactStageGrowth.lean`), with the
  layout margin `κ ≤ ε · cParam · (1 - τ)` and the prefix fact `2ε ≤ 1 - κ` of `exp_facts`.

The manuscript's statement is Lemma 16, `O(T p [d K + p K^(τ-1) + ℓ d^λ'])`
(`~/imul/openai-109/paper.pdf`, §6.2).

**Contiguous exchanges cannot do better.** Exchanging two contiguous equal-length runs of chunks
changes at most four chunk adjacencies. The transposition `layTr D q` needs `D q - 1` new
adjacencies, so any schedule of contiguous exchanges uses at least `(D q - 1)/4` of them, each of
width at least `K`. Their cost is `Ω(V p K^(τ-1))`. Lowering the layout charge therefore needs a
movement primitive on non-contiguous coordinate sets: M5b.

## (b) The selected construction

Sources, all at CrocSwap revision `0fdd7d82de03e43c9e5a1000dfbcd380d1b687d2` (the pin of
`docs/sharper-bound-source.json`; local clone in the session scratchpad `croc/repo`):

* `notes/structured-bulk-assembly.tex`, §"Coordinate routing" and the exact selected assembly
  (the seven margins).
* `references/copied-fixed/pr34/review-balanced-transform.md`: the balanced positional layout.
* `references/semantic-bulk/rad20/reports/compact-arbitrary-source-routing.md`: the
  arbitrary-source XOR routing. Its own text states that independent mathematical review is
  pending.
* `research/complex-sw4-frame8/vendor/main/research/complex-k492-owner-repair/vendor/multicold/engines/outer.py`:
  the balanced outer engine with margins `balanced_prefix = 1 - ε`, `coordinate_movement = a`.
* The OpenAI manuscript `~/imul/openai-109/paper.pdf`, §§6.1–6.2.

**Balanced positional layout.** Put `n = ℓ - 1` and `q = ⌊n/K⌋`, and write `n = qL + t`
with `0 ≤ t < q`. Every axis splits its `n` common slots into `t` chunks of width `L + 1` and
`q - t` chunks of width `L`, so `K ≤ K_j < 2K` (`Balanced/Widths.lean`). Only the extra top
slot of each long axis moves to the prefix, at most `d - 1` bit moves. The chunk order goes from
axis-major to group-major in at most `D q - 1` transpositions. An unequal transposition of
adjacent widths `L`, `L + 1` is one single-bit move and one equal-width interchange:
`a₀ x M y → x M a₀ y → y M a₀ x`. All rounds of group `j` see the same width `K_j` and one
common offset. The compact layer takes `K_j` as a supplied round parameter with
`⌊d^c⌋ ≤ K_j < 2⌊d^c⌋`. The cost is `O(T p [d + p K^(τ-1) + ℓ d^λ'])`.

**Coordinate routing.** The input is a complete rectangular stream `[P] × [2^n] × [R₀]` and a
permutation of the `n` named coordinates, given by a poly(`p`) description. The cost is
`O(V p^τ polylog p + poly p)`. The construction has six parts:

1. **The masked later-source shear.** Fields `u, t` sit at the front, `y` in the middle and `b`
   at the back, each temporary field `H` bits wide. The targets are `j_i = ρ + iK` in `y` for
   `i` in an `ACTIVE` set, and the sources `s_i` are distinct positions outside the target set.
   Four modular updates `F_u` toggle `y[j_i]` by `parity(u_i)` and restore `t`. Then `F_u`, the
   load `u += A(y)`, `F_u` and the unload `u -= A(y)` give the shear `y[j_i] ^= y[s_i]`. That is
   ten rotations and twelve interchanges. Every rotation's controls precede its target, so each
   rotation is a global bijection.
2. **Repair.** On the good set (guard digits away from carries) the construction equals the
   ideal shear `T`. It maps the bad set to itself. The bad records are extracted, keyed by
   `T(S⁻¹(address))`, stably radix-sorted and reinserted into the marked holes. With
   `G = 4⌈log₂ p⌉ + 6` and `K = 64G` the bad density is at most `5/(128 p³)`, so repair costs
   `O(V)`.
3. **Reservoirs and matchings.** For `n ≥ 64G`, take `H = ⌈n/K⌉ G` and three disjoint
   reservoirs `R_k` of `3H` bits each. A matching splits into three edge classes, each avoiding
   one reservoir, and the class's reservoir is placed in `u, t, b` by at most three equal-width
   interchanges. Each class is three directional shears, split by residue mod `K` into `O(K)`
   gadget calls of at most `H/G` active digits, at cost `O(V K (H^τ + 1)) = O(V n^τ polylog p)`.
   The last `K` positions use elementary XORs through two bit moves and one quarter interchange.
4. **Permutations.** Every permutation is a product of two involutions. On a cycle `c_j`,
   `A(c_j) = c_{-j}` and `B(c_j) = c_{1-j}`.
5. **Spectators.** Coefficient records of `O(p)` bits get an untouched spectator field of
   `ℓ = Θ(p^(1-ε))` bits per class, which makes the record superpolynomial. For `n ≤ 3ℓ` the
   elementary method costs `O(V n)`, below `V p^τ` when `ε > a_b`.
6. **Setup.** The descriptors are computed in poly(`p`) and absorbed by the tensor volume.

## (c) The replacement schedule

### M5a

The present layout cuts the `n = ℓ - 1` common slots of every axis into `q = ⌊n/K⌋` chunks of
width `K` and moves the remaining `b = n mod K` low slots to the prefix. The prefix charge
`d (b + 1)` bit moves and `b + 1` prefix rounds is `T p d K` only because `b < K`. A chunk width
that leaves a small remainder removes it.

* **The uniform balanced width.** `unifWidth n K = max K (n / ⌊n/K⌋)` (`Balanced/Widths.lean`).
  For `1 ≤ K ≤ n` it is `w = n / q`, with `K ≤ w < 2K` (`le_unifWidth`, `unifWidth_le_two_mul`)
  and remainder `n mod w < q` (`mod_unifWidth_lt`): `n = w q + r` with `r = n mod q < q`, and
  `n mod w = r mod w ≤ r`. Every chunk has the one width `w`, so the rounds, the selected-bit
  offsets (`layPerm_sel_chunk`) and the layout programs are the present ones at `K := w`.
* **The chunk width of the compact chain.** `CompactSizes.K n` becomes
  `min d (max K₀ (unifWidth (ℓ - 1) K₀))` with the root `K₀ = ⌊d^(7/8)⌋`. Under `Big`,
  `2 K₀ ≤ d` and `K₀ < ℓ - 1`, so it is the uniform width. Unconditionally
  `K₀ ≤ K ≤ min (d, 2 K₀)`: every lower bound on `K` stays as it is, and the upper bounds
  `K ≤ d^c`, `K ≤ B^(εc)` lose a factor `2`. The parameter program computes it after the root
  with two divisions and two comparisons.
* **Charge.** Under `Big` the prefix holds `b + 1 ≤ q ≤ (ℓ - 1)/K₀` slots per axis, so the
  bit moves and the prefix rounds cost
  `T p d (b + 1) ≤ T p · d ℓ / K₀ ≤ T p · p/(3 K₀) ≤ T p · p K^(τ-1)`, with `dℓ ≤ p/3`,
  `K ≤ 2 K₀` and `K^(τ-1) ≥ K^(-1)`. The prefix charge joins the chunk-exchange charge, and the
  convolution envelope becomes `T p (d + p K^(τ-1) + ℓ d^λ' + log log (r p))`.
* **Register, stack and round interface.** Unchanged: `p .K` holds the new width, and the
  rounds, `synChunk`, `synOS`, `synCfg` and the move lists are the present ones at that width.

The variable-width layout of (b) (`balWidth`, `balOff`, chunks of widths `L` and `L + 1`, one
unequal transposition lowered to a bit move and an equal-width exchange) reaches the same
charge with a per-round width; the uniform width needs none of it.

### M5b

* **Router contract.** A program `crRoute` on the record stream with:
  * a poly(`p`) coordinate permutation description on a work band;
  * the interchange bank, the compact rotation machine and a radix-sort scratch;
  * spectator fields for short records;
  * the postcondition: records moved by `layRec π`, every scratch and guard bit restored, all
    other registers unchanged;
  * cost `C V (p^τ log^k p + 1) + poly p`.
* **Layout.** `L_bal` keeps the prefix moves of M5a and replaces the chunk transpositions by one
  `crRoute` call with `π` the group-major permutation. Its inverse is one more call with `π⁻¹`.
* **Primitives reused:**
  * `layXchg` at width `H` (the reservoir placement and the twelve gadget interchanges);
  * `layMoveBit`;
  * the compact-control modular rotation `y += f(u, t) mod 2^w`, whose controls precede its
    target (the rotation and copy fibers of `Cost/CRTControl*.lean`, `Fast/CRTSwap.lean`);
  * the stable record radix passes of the CRT routing.
* **New:**
  * the four-update shear gadget, its good-set predicate and its global bijectivity;
  * bad-record extraction and reinsertion;
  * the matching partition, the involution decomposition and the residue split;
  * the spectator placement.
* **Charge.** `O(T p · p^τ polylog p)` for the layout, independent of `K`.

## (d) What changes

**Statement changes, M5a:**

* `Mult/CompactSizes.lean`: `K` becomes the uniform width above `Kroot = ⌊d^(7/8)⌋`;
  `K_eq_floor`, `K_pow_le`, `le_K_iff` move to `Kroot`; new `Kroot_le_K`, `K_le_two_Kroot`,
  `two_Kroot_lt_d`, `K_eq_unif`, `mod_K_succ_le`.
* `Fast/CompactParamProg.lean`: `compactPmOverwrite` gains the width program;
  `compactPmOverwriteAtoms` gains its atoms.
* `Cost/CompactGrowth.lean`: `compact_K_le_d_rpow`, `compact_K_le_rpow` with the factor `2`.
* `Cost/CompactStageGrowth.lean`: `conv` with `d` in place of `d K`; `exp_facts` with `ε ≤ 1 - κ`
  in place of `2ε ≤ 1 - κ`; `conv_le` and its constants.
* `Cost/CompactRetunedLayoutMatch.lean`, `Cost/CompactRetunedTransformMatchR.lean`,
  `Cost/CompactRetunedDirectCost.lean` (`compactRetuned_conv_ge`): the bit moves and the prefix
  rounds against `p K^(τ-1)` through `CompactTotal.prefix_le`
  (`d ((ℓ - 1) mod K + 1) ≤ p K^(τ-1)` under `Big`).

**Proof-only changes, M5a:** the consumers of the upper bounds of `CompactSizes.K` (`K ≤ d`,
`K ≤ d^c`) and of `compactPmOverwrite_do`.

**Statement changes, M5b:**

* `ml_stage_le`, `compactRetuned_ml_stage_le`, `mt_lay_stage_le_conv`: the term `p K^(τ-1)`
  becomes `p^τ (log₂ p)^k`.
* `CompactTotal.conv`, `CompactStageGrowth.conv`, `Cost/Total.lean` (`totConv`, and the bound
  `p K^(τ-1) ≤ 24 b^(1-κ)` in its proof): the layout term changes and the margin
  `κ ≤ ε · cParam · (1 - τ)` (`CompactInterim.margin 0`, `exp_facts`) becomes
  `κ < 1 - τ` with strict room for the polylogarithm.
* `CompactInterim.compact_slacks` and `margin`.

**Unchanged:** the pointwise product, the CRT and resampling stages, the layer recurrence and
`Parameters`. M5b also leaves the compact layer untouched.

## (e) Staged plan

Line counts and agent time are conservative. Times assume the shared Lean lock and the
24 GB machine. The present layout stack (`LayoutMath`, `Layout`, `LayoutMove`, `LoadLayout*`,
`SynLay*`, `SynRec`, `SynSel`, the matching files) is about 11k lines.

| stage | content | new or changed lines | agent time |
| --- | --- | --- | --- |
| 0 | Confirm with Kenny that M5 is unclaimed; agree on file ownership for the compact layer width change | — | days |
| 1 | The uniform balanced width (`Balanced/Widths.lean`: `unifWidth`, `mod_unifWidth_lt`) | 100 | done |
| 2 | The uniform width as `CompactSizes.K`: sizes, parameter program, consumers of its upper bounds | about 250 changed | done |
| 3 | Layout programs | none (the present programs at the new width) | — |
| 4 | M5a cost matching and margin rewiring (`d K → d`, `2ε → ε`, `CompactTotal.prefix_le`) | about 150 changed | done |
| 5 | M5b mathematics: shear identity, good set, bijectivity, repair correctness, reservoir partition, involution decomposition, spectators | 2.5–4k | 4–6 weeks |
| 6 | M5b machine: gadget rotations, bad-record extraction and reinsertion, descriptor generation, spectator placement | 5–8k | 8–12 weeks |
| 7 | M5b cost matching, layout replacement, `conv` and margin rewiring | 1.5–2.5k | 2–4 weeks |

Stages 1–4 (M5a) are under 1k lines and finish independently of M5b. M5b is 9–15k lines and 3–5
months of agent time. The riskiest parts are stage 2, which changes the chunk width of the
compact layer chain that Kenny is extending under M3, and stage 6, whose argument is still
awaiting review upstream.
