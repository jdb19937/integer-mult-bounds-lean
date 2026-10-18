# M5: balanced positional transforms and coordinate routing

M5 removes the multiplicative layout loss of the synthetic transforms (plan
`plan/D-sharper-bound.md`, §6, "M5"). It has two independent parts:

* **M5a, the balanced positional layout.** The prefix charge `T p d K` becomes `T p d`, so the
  prefix margin moves from `1 - ε(1+c)` to `1 - ε`. It uses only the existing single-bit moves and
  equal-width chunk interchanges.
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

* **Layout.** `balPerm es ℓ K : Equiv.Perm (Fin es.sum)` replaces `layPerm`. Its moves are the
  long-axis top-slot moves, then the scan of the variable-width chunk transposition, each
  unequal transposition lowered to one bit move and one equal-width exchange. `layBits` and
  `layXcs` get balanced counterparts with the same register-level description-stream formats.
  The writer `ldgWriter` and the loaders `ldlPrepM`, `ldlPrepX` stay unchanged and consume the
  new lists.
* **Register and stack interface.** It is unchanged:
  * record stream on `lreg .io`;
  * layout wires `ly 1 … ly 22` (`slyRg`), interchange bank `swp 0`, temporaries `slyT c`;
  * park predicate `slyPk W E`;
  * unary sizes on `p .N, p .ℓ, p .K, p .D`.
* **One new per-round input: the group width `K_j`.** The persistent wire `p .K` keeps
  `K = ⌊d^c⌋`. The round header (`synCfg`) carries `K_j` and the group offset `balOff n q j`.
* **Rounds.**
  * Forward: the top round on the long axes (individual prefix processing, as the present prefix
    rounds), then the common rounds `h = ℓ - 2, …, 0` in decreasing order. All are chunk rounds
    of their group.
  * Opposite: the same rounds in reverse, ending with the top round.
  * Frequency order: slot `(i, h)` keeps frequency significance `aᵢ - 1 - h`, and the monomial
    exponent `E = -Σ (2r/2^(h+1)) bᵢ kᵢ mod 2r` is computed from the named slots. The exact
    operators are `L_bal B F⁻` and `F⁺ B⁻¹ L_bal⁻¹`, so the pointwise product and the
    opposite transform keep their present conventions.
* **Spectators.** Prefix slots and the other chunk groups are spectators of every common round.
  The opposite program restores the original box order with the inverse moves in reverse.
* **Charge.** At most `d - 1` bit moves and `D q - 1` transpositions, `O(T p (d + p K^(τ-1)))`.
  There is one prefix round, so `O(T p d)` for prefix rounds.

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

* `Fast/LayoutMath.lean`: new `balPerm`, `balMoves`. `layPerm` and `layB` stay for the present
  route.
* `Fast/SynRec.lean`: `synChunk`, `synOS`, `synCfg`, `synPcsR` take the group width `K_j` and the
  offset `balOff`. The low rounds disappear (`layB` no longer occurs).
* `Fast/SynSel.lean`: `synSel_chunk` and `synSel_top` for `balPerm`. `synSel_low` has no
  counterpart.
* `Fast/SynFwd.lean`: `synFwd_spec_br`, `synOpp_spec_br` and `SynV` take the layout permutation as
  a parameter, so `layPerm` becomes a variable `L` with the selected-bit property as a hypothesis.
* `Fast/SynLaySpec.lean`: `slyFwd_spec_br`, `slyOpp_spec_br` at `balPerm`.
* The compact layer chain, statement change in the chunk width: every lemma taking
  `Mult.CompactSizes.K M` as the round width takes a supplied `K'` with
  `K ≤ K' < 2K`. This covers `CompactSynHybridRoundR`, `CompactSynLayerFitR`,
  `CompactRetunedLayerMatchR` (`compactRetunedR_layer_chunk_eventually`),
  `CompactReservationFits`, `compactTopRows_bounds`, `CompactCallerRetunedCapacity` and the
  reservation counts (`ceil(2dG/K')+ceil(dG/K')` only decreases in `K'`).
* `Cost/MatchSynLay.lean` `ml_stage_le`, `Cost/CompactRetunedLayoutMatch.lean`
  `compactRetuned_ml_stage_le`: the right side `d K + p K^(τ-1)` becomes `d + p K^(τ-1)`.
* `Cost/MatchSynLoop.lean` `mr_rounds_split`, `mr_prefix_layer_le`: one prefix round.
* `CompactTotal.conv` and `CompactStageGrowth.conv`: `d K` becomes `d`. `exp_facts` replaces
  `2ε ≤ 1 - κ` by `ε ≤ 1 - κ`.

**Proof-only changes, M5a:**

* `slyFwd_lay`, `slyOpp_lay`, `sly_post_fwd`, `sly_post_opp`, `ldLayGenStage_exec` and the
  writer lemmas, now on the new move lists with the same formats;
* the twiddle-exponent lemmas (`Fast/TwiddleL.lean`, `twPosL`), which already take the
  permutation;
* `mrP_pieces_le`.

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
| 1 | Balanced arithmetic: widths, offsets (`Balanced/Widths.lean`), `balPerm`, unequal-transposition lowering, selected-bit offsets per group, frequency order | 1.2–1.8k | 1–2 weeks |
| 2 | Supplied chunk width `K'` through `SynRec`, `SynSel` and the compact layer chain | 2.5–4k changed | 3–5 weeks |
| 3 | Balanced move lists and layout programs on the existing writer and loaders | 1.5–2.5k | 2–3 weeks |
| 4 | M5a cost matching and margin rewiring (`d K → d`, one prefix round) | 0.8–1.2k | 1–2 weeks |
| 5 | M5b mathematics: shear identity, good set, bijectivity, repair correctness, reservoir partition, involution decomposition, spectators | 2.5–4k | 4–6 weeks |
| 6 | M5b machine: gadget rotations, bad-record extraction and reinsertion, descriptor generation, spectator placement | 5–8k | 8–12 weeks |
| 7 | M5b cost matching, layout replacement, `conv` and margin rewiring | 1.5–2.5k | 2–4 weeks |

Total: 15–24k lines, 5–8 months of agent time. Stages 1–4 (M5a) are 6–9k lines and 2–3 months
and can finish independently. The riskiest parts are stage 2, which touches the compact layer
chain that Kenny is extending under M3, and stage 6, whose argument is still awaiting review
upstream.
