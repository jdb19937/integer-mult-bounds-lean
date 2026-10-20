# M8: the PR97 bit supplier

M8 replaces the Shared50 recursion behind `Machine/BinaryInterchangeRun` with the two-stage
partial-swap word of PR97. The supplier needs no routes, charts, cover classes or helper hosting.
It runs on the existing recursive interchange machine model. Stage 1 uses rank-one children in the
existing uniform recursion. Stage 2 adds the opposite-bank compiler (variable-rank reversed
children over atom rings, stopped recurrence).

## 1. Numbers

`h = 23`, `v = C(23,3) = 1771`, `m = h² = 529`, `N = v² = 3136441`, `R = 28866` side roles per
invocation, `W = 2N + 2vR = 108516254`, `L = 2vh(h-1) = 1792252`, rank mass
`s = Wm − N + L = 57403754177`, deficit `Wm − s = N − L = 1344189`.

| bit supplier | `a_b` | κ with T16 (≈ 0.45·a_b) |
| --- | --- | --- |
| Shared50 (current) | `2.96·10⁻⁹` | `2^-29.6` |
| stage 1: PR97, rank-one children | `3.734·10⁻⁶` | `2^-19.2` |
| stage 2: opposite bank, plain frames (section 5) | `9.69·10⁻⁵` | `2^-14.5` |
| stage 2: opposite bank, upstream's design-B frames | `1.2402·10⁻⁴` | `2^-14.1` |

The rank-one saving is `(1 − s/(Wm))/ln m` up to the certified grid point; stage 2 is
`(1 − θ)a* + θ·a_leaf` with `θ = 1/1000`, `a*` the whole-projector moment saving and `a_leaf`
the leaf interchange (Shared50 here).

## 2. Sources

Pinned in upstream at `463113d6`, `references/partial-gauge/pr97/` (hashes in its `SOURCE.json`):
- PR97, Zhihao Chen, `jacklightChen/integer-mult-bounds@e15350b6`: the literal ledger
  (`round7_literal_frame_ledger.py`) and `PROOF.md` (two-stage gauges, exits, connectors,
  reflected word, rank-one copy correction).
- Swapnil Jain's round-7 witness, `Swapnil-jain/integer-mult-kappa@741e7aa0`:
  `witness_23.json.gz` (the side DAG: 64042 nodes, 5313 outputs, 23 retained centres,
  38741 links, the flag matrix, lift indices, late copies), `deferred_23.json.gz` (the design-B
  schedule: 82983 ops, deferred readout frames, V-leaf frames), `check_frames.py`,
  `check_lifted.py`, `deferred.py`, `linalg.py`.
- icekylinx's #104 compiler: `notes/stopped-product-factorization.tex`,
  `notes/stopped-product-interface.tex`, `notes/partial-gauge-construction.tex`,
  `certificates/partial-gauge-bit-input.json`, `scripts/partial_gauge_bit.py`.

The ledger replays here unchanged: 1080616 events (856849 XORs, 223744 moves, 23 centre
copies), 90173 frame keys, complete forward and reflected F2 shear, `s = 57403754177`.

## 3. What the tree already has

- **Frames are free in the semantics.** `Networks/FramedCircuit`: any linear equivalences as
  frames; `common_frame_identity` makes the compiled run `encode output ∘ scalar ∘ decode input`,
  and `independent_of_intermediate_frames`. Correctness of a node is scalar correctness plus its
  endpoint frames; intermediate frames only change cost.
- **Field programs.** `AffineFieldProgram.Op`: in-group ordered affine steps, `addToD`,
  `subFromD`, and `interchange i j`, which swaps `H_i` with `D_j` for independent `i`, `j`. The
  tape runs the nonrecursive steps as `OrderedAffine` steps on the flat `H ++ D` vector
  (`AffineFieldCoordinates`) and each `interchange` as one child.
- **Factorization.** `Swap/LowerTriangular.factorization`: `A = E₁ Π E₂`, lower-triangular
  invertible factors and a pivot list with distinct rows and columns; `PivotRank` gives
  `L.length = rank A`. `ModularFrameSchedule` and `Swap/Modular` choose one prime avoiding every
  denominator and reduce rational programs to `ZMod (q^b)`.
- **The machine.** `Shared50Recursive*` over the generic `Recursive*` layer runs any fixed
  control list `List (FramedControlSchedule.Step World (ZMod 2) FieldProgram)` with XOR gates,
  segments and interchange calls. It is hardwired to Shared50 through `roleCount`, `m = 125000`,
  `Shared50PieceSchedule.pieces` and `Shared50FixedControl`; nothing in it depends on what the
  frames mean.
- **Cost.** `Shared50RecursiveBudget.budget (d+1) V = node·V + s·budget d (V/W)` and
  `Swap.Recurrence.power_width_bound`; `BinaryInterchangeBudget.uniform_bound` is the interface
  the cost chain consumes. Stage 2 uses `Layer.VariableRecurrence.variable_closed` plus a stopped
  variant.

`exists_prime_shear` does not give the exchange-frame lemma. It realizes the shear
`H ← H + A D`. A partial swap `D_U` factors through shears only with the within-field
involution `1 − 2U`, which is not lower triangular.

## 4. Exchange-frame edges

For an idempotent `U`, `D_U(h, d) = ((1 − U)h + Ud, Uh + (1 − U)d)`. For commuting idempotents,
`D_A D_B = D_{A+B−2AB}`; for `A ≤ B` (`AB = BA = A`) this is `D_{B−A}`, of rank `rank B − rank A`.

**Lemma (exchange program).** For idempotent `U` with `U = E₁ Π E₂`, the program
`[transformH E₁⁻¹, transformD E₂] ++ cross K ++ [interchange i j | (i,j) ∈ L] ++ cross (−K) ++
[transformH E₁, transformD E₂⁻¹]` runs as `D_U`, with exactly `L.length = rank U` interchanges.
Here `M = E₂E₁`, `P_E = ΠΠᵀ`, `P_F = ΠᵀΠ` and
`K = M P_E − P_F M + P_F M P_E − Πᵀ`; `cross K` is `D ← D + K H`, compiled to unit scalings and
`addToD`.

*Proof.* In the coordinates `(E₁⁻¹h, E₂d)` the map is `g = 1 + C R` with `C = [Π; −MΠ]`,
`R = [−M, 1]`. Idempotency of `U` is `ΠMΠ = Π`, that is `FᵀME = 1` for the pivot columns
`E`, `F` (`Π = EFᵀ`). With `S = [[1,0],[K,1]]`: `SC = [E; (K−M)E]Fᵀ` and `RS⁻¹ = [−M−K, 1]`, and
`K` satisfies `KE = ME − F`, `FᵀK = Eᵀ − FᵀM`. Hence `SgS⁻¹ = 1 + [E; −F][−Eᵀ, Fᵀ]`, the swap of
`h_i` with `d_j` on the pivot pairs. No characteristic assumption is used. ∎

This is the exchange-frame Bruhat statement in constructive form. The same identity holds over `ZMod (q^b)`
after one prime choice that avoids the denominators and the numerators of the scalings.

## 5. Plain frames

**Rank-one cost telescopes.** With rank-one children an edge `D_A → D_B` with `A ≤ B` costs
`rank B − rank A`. Along every wire the frames are nested, so its total is final rank minus initial
rank, plus the paid connectors. The intermediate frames therefore do not change `s`. Stage 1 can
use the simplest nested frames that the gates allow, in place of upstream's design-B frames
(deferred readouts, V-leaf frames, late-copy intersections, the flag `F_j`).

**The choice.** Readouts at frame `0`, at the start of the word. Sources (`slot += x_S`) at the
line `t_S`. The add and copy of node `n` at `span(n) = Σ_{S ∈ supp n} ℚ t_S`, recursively
`span(a) ⊔ span(b)`. Root reads at the root hyperplanes `t_T^⊥` and `U_c`. Centre scatters
through a zero temporary. Idempotents are the `G`-orthogonal projectors, `G = I − J/9`.

**Nondegeneracy is a theorem.** Every support lies in a star `star(c)` (the triples through one
point `c`): supports grow along parents, every node is below a root, and the root supports lie in
`star(c)`. For `S, S' ∋ c`, `G(t_S, t_S') = |S ∩ S'| − 1 = ⟨e_p, e_p'⟩` with `p = S ∖ c`, so on
`span(star c) = U_c` the form is the Euclidean form of the pair vectors `e_p ∈ ℚ^{[h]∖c}`. A
relation `Σ a_p e_p = 0` has `Σ a_p = 0` (count each coordinate twice), so `e_c ∉ U_c` and `G` is
positive definite on `U_c`, hence on every `span(n)`. No per-frame computation is needed.

**Links by pair graphs.** For supports in `star(c)`, `span(n) ≤ span(t)` iff every pair edge of
`n` lies in the span of the unsigned incidence vectors of `t`'s pair graph: both ends in one
component, and on opposite sides if that component is bipartite. 37579 of the 38741 links have
`supp(n) ⊆ supp(t)`; the other 1162 carry a spanning forest and a bipartition or odd-cycle
witness.

**What has to be checked.**
- DAG chains: free (`span(a) ≤ span(a) ⊔ span(b)`).
- Root inclusions: `supp(n) ⊆ {S : |S ∩ T| = 1}` and `supp(n) ⊆ star(c)`, as bitsets.
- Links: support inclusion, or the pair-graph witness.

All checks pass, by computation (`plain.py`, `graphlink.py`).

**Same `s`.** The compiled plain word has `R = 28866`, 91137 ops (62271 adds, 27095 copies,
1771 sources), 555403 start-readout XORs and 10626 root reads. It passes the complete F2 shear on
all 32408 basis vectors (`plainword.py`). Its two-stage histogram has `Wm − s = 1344189`
exactly, so stage 1 has the same `s` and the same `a_b` (`plainhist.py`).

**Stage 2 with plain frames.** The whole-projector moment of the plain histogram gives
`a* = 9.700·10⁻⁵`. Design-B gives `1.2410·10⁻⁴`, a 28% larger saving, by moving rank into larger
blocks: the deferred readout frames `σ_u` enlarge the exteriors. Design-B is a later upgrade with
its own frame certificates (11565 readout and 11374 V-leaf bases, about 15 MB of integer data,
plus exact dimensions of `M_n = span(n) + (U_n ∩ F_j)`).

## 6. The local word: scalar proof

The word is `OPS' ; RR ; OPS'⁻¹ ; OPS ; RR ; OPS⁻¹` (`Local/Word.lean`), where:
- `OPS` is the compiled operation list as XOR gates: source gates `slot += x_S`, additions
  `a[piv] += a[oth]`, and copies;
- `OPS'` is `OPS` without the source gates;
- `RR` adds each root's slot into the targets of the root.

The first pass runs at frame 0, so it costs no edges.

Proof structure:
1. Compiler (`Local/Compile.lean`, `compile_correct`): for every valid DAG, from zero side slots,
   each root's read slot holds the root's value. Validity: arguments precede their node, a link
   names a later use of the same operand, distinct donors serve distinct uses, every node has a
   free use.
2. Word (`word_run`): on arbitrary contents, the first three parts add the side slots' garbage
   into the targets and restore the side slots; the last three add the same garbage and the root
   values. Over `𝔽₂` the garbage cancels: `y_T += Σ_j count(T, targets j) · val(root j)`, with
   sources and side slots unchanged.
3. Checks (`Local/Kernel.lean`, `Local/Checks/*`, `Local/Witness.lean`): every record passes its
   local kernel check, which gives `dag_valid` and `supp_add` (an addition's support is the
   disjoint union of its arguments' supports).
4. Scalar (`Local/Scalar.lean`): the leaf triples increase lexicographically, so they are
   distinct, and `val_eq` sums each node over its support. The output root `(c, T)` has the
   triples meeting `T` exactly in `c` and the centre of `c` has the triples through `c`. The
   triple identity `Σ_{c∈T}[c ∈ S, S∩T = {c}] + Σ_{c∈T}[c ∈ S] ≡ [S = T] (mod 2)`
   (`Local/Triples.lean`) then gives `word_run_target`: `y_t += x_t` for every leaf `t`.

Result: `y += x`, `x` unchanged, side slots restored, on arbitrary dirty contents, on the
standard axioms. The reflected word (time reversed, banks exchanged) is `x += y` by the same
theorem with the register kinds exchanged.

## 7. The global node

Files: `Global/FrameMachine`, `Auto`, `Lift`, `Map`, `Stage`, `StageFrames`, `Node`,
`NodeFrames`, `NodeRun`, `NodeCost`, `Instance`.

**Wires.** Contract roles: the data `X S T` and `Y S T` for triples `S`, `T` (`2N` roles) and
the side slots of the `2v` invocations (`2vR`, `R = 28866`, `slot_count`). Temporaries: one per
stage, invocation and centre, one per data pair, and one unused wire (3217908 in all). Each
temporary is used once. A zero stream is valid in every frame, so each temporary starts in the
frame its first gate needs, and no relabel or reset is needed.

**Framed steps** (`FrameMachine`). A wire in frame `U` stores its logical stream read through
`D_U` mod `p^b`. Moves between nested frames are the exchange programs of their difference; XOR
gates act on wires in one common frame. The physical run is the logical run of the gates,
encoded in the final frames (`run_phys`). Aligned lists (`Auto`) insert the moves before each
gate. They are valid when each wire's frames form a chain of comparable frames (`ChainOk`).

**Stages** (`Stage`, `StageFrames`).
- Stage one, invocation `T`: the doubled local word with frames `K ⊗ Q_T` (`lift1`). Its centre
  reads go through temporaries: copy at the star frame, move to `0`, scatter.
- Stage two, invocation `S`: the blocks of stage one in reverse order with complemented frames,
  each centre block in its own order, lifted to `(1 − P_S) ⊗ 1 + P_S ⊗ K` (`lift2`), with the
  banks exchanged.
- Each stage adds every source into its target (`stage1_run`, `stage2_run`). Along every local
  register the frames increase (`chain1_aux`, `chain1_x`, `chain1_y`), and stage two sees them
  reversed and complemented (`fseq2_reg`).

**Gauges.** `X S T` starts in `U = P_S ⊗ Q_T`, the frame of its source gate. After the
correction (`ct += X` at frame `1`, then `Y += ct` at frame `1 − U`), `Y S T` ends in `1 − U`. On
scalars the node maps `(x, y) ↦ (y, x)` (`node_scalar`). With `D_U D_{1−U} = D_1`, every contract
role ends with its route's stream, address fields exchanged (`node_run`).

**Cost.** Interchanges are wire sums of move ranks (`edgeRanks_autoSteps`). The contract roles
climb monotone chains: `528` for `X` and `Y`, `529` for side slots, including the final sinks
to `1`. Centre temporaries make one move of rank at most `22`, and correction temporaries one
of rank `1`. In all, `calls ≤ s₀ = 57403754177` (`calls_node_le`).

**Instance.** `pr97₀ : BitNetwork` (`Instance`) takes `rankSum := calls control`. Branching
comes from `Branching97.branching` at `s₀`. Its run identity is `node_run`, moved to the
structure's decidable-equality instance by `run_inst`. `pr97` seals it with `irreducible_def`.
The machine runs it (`runs_pr97`), and its exponent is `Branching97.tau` (`pr97_tau`). All of
these rest on the standard axioms.

**Elaboration of the node.** The node's terms are closed and built from the compiled word. Lean
evaluates them, past 10 GB, whenever it checks a defeq between closed terms that differ
syntactically. That happens in the kernel's numeral reduction under `+` and `*`, after a `simp`
step by a definitional lemma, or after a rewrite whose instance unfolds an abbreviation such as
`V` or `Slot`. It also happens when `whnf` runs over `Valid` of the gate list. The files avoid
this in four ways:
- `allGates` and `sideWires` are `@[irreducible]`, with `allGates_def` and `sideWires_def`;
- proofs about the node use `rw` chains with lemmas stated on the node's own types (`card_V`,
  `card_Slot`);
- sums and counts go through generic lemmas over type variables (`calls_sinks`,
  `sum_costBoundOf`);
- the compiled schedule is used only through generic statements (`compile_chain`,
  `compile_root_nodes`).

## 8. Interface between the word side and the machine side

The structure `M8.BitNetwork` (`BitNetwork.lean`) contains:
- the contract roles `World` with `roleCount` and `roleEquiv : Fin roleCount ≃ World`, and the
  temporaries `Temp` with `tempCount` and `tempEquiv`;
- the width `m` with `2 ≤ m`, and the prime `q` (prime, odd);
- `control : List (Step (World ⊕ Temp) (FieldProgram m))`, with field programs over `ℚ`;
- the route `route : World → World`, an involution;
- the certificates:
  - `calls_exact : calls control = rankSum` (`rankSum` is `s`);
  - `legal` and `legal_mod b`: every field operation is legal over `ℚ` and after reduction mod
    `q^b`;
  - `xor_gate`: every gate is one XOR of two distinct streams;
  - `run_identity b`: on arbitrary contract-role streams and zero temporaries, role `i` ends with
    the stream of `route i`, its two address fields exchanged;
  - `tau` with `0 < tau < 1` and `branching : s / roleCount < m ^ tau`.

The machine side also needs `Runs N` (section 9): the shared prime, the coefficient bound and
`m ≤ roleCount`. The word side (sections 4–7) produces `M8.Global.pr97 : BitNetwork` and `Runs pr97`;
the machine side consumes any network that meets `Runs`. Shared50 is the existing instance in all
but name: its control is `Shared50FixedControl.control`.

## 9. The machine side

`M8/Machine/` is one generic copy of the recursive interchange machine over a `BitNetwork`: the
Shared50 machine (`Shared50Recursive*` and the arbitrary-width wrapper up to
`BinaryInterchangeBudget`) with the network as a parameter.

**Parameter.** `class Net` (`Net.lean`) carries the network and `Supports net`
(`Network.lean`):
- `prime_eq`: the network's prime is `Shared50ModularControl.prime`, the prime of the machine
  alphabet;
- `coeff_supported`: every operation of every edge program has coefficients that the coefficient
  stages accept (`Coordinates.CoeffSupported`). That is a coefficient of Shared50's schedules, or
  any coefficient with numerator and denominator at most
  `Networks.coefficientBound = 2^(2^(2^16))`;
- `width_le_roleCount`: `m ≤ roleCount`, so the row divisor `roleCount^k` of the wrapper
  dominates the width `m^k`.

`Runs net` has the same fields, with every coefficient within the bound (`coeff_bound`), and it
gives `Supports net` (`Runs.supports`). The word side proves `Runs pr97`
(`Global/EdgePrograms`). Shared50 meets only `Supports`: its factorizations are
`Classical.choose` witnesses with no height bound, and its coefficients are accepted because they
occur in its schedules.

**Shared50 as a network.** `Machine/Shared50Network` makes Shared50's fixed control a
`BitNetwork` on its World roles with no temporaries (`network`, sealed with `irreducible_def`)
and `net : Net`:
- the control's run is Shared50's run (`run_step`), so `run_identity` comes from
  `Shared50FixedControl.run_identity`;
- the certificates are Shared50's: calls `s`, legal programs over `ℚ` and mod every `q^b`, XOR
  gates, and branching at `Shared50Parameters.tau`.

Definitions use `variable [Net]` and refer to the network like a global constant. Nothing
evaluates the prime or the bound: comparisons are on exponents, and the prime is a
`Classical.choose` witness.

**Shared prime.** `Shared50ModularControl.prime` is chosen beyond `coefficientBound` and every
Shared50 denominator, and `Shared50AffineCoefficients.Occurs` admits every coefficient within the
bound, so one alphabet serves Shared50 and every network that meets `Runs`. With the `Or.inl`
witnesses in `Shared50NonrecursiveCoordinates`, these are the only edits to existing files;
`Networks/CoefficientBound` is new.

**Temporaries.** The wires are the contract roles and the temporaries (`Wire = World ⊕ Temp`),
each on its own tape, plus one input/output tape. The split and the merge use the contract roles
only. After the split `tempInit` fills every temporary with the zero bit, and after the last piece
`tempClear` blanks them (`NodeLayout`, `NodeData.init_encoded`, `NodeData.clear_network`).
Resets (a fill with the zero bit) are pieces.

**Results** (standard axioms):
- `Induction.contract`: at every depth, the graph started on a canonical source bank returns the
  full H/D transpose to the decoded caller within `Budget.budget k depth V`, with every stack and
  spectator restored;
- `RootExecution.halts_power_bound`: the root program halts within `C·V·width^τ`, `τ = N.tau`;
- `BinaryInterchangeRun.runs` and `BinaryInterchangeRun.uniform_bound`: the width-selecting
  rectangular interchange from five caller headers costs at most `C·V·max(1,h,d)^τ`, the
  interface the cost chain consumes.

The node coefficient is `node k = entry + exit + Σ overhead + tempInit + tempClear + 137 + k`, and
`budget (d+1) V = node·V + s·budget d (V/roleCount)`. For PR97, `m = 529`,
`roleCount = 108516254` and `τ₉₇ = 1 − 3734/10⁹`; `Runs pr97` comes from the word side. Switching
`Parameters.tau` and retuning go through main, since they touch the Cost chain.

**Proof conventions.** `width`, `roleCount` and the tape counts are symbolic. Width facts come
from `two_le_width`, `width_pos`, `one_lt_width`, `two_le_roleCount` and `width_le_roleCount`; no
`decide` touches `width` or its powers. Where a failing tactic alternative would unfold a symbolic
tape count, the proofs list their cases directly or simplify slot values first.

**Module map.** Kenny's module, then its M8 counterpart under `M8/Machine/`.

| Kenny's module | M8 module |
| --- | --- |
| `Networks/Shared50FixedControl`, `Shared50TapeGlobal` | `BitNetwork.control`, `Net` |
| `Shared50NonrecursiveCoordinates` | `Coordinates` |
| `Shared50CleanSegments` | `Segments` |
| `Shared50PieceSchedule`, `Shared50OrderedPieces` | `Pieces` |
| `Shared50PieceSemantics` | `Semantics` |
| `RecursiveXorRoleBank` | `FillRoleBank` |
| `RecursiveMixedSchedule`, `RecursiveMixedInitialized`, `RecursiveMixedClean`, `RecursiveMixedRoleBank` | `RoleOps`, `RoleOpsInitialized`, `RoleOpsClean`, `RoleOpsBank` |
| `Shared50NodeSegments`, `Shared50NodeGates` | `NodePieces` |
| `Shared50NodePieceTransport` | `NodeTransport` |
| `Shared50RecursiveNodeLayout` | `NodeLayout` |
| `Shared50RecursiveNodeSemantics`, `Shared50RecursiveNodeBinary`, `Shared50RecursiveNodePieces` | `NodeData` |
| `Shared50RecursiveChildPermutation` (`child`, `child_spec`) | `ChildPermutation` |
| `Shared50RecursiveSegments`, `Shared50RecursiveGates`, `Shared50RecursiveBankNodes`, `Shared50RecursiveCallLayout` | `BankNodes` |
| `Shared50RecursiveX`, for `X` = `Control`, `Implementation`, `Execution`, `BlockExecution`, `ReturnExecution`, `BaseExecution`, `Root`, `CallSemantics`, `CallRecovery`, `BinaryInvariant`, `PieceExecution`, `NodeBoundary`, `Depth`, `NodeExecution`, `CallReady`, `CallInductionBridge`, `Induction`, `BudgetBound`, `RootExecution` | `X` |
| `Shared50RecursiveBudget`, `Shared50RecursiveBudgetAssembly` | `Budget` |
| `Shared50RecursiveInductionBase`, `Shared50RecursiveBasePermutation` (`source_roles_updated`) | `InductionBase` |
| `ArbitraryWidthPieces` (`slice_shape`, `piece_shape`, `piece_view`) | `ArbitraryWidthPieces` |
| the 76 modules of the arbitrary-width wrapper that depend on `W = 125000` or on the Shared50 root, `ArbitraryWidthSchedule` through `BinaryInterchangeRun` and `BinaryInterchangeBudget` | the same names |

`Network`, `Net` and `BankFacts` are new. Used unchanged: the generic `Recursive*` layer,
`Shared50RecursiveBank`, `Shared50RecursiveBankReturn`, `Shared50RecursiveNodeRows`,
`Shared50RecursiveNodeTranspose`, `encoded` from `Shared50RecursiveNodeSemantics`, `array` and
`toChild` from `Shared50RecursiveChildPermutation`, `array_transpose` from
`Shared50RecursiveBasePermutation`, the generic part of `ArbitraryWidthPieces`, and the 43
arbitrary-width modules independent of `W` and the root (for example `ArbitraryWidthHighLayout`,
the `RadixHighBlockJoin*` chain and the `BinaryAdjacentWidth*Shared` banks). At integration the
Shared50-specific modules on the left become candidates for retirement.

## 10. Certificate engineering

- **Kernel cost model** (one thread, guarded checker):
  - records are structures and the checks apply the `Nat` functions themselves (`Nat.add`,
    `Nat.land`, …) to their fields, which the kernel evaluates on literals directly; instance
    arithmetic and `let`-bound fields cost about 0.5–1 ms per operation;
  - a lookup in the static tree of 65536 records (depth 16, through `Tree.rec`) costs about
    0.7 ms;
  - pair sets are 529-bit masks in the layout `pb u w = 23u + w`; star and touch masks are
    loops of 23 steps.
- **Consequence.** No state is replayed in the kernel. Every certificate is a list of local
  checks over static data, with a few lookups per item.
- **Data** (`Local/Data/*`, about 11 MB of source, emitted by `scripts/pr97/emit_lean.py` from
  the output of `scripts/pr97/generate.py`; `scripts/pr97/mirror.py` reruns the checks in
  Python):
  - the DAG in compile order: 64042 nodes, each with arguments, link, donors, a free use and a
    support (a leaf triple, two points with a mask of third points, or a point with a pair
    mask);
  - 5336 roots: 5313 outputs and 23 centres; 38741 links, 1162 of them with pair-graph paths.
- **Checks.** Sixteen node chunks of 4096 records and the root check, each `decide +kernel`,
  each 4–11 s and at most 2.3 GB; about 2.5 min in all.
- **Proof style.** Everything else is a general lemma; no literal word list is ever unfolded.

## 11. Stages and estimates (conservative, one agent per side)

| stage | content | estimate |
| --- | --- | --- |
| 1a | exchange-frame algebra; the exchange program (section 4) over ℚ and `ZMod (q^b)`; nested-edge cost; tensor (Kronecker) lifts and ranks | 3–5 weeks |
| 1b | generator, witness data, DAG and slot-bookkeeping kernel checks; scalar theorem of the local word and its reflection (section 6) | 6–10 weeks |
| 1c | plain frames: spans, positive definiteness on stars, pair-graph links, roots; per-wire nesting; the local cost | 4–7 weeks |
| 1d | the global node (section 7): World, stages, gauges, connectors, temporaries, correction; routed transpose; `calls = s` | 8–12 weeks |
| 1e | machine side (section 9): generic recursive machine over `BitNetwork`, temporaries, PR97 instance, `uniform_bound` at `τ₉₇` | 8–12 weeks |
| 1f | switch `Parameters.tau` and retune with T16 (through main) | 1–2 weeks |
| 2a | generic common basis (nonvanishing-polynomial lemma), exact plain-frame dimensions, whole-projector histogram and its moment | 5–8 weeks |
| 2b | opposite-bank factorization with reversal over atom rings `(ℤ/q^w)^f`, one reversed child per increment | 4–6 weeks |
| 2c | atom adapters `O(Vn)`, reversed recursive family, stopped recurrence, outer wrapper `F L F`, width selection `w = e^θ`; machine changes for variable-rank children | 10–16 weeks |
| 3 | optional: design-B frames for the extra 28% | 6–10 weeks |

**Totals.**
- Stage 1: 30–48 weeks of work. With the word side (1b–1d) and the machine side (1a, 1e) in
  parallel, 5–8 months calendar.
- Stage 2: another 19–30 weeks.
- T16 is already in the layer chain (upstream `2e11a91c`, `κ = 25222/2^46`), so the bit side
  binds.

## 12. Risks

- **Kernel throughput.** The local checks total about `2·10⁵` lookups (section 10). The
  remaining exposure is the global node (1d): its lemmas must stay general in the invocation
  index, since `W` is about `10⁸`.
- **Machine temporaries.** These are settled. The machine zero-fills and clears its temporaries
  (section 9), so PR97's 3,217,908 temporaries add only constants to the node coefficient. The
  branching ratio and the row divisor use contract roles only.
- **Stage 2.** The stopped recurrence with a linear toll and the reversed atom family are new to
  the machine; their estimates are the least certain.

## 13. Stage 2: the stopped opposite-bank supplier

The construction is icekylinx's stopped product-ring interchange (`notes/stopped-product-*.tex`
in the research tree). It was written for the retained h23 producer; stage 2 applies it to
PR97's plain-frame node (section 5).

**Atom model.**
- One invocation fixes the prime `q` and an atom width `w`.
- A field of `n` atoms is `(ℤ/q^w)^n`. `C_n` reverses the atoms and keeps their digits.
- The recursive target is the reversed interchange `F_n(H, D) = (C_n D, C_n H)` on two
  contiguous chunks with complete spectators.
- The machine's descriptor already has this shape: width `n`, digit width `w`. A node of
  `n = m f` atoms has `m` sub-fields of `f` atoms. Every rational scalar acts on each atom
  separately, so it commutes with reversal.
- Lean: a reversal of `RecursiveScalarCoordinates.Address` with its index lemma, and the
  reversed array as the counterpart of `Shared50RecursiveNodeRows.transpose`.

**Frame convention.**
- Conjugating every frame, gauge and endpoint of the node by `diag(I, C_m)` turns its partial
  swap into
  `D'_P = [[(I−P)⊗I_f, (P C_m)⊗C_f], [(C_m P)⊗C_f, C_m(I−P)C_m⊗I_f]]`.
- The common-frame identities of `FramedCircuit` are invariant under one common conjugation. So
  the word side's node theorem holds with endpoint `F_n`, through one conjugation lemma for
  framed runs.

**Generic basis** (`GenericBasis.lean`).
- `exists_generic_basis_of_idempotent`: for a finite family of idempotents `P_j`, one basis `g`
  with natural entries at most `degreeBound m (rank ∘ P)` makes every `g P_j g⁻¹` generic.
  Generic means nonzero leading principal minors of sizes `1..rank P_j`, and
  `degreeBound = m + Σ_j Σ_{i ≤ r_j} i (m + 1)`.
- Proof:
  1. Each minor of `X P adj(X)`, for the matrix of variables `X`, has total degree at most
     `i (m + 1)` (`totalDegree_minorPoly`).
  2. The minor is nonzero, because an adapted basis of range and kernel makes `P` generic
     (`exists_generic_of_idempotent`) and `g P adj(g) = det g • g P g⁻¹` (`minor_adjugate`).
  3. Mathlib's combinatorial Nullstellensatz then gives a common non-root with entries bounded by
     the total degree (`exists_generic_basis`).
- The bound is explicit because a basis from `Classical.choose` would have no height, and the
  prime must avoid every numerator and denominator. Shared50's factorizations are such
  unbounded choices, so the machine accepts Shared50's coefficients by occurrence
  (`Coordinates.CoeffSupported`).
- After elimination (`Height`, `FE N n α ≤ (16N⁵)^n (α+1)`), every coefficient stays below
  `coefficientBound`.

**K-factorization: one reversed child per projector** (`ReversedExchange.lean`,
`ReversedPivots.lean`).
- `revExchange P = transform 1 C ∘ D_P ∘ transform 1 C` is the partial swap in the frame
  `diag(1, C)`. `revPivots m r` are the pivots `(k, m-1-k)` for `k < r`.
- `revExchange_factor`: if `P C = L Π_r R` with lower-triangular invertible `L` and `R`, then
  `revExchange P = transform L R⁻¹ ∘ cross(−K) ∘ swaps(revPivots) ∘ cross K ∘ transform L⁻¹ R`,
  with `K = kMat Π_r (R C L)`. This is section 4's `exchange_factor` at `E₂ = R C`.
- `exists_rev_factor`: in a generic basis, every lower-triangular factorization of `P C`
  (`Swap.LowerTriangular.factorization`) has exactly the reversed pivots.
  - The factors keep the rank of every northeast rectangle, and that rank is the number of pivots
    inside it (`rank_mask`).
  - Genericity makes these ranks `min(i, m − j, r)` (`rank_mask_rev`).
  - The four counts around a cell count its pivots (`cell_count`), which forces the pivots
    (`pivots_forced`).
- `revExchange_generic` combines the two: a generic projector's reversed exchange has the `r`
  interchanges of one reversed child `F_r`.
- `revExchange_atoms` lifts this to `f` atoms per sub-field. The reversal of all atoms is
  `C_m ⊗ C_f`, the projector acts as `P ⊗ 1`, and the factors are `L ⊗ 1` and `R ⊗ 1`. The
  `r f` pivots `atomPivots` pair head atom `(k, x)` with tail atom `(m-1-k, f-1-x)`: one reversed
  child `F_{rf}` on the first `r f` head atoms and the last `r f` tail atoms.
- Still to do: lower-triangularity of the lifted factors in the atom order, which the streaming
  adapters need, and the machine side.

**Atom adapters.**
- Chosen design (2026-10-20): a coordinate carries its `f` atoms, with atomwise arithmetic in
  `S = (ℤ/q^w)^f`, and the atom reversal is a ring involution `σ` of `S`. The field programs and
  the control stay the network's, at `m` coordinates, for every `f`. `TwistedExchange.lean`:
  conjugating the tail by `σ` keeps fixed transformations, twists the cross shear to
  `d ← d + K σ(h)` and every interchange to `h_i ← σ(d_j)`, `d_j ← σ(h_i)`; so the reversed
  exchange over `S` is `twisted_rev_factor`. `TwistedProgram.lean`: the twisted semantics
  `twRun` of the unchanged field operations is the conjugated ordinary run (`twRun_eq`) when the
  coefficients are scalars, and `revOps_twRun` runs the reversed exchange program. Remaining:
  the coordinate stages with atomwise carries and a reversed head read.
- Each lower-triangular factor expands to unit scalings and additions from earlier to later
  fields.
- A cross-bank update `D_{i,t} += k H_{j,f−1−t}` reads an earlier head atom. So the
  ordered-affine streaming primitive applies per atom: `O(V)` per pass, `O(f)` passes per fixed
  matrix, `O(V n)` per node.
- The segment compiler (`Segments`, `Coordinates`) runs on atom-indexed coordinates.
- The node toll is linear in `n`, which is the main change to the budget.

**Reversed recursive family and remainders.**
- For `n = m f + δ` with `δ < m`:
  - the first `δ` head atoms pair with the last `δ` tail atoms through `δ` ordinary width-`w`
    leaf interchanges (stage 1's supplier);
  - the two contiguous `m f`-atom intervals take the node construction;
  - for `n < m`, at most `m` leaf calls complete `F_n`.
- The machine changes:
  - variable-rank children, of width `r⌊n/m⌋` atoms;
  - a node at every `n`, so `Depth.Shape` counts atoms with no power-of-`m` condition;
  - remainder pieces;
  - the call piece becomes a block call of rank `r`.

**Stopped recurrence with linear toll.**
- With `n_r` the rank histogram on `W` contract roles, for `n ≥ m`:
  `T(n,w) ≤ Σ_r (n_r/W) T(r⌊n/m⌋, w) + C n + C w^{1−a_leaf}`. For `n < m`:
  `T(n,w) ≤ C w^{1−a_leaf}`.
- The two moment gaps `μ_1 = s/(Wm) < 1` and `μ_{τ*} = Σ_r (n_r/W)(r/m)^{τ*} < 1` give
  `T(n,w) ≤ A n + B n^{τ*} w^{1−a_leaf}` by strong induction.
- `StoppedRecurrence.stopped_closed` proves this for any node type. Children have sizes at most
  `(r/m) n`, the moments are `Σ w (r/m) ≤ q₁ < 1` and `0 ≤ Σ w (r/m)^τ ≤ q_τ < 1`, and every node
  has size at least one. The bound is `cost ≤ C/(1−q₁) n + C/(1−q_τ) n^τ L`.
- The moment certificate is rational, with exp/log enclosures as in `Global/Branching97`
  (`Stage2Moments.lean`, data `Stage2Histogram.lean` from `scripts/pr97/stage2hist.py` and
  `stage2cert.py`). The whole-projector histogram has 23 ranks over 754171495 moves and rank mass
  `s₀`; `linear_moment` gives `q₁ = 1409269/1409302` and `tau_moment` gives `q_τ = 1 − 2/10⁸` at
  `τ* = 1 − 969/10⁷`, against `a* ≈ 9.69991·10⁻⁵`. Linking the histogram to the node's moves
  remains, with the reversed family.

**`F L F` wrapper and width selection.**
- `F_n L F_n = (H+D, D)` for `L(H, D) = (H, D+H)`. So `D ← D−H; F_n; D ← D+H; F_n; D ← H−D` is
  the ordinary interchange `(H, D) ↦ (D, H)` (`ReversedExchange.flf_wrapper`, for any involution
  `C`), at `O(V n)` outside the recursion.
- For radix width `e`: `θ = 1/1000`, `w = ⌈e^θ⌉`, `n = ⌊e/w⌋`. The residual digits use the leaf
  interchange.
- Cost: `O(V[e^{1−θ} + e^{(1−θ)(1−a*)+θ(1−a_leaf)}])`, so `a_b = (1−θ)a* + θ·a_leaf`.
  Since `θ > a_b`, the adapter term is of lower order.
- For the stage-2 supplier this replaces the power-of-`m` arbitrary-width wrapper (section 9).
  The binary range padding and the `BinaryInterchangeRun` seam stay. The stage-2 switch is again
  one seam instance (`scripts/s6/apply_seam.py`).

**Numbers.** With plain frames, `a* = 9.700·10⁻⁵` (section 5) and `a_leaf = 3.734·10⁻⁶`
(stage 1). So `a_b ≈ 9.69·10⁻⁵` and `κ ≈ ε c a_b ≈ 2^-14.5` (section 1).

**What stage 1 supplies.**
- The algebra pattern of `Exchange` and `ExchangeProgram`.
- The coefficient heights of `Height` and `ExchangeBound`.
- The node of the M8 machine: split, temporaries, schedule, merge and induction. `Budget` and
  `BudgetBound` give way to the stopped recurrence.
- The supplier seam.

Estimates are in section 11 (2a 5–8, 2b 4–6, 2c 10–16 weeks).

## 14. The supplier seam and the retune

**Seam.** The cost chain uses the interchanges under Kenny's names. `scripts/s6/apply_seam.py`
makes those names a seam, and it is idempotent, so it can be rerun after an upstream merge:
- Shared50's implementations live in `Machine/Shared50BinaryRadixEqualShared`,
  `Shared50BinaryInterchangeRun` and `Shared50BinaryInterchangeBudget`.
- The Shared50 supplier modules (`scripts/s6/shared50_supplier_modules.txt`) use Shared50's own
  exponent `Shared50Parameters.tau`, and `Shared50RecursiveBudgetBound.tau_range`.
- The seam modules at the old paths (`Machine/BinaryRadixEqualShared`, `BinaryInterchangeRun`,
  `BinaryInterchangeBudget`) do three things:
  - re-export the chosen supplier (`export`, which `unfold` and `simp` see through);
  - state both uniform bounds at `Parameters.tau`, through `supplier_tau`;
  - keep `Shared50RecursiveBudgetBound.exponent_range` as the range of `Parameters.tau`.

`Parameters.tau` is now the exponent of the cost chain, and no consumer was edited. The choice of
supplier is kept in `scripts/s6/supplier.txt`:
- `m8` re-exports the M8 machine at Shared50 as a bit network (`Machine/Shared50Network`),
  under a sealed instance;
- `pr97`, the current choice, re-exports the M8 machine at the PR97 node (`Global/Instance`),
  through the sealed `Global.pr97` and its lemmas `runs_pr97` and `pr97_tau` only.

At `pr97` the default build, the `Theorem` target and the seven checks (`CompletedProofCheck`,
`CompactControlCheck`, `AxiomAudit`, `MathlibTM2Check`, `FastPathCheck`, `CRTControlCheck`,
`CRTGapCheck`) are green, with κ = 111364923/2⁴⁶. `mulInTime` and `DFT.dftInTime` use only
`propext`, `Classical.choice` and `Quot.sound`. `Host.swapMachine` and the gadget programs unfold
to M8's programs. Kenny's Shared50 tail and root, and with them the `shared50` choice, were
retired ([record](../../../docs/retired-shared50-machine.md)).

**The PR97 choice** (`apply_seam.py --supplier=pr97`, then `scripts/s6/retune.py`) sets:
- the seam instance and `supplier_tau`, from `Global/Branching97`;
- `Parameters.tau := 1 − 3734039/10¹²`;
- `CompactInterimParameters` (λ, λ', κ);
- the value of `Cost.Total.tot_kappa_eq`;
- the statement of `Theorem.lean`;
- the κ literals of `Fast/CompactFinalR`, `Fast/CompactMainDispatch`, `DFT/DFTCheck` and
  `CompletedProofCheck.lean`.

**Retune.** These numbers assume T16 as in master, `ε = 31/64`, `c = 7/8` and `δ = 1/128`.
- `τ₉₇ = 1 − 3734039/10¹²`. The exact threshold for `s/W < 529^τ` is
  `1 − τ < 3.73403992·10⁻⁶`. The certificate is `Global/Branching97.branching`: a 26-term
  exponential series for `log 529`, the cubic bound `Real.exp_bound'`, and rationals.
- `λ = 1 − 35/10⁷` and `λ' = 1 − 33/10⁷`. Then `τ < λ`, `999/1000 < λ`, `λ < λ'`, `1 − c < λ'`
  and `λ' < 1`.
- `κ₉₇ = 111364923/2⁴⁶ ≈ 1.5826·10⁻⁶ ≈ 2^-19.27`, against master's `88279/2⁴⁶ ≈ 2^-29.57`.

| margin | value | slack over κ |
| --- | --- | --- |
| layout `εc(1−τ)` (binding) | 1.582591e-6 | 6.9e-15 |
| layers `ε(1−λ')` | 1.598438e-6 | 1.6e-8 |
| CRT `(1−ε)(1−τ)` | 1.925364e-6 | 3.4e-7 |
| resampling `1/2 − δ − ε(1+2^-33)` | 7.8125e-3 | 7.8e-3 |
| direct `ε(1−c)` | 6.0547e-2 | 6.1e-2 |

The facts of the older path in the cone (`Cost/Total`) hold at `τ₉₇`. `tot_kappa_eq` becomes
`totKappa = 115755209/(10¹²·2³⁸)`.

