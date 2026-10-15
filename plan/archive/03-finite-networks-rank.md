# 3. Two finite networks with a rank saving (§3)

**Archived native-machine route.** Open entries here are historical targets,
not gaps in the completed Mathlib proof. See the [archived roadmap](native-roadmap.md)
and the [current plan](../../PLAN.md). This file is no longer regenerated.

Part of the [plan](../../PLAN.md). See [COMPONENTS.md](../../COMPONENTS.md) for what each file proves.

## How the proof goes

Section 3 builds a finite reversible linear network over the triple bank of a ground set of size 100 that exchanges two data banks while restoring arbitrary dirty scratch, and proves that this exchange costs strictly less projection rank than the trivial bound. The saving is what makes the recursive address interchange cheaper. The argument first fixes the exact scalar shear schedule, then attaches nested bilinear labels to every wire and telescopes projection ranks along the schedule, first for the baseline motif (h=25) and then for the optimized shared-point network (h=50), and finally realizes the optimized program physically and on tapes.

1. **Scalar shear and bank exchange.** An eight-step dirty-scratch cancellation schedule and a three-stage signed exchange give an exact bank identity for the complex and binary motif matrices (`Scalar`, `Circuit`, `CircuitRouting`, `CircuitTriples`, `CircuitBits`), lifted to framed and global circuits with per-invocation scratch (`FramedCircuit`, `GlobalCircuit`).
2. **Wire counts and label spaces.** Exact subset-intersection censuses give the triple, neighbor and role counts matching the manuscript totals (`NeighborCounts`, `Wires`); degree-one and tensor-cube bilinear label spaces are nondegenerate, and stage boundary labels and the binary coordinate bridge are exact isometries (`Labels`, `TensorLabels`, `TensorSubspace`, `StageLabels`).
3. **Grouped gates and binary residual units.** Sparse grouped motif gates are scheduled globally with local inverses and exchange (`GroupedCircuit`, `GroupedRouting`, `GlobalGrouped`, `GroupedFrames`); binary orthonormalization, diagonal phase/Walsh factorizations and neighbor residual bases supply the unit residual factors, with exact Gaussian-dyadic arithmetic and numerator bounds (`BinaryOrthonormal`, `BinaryPhase`, `MotifResiduals`, `GaussianPrecision`).
4. **Projection-rank trace and baseline saving.** Nested nondegenerate labels turn each edge into a projector-difference rank (`ProjectionRank`, `RankTrace`); attaching physical labels to every invocation and assembling the global trace gives a balanced loss bound (`GlobalLabels`, `GlobalRank`, `GlobalProjectionRank`), and the budget arithmetic yields the h=25 rank saving (`NetworkBudget`, `ComplexRank25`).
5. **Shared-point h=50 network.** A paired-exclusion recursion with globally interned common points yields a smaller scalar DAG; its correctness is proved by induction and its counts by kernel-checked certificates (`PairedCircuit`, `Paired49Certificate`, `Shared50Certificate`), and a reversible allocator compiles the DAG into framed forward and complementary-inverse scalar programs with zero label loss (`DAGAllocator`, `DAGFramedExecution`, `Shared50FiniteFramed`).
6. **Optimized global rank trace.** Local forward/opposite label histories, a Hall-selected stage-reuse matching and the two-bank parameter budget assemble into a global projection-rank trace meeting the improved rank budget (`Shared50InvocationRank`, `Shared50ReuseLabels`, `Shared50GlobalProjectionRank`).
7. **Optimized physical program and interchange.** The signed two-bank program executes the full rational address shear on arbitrary arrays (`Shared50GlobalShear`), reduces modulo one good prime at every radix (`Shared50ModularExecution`), and gives the full coordinate-group interchange with the improved budget (`Shared50FiniteInterchange`), together with the sparse dirty invocation and global scalar program (`Shared50SparseInvocation`, `Shared50GlobalCircuit`).
8. **Tape realization.** The Shared50 scalar XOR lists run on fixed role tapes with exact exchange, scratch restoration and linear stream-time bounds (`Shared50XorLists` and its tape modules), while the rational address-shear and phase interfaces connect the network to the tape-level transform; recursive calls and full network tape assembly remain open.

## Sub-problems

### Scalar shear and bank exchange circuits

An exact dirty-scratch shear schedule exchanges the two data banks over rational and binary motif matrices, lifted to framed global circuits.

- Math milestone: `IntegerMultBounds.Networks.GlobalCircuit.motif_program_run` — For the actual complex (rational) and binary motif matrices, the global three-stage circuit sends (X, Y, scratch) to (-Y, X, scratch) on every triple address, restoring every invocation scratch bank. Combines `GlobalCircuit.program_run`, `GlobalCircuit.complexProgram_run`, `GlobalCircuit.bitProgram_run`.
- Tape milestone: `IntegerMultBounds.Machine.CompactComplexRecursiveExecution.root_runs` — From the root bank, the fixed cyclic node table runs to halt with the full complex tensor transform installed and clean workspace, in total time bounded by the uniform recursive runtime (a constant times native volume times the certified stage factor).

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Scalar cancellation schedule and bank identity | `Scalar` | ✅ | ⬜ | Eight-step dirty scratch, signed exchange |
| Executable linear circuits | `Circuit`, `CircuitRouting` | ✅ | ⬜ | Instruction counts, not wire counts |
| Complex (rational) motif matrices | `CircuitTriples` | ✅ | ⬜ | Exact matrices; dyadic coefficient bounds in `GaussianCircuit` |
| Binary motif matrices over `ZMod 2` | `CircuitBits` | ✅ | ⬜ | Original motif; optimized h=50 replacement is separate |
| Framed circuit compilation | `FramedCircuit` | ✅ | ⬜ | Full finite-circuit common-frame identity, including spectators; exact operators |
| Global circuit with per-invocation scratch | `GlobalCircuit`, `GlobalCircuitBits` | ✅ | ⬜ | Complete three-coordinate scalar schedule and restoration; grouped topology separate |

### Wire counts and bilinear label spaces

Exact role and neighbor counts at ground size 100 and nondegenerate degree-one, tensor and stage label spaces.

- Math milestone: `IntegerMultBounds.Networks.StageLabels.census_and_labels` — At ground size 100 the triple, neighbor and role counts equal the manuscript totals, and the degree-one, tensor-cube and stage-boundary label spaces are nondegenerate with exact isometries. Combines `Wires.complex_role_card`, `Wires.complex_role_card_100`, `NeighborCounts.complex_neighbor_card_100`, `NeighborCounts.bit_neighbor_card_100`, `Labels.binary_nondegenerate`, `Labels.rational_nondegenerate`, `Labels.cube_nondegenerate`, `Labels.cube_line_decomposition`.
- Tape milestone: —

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Neighbor and wire counts | `NeighborCounts`, `Wires` | ✅ | — | Matches manuscript totals at ground size 100 |
| Degree-one label spaces | `Labels` | ✅ | — | Rational form nondegenerate for size ≠ 9 |
| Tensor-cube label spaces | `TensorLabels` | ✅ | — | Nondegeneracy, dimension, terminal line/complement decomposition |
| Embedded tensor subspaces | `TensorSubspace` | ✅ | — | Actual dimensions, nondegeneracy, orthogonality and sum/inclusion laws |
| Binary tensor coordinate bridge | `TensorCoordinates`, `LabelTransport` | ✅ | — | Actual isometry to h³ bits; transports labels, residuals and projections |
| Local nested gate labels | `MotifLabels` | ✅ | — | Actual tensor subspaces and unique central decrease; future factor and scratch endpoints included |
| Stage boundaries and terminal labels | `StageLabels` | ✅ | — | Actual isometries and all X/Y interstage and source/sink identities |

### Grouped gates and binary residual units

Sparse grouped motif gates with binary orthonormal, phase and residual factorizations and exact dyadic arithmetic bounds.

- Math milestone: `IntegerMultBounds.Networks.GroupedFrames.grouped_units_identity` — The compiled grouped network acts as the grouped scalar run through the label frames, every residual factor is a binary unit (orthonormal, phase and neighbor-residual factorizations), and all Gaussian-dyadic numerators meet the explicit bounds. Combines `GroupedFrames.network_identity`, `GroupedFrames.projection_rank_balance`, `BinaryOrthonormal.exists_orthonormal_basis`, `BinaryPhase.exists_phase_decomposition`, `NeighborResidual.binary_neighbor_residual`, `GlobalBinaryResiduals.network_residuals`, `GaussianPrecision.bounded_projection_edges`.
- Tape milestone: `IntegerMultBounds.Machine.CompactComplexRecursiveExecution.root_runs` — From the root bank, the fixed cyclic node table runs to halt with the full complex tensor transform installed and clean workspace, in total time bounded by the uniform recursive runtime (a constant times native volume times the certified stage factor).

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Sparse grouped motif gates | `GroupedCircuit` | ✅ | ⬜ | Exact support, eight-row semantics and framed refinement; full grouped exchange separate |
| Binary orthonormalization | `BinaryOrthonormal` | ✅ | — | Nonalternating nondegenerate forms; local witnesses and full global edge coverage proved |
| Local grouped inverse and exchange | `GroupedRouting` | ✅ | ⬜ | Bit/rational semantics and exact support transport; globally embedded by `GlobalGrouped` |
| Neighbor residuals and binary units | `NeighborResidual` | ✅ | — | Actual pair-complement dimension and bases; coordinate witnesses for tensor-line complements |
| Global grouped schedule | `GlobalGrouped` | ✅ | ⬜ | Physical scratch per invocation, middle inverse, sparse support transport and counts |
| Binary diagonal phase decomposition | `BinaryPhase` | ✅ | ⬜ | Rank-one residual and weight-mod-four factorization; Walsh conjugation separate |
| Binary one-column translation interface | `BinaryWalsh` | ✅ | ⬜ | Exact finite Walsh conjugation and residual-dimension kernel sequence |
| Full grouped frame compiler | `GroupedFrames` | ✅ | ⬜ | Scalar array identity and actual label history linked to projection-rank balance |
| Sparse physical motif incidences | `MotifSupport` | ✅ | — | Concrete nonzero coefficient/owner tests and central support |
| Binary multi-column interface | `BinaryColumns` | ✅ | ⬜ | Concrete slice operators and exact residual-dimension factor count; unit premise explicit |
| Local residual formulas and binary units | `MotifResiduals`, `BinaryMotifResiduals` | ✅ | — | Thirteen local comparisons plus future/sink at all three stages; physical sparse-history coverage in `GlobalBinaryResiduals` |
| Exact Gaussian-dyadic arithmetic | `GaussianDyadic`, `GaussianCircuit` | ✅ | ⬜ | Concrete motif coefficients, grouped updates, and both binary edge directions; denominator growth proved, numerator bounds in `GaussianPrecision`; tape costs open |
| Binary interface numerator bounds | `GaussianPrecision` | ✅ | ⬜ | Actual kernels and both projection-edge directions; explicit scale and integer numerator bounds |

### Projection-rank trace and h=25 saving

Nested labels along the global schedule telescope projection ranks to the baseline h=25 rank saving.

- Math milestone: `IntegerMultBounds.Networks.ComplexRank25.branching_bound` — The actual h=25 projection-rank sum divided by the role count is below 15625^sigma.
- Tape milestone: `IntegerMultBounds.Machine.CompactComplexRecursiveExecution.root_runs` — From the root bank, the fixed cyclic node table runs to halt with the full complex tensor transform installed and clean workspace, in total time bounded by the uniform recursive runtime (a constant times native volume times the certified stage factor).

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Projection-rank trace accounting | `RankTrace` | ✅ | — | Actual edge ranks telescope; global physical instantiation in `GlobalProjectionRank` |
| Physical local label histories and loss | `LabeledMotif` | ✅ | — | Forward/opposite sparse histories; comparable nondegenerate edges, loss ≤ central count × current dimension, including sinks |
| Rational negative-source correction | `SignedProjection` | ✅ | — | Exact extra source rank for arbitrary nested first label, including skipped vertices |
| Global physical label attachment | `GlobalLabels`, `GlobalLabelsNondegenerate` | ✅ | — | Exact schedule erasure, physical endpoints/stage boundaries, all vertex labels nondegenerate |
| Sparse skipped-edge binary units | `GlobalLabelsResiduals` | ✅ | — | Actual witnesses for xIn→full, yIn→yOut, bot→full, including future factor |
| Physical invocation rank loss | `GlobalRank` | ✅ | — | Actual embedded histories, comparable edges and loss bound; supports weaker input labels left by sparse predecessors |
| Full labeled trace assembly | `GlobalRankStages`, `ProjectionTrace`, `GlobalProjectionRank` | ✅ | ⬜ | Actual global comparable nondegenerate edges, loss bound and projection-rank balance, including terminal alignment |
| Terminal dimension and budget arithmetic | `NetworkBudget` | ✅ | — | Actual source/sink sums and h=25 role count; trace balance/loss premises discharged for h=25 by `ComplexRank25` |
| Orthogonal residual and projection rank | `ProjectionRank` | ✅ | — | Nested nondegenerate labels give actual projection-difference rank |
| Residual rank saving | `ComplexRank25`, `GlobalBinaryResiduals`, `ComplexPhaseBudget` | ✅ | — | Actual h=25 rank sum, full binary residual-factor coverage and uniform complex edge-factor budget proved; optimized h=50 rank bound is proved in Shared50GlobalShear |

### Shared-point h=50 network and compilation

The paired-exclusion shared-point DAG is correct, certified in size, and compiled into reversible framed scalar programs.

- Math milestone: `IntegerMultBounds.Networks.Shared50FiniteFramed.certified_compilation` — The certified Shared50 program writes the paired-exclusion support sum at every output, has at most 450,394 additions, 509,194 roles and 959,588 XOR updates, and compiles into forward and complementary-inverse framed scalar programs with exact frame identities. Combines `Shared50Finite.run_output`, `Shared50Certificate.addition_bound`, `Shared50Certificate.role_bound`, `Shared50Certificate.instruction_bound`, `Shared50FiniteFramed.forward_identity`, `Shared50FiniteFramed.inverse_identity`.
- Tape milestone: `IntegerMultBounds.Machine.Shared50TapeInvocation.compiled_hoare` — The certified Shared50 forward program and its complementary inverse run on fixed role tapes with exact paired-exclusion outputs and restored dirty scratch and heads, within the certified instruction count times (14L + 14·width + 34) steps. Combines `Shared50TapeInvocation.invocation_hoare`, `Shared50TapeInvocation.invocation_cost50`, `OneSourceCircuit.circuit_hoare`, `Shared50XorLists.finite`, `Shared50XorLists.inverse`, `Shared50Finite.run_output`, `Shared50Certificate.instruction_bound`.

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Improved h=50 bit network | `SharedPointMap`, `SharedPointKey`, `DisjointCircuit`, `DisjointPruning`, `DisjointBuilder`, `ReversibleFanout` | ✅ | ⬜ | Exact shared-point map, compressed-key interning, output-preserving active-node pruning, DAG primitives and reversible fanout proved; full literal paired-exclusion recursion and concrete 49-vertex input/output semantics proved; the independent checked local witness has 9,813 additions and 1,176 outputs; global sharing counts and actual finite scalar execution are now certified; full global rank, signed physical shear and modular execution are proved for the selected tau; literal tape costs remain open |
| Exclusion-circuit building blocks | `DisjointBalanced`, `DisjointExclusion`, `DisjointPaired` | ✅ | ⬜ | Literal balanced totals, shared prefix/suffix leave-one-out sums and weighted base-case query batches; exact support/value preservation and node upper bounds, not the optimized certificate count |
| Paired-exclusion reconstruction | `PairedPartition`, `PairGrouping` | ✅ | ⬜ | Literal pair grouping and recursive decrease; actual single/pair smart-add reconstruction with exact supports and node bounds; full recursive DAG assembly is proved in PairedBlockCorrect; optimized counts remain open |
| Literal paired recursion and query semantics | `PairedCircuit`, `PairedGraphSpec`, `PairedVectorCorrect`, `SupportInterpretation`, `PairedCoarseSupport`, `PairedCoarseCorrect`, `PairedQuerySupport`, `PairedCoarseQuery`, `PairedStripCorrect`, `PairedStripSupport`, `PairedCircuitCorrect`, `PairedReconstructionSupport`, `PairedReconstructionKeys`, `PairedBlockCorrect`, `PairedInitialGraph` | ✅ | ⬜ | Full literal recursion proved correct by strong induction; concrete 49-vertex graph has exact output sums and 1,176 inputs/outputs; active addition and global sharing counts remain separate |
| Interning invariants and certificate checking | `DisjointUnique`, `DuplicateBudget`, `SharedPointMatching`, `MaskDAG`, `MaskSignature`, `MaskUnique`, `PairMask` | ✅ | — | Full recursive support uniqueness; matching-based sharing bound and sound bitmask/signature/uniqueness checkers; concrete local counts, signatures and all 40,256 global duplicate witnesses kernel-checked |
| Checked local 49-vertex witness | `Paired49Certificate`, `Certificates/Paired49/*` | ✅ | ⬜ | All pair-exclusion outputs, 9,813 additions, unique supports, exact endpoint signatures and at most 10,989 compiled scalar roles; independent certificate, not a proof of generator trace equality |
| Actual common-point support family | `SharedPointLift`, `SharedPointFamily` | ✅ | — | Exact local-to-global core/union formulas and 490,650 actual local additions across fifty copies; matching structural hypotheses and all 40,256 genuine duplicate witnesses proved |
| Actual globally interned circuit | `DAGReplay`, `DAGReplayBudget`, `SharedPointOutputMap`, `SharedPointReplay`, `SharedPointExecution`, `SharedPointOutputIndex`, `Shared50Certificate`, `Shared50Finite`, `BoundedCircuit`, `DAGFiniteCompile` | ✅ | ⬜ | Actual fifty-copy DAG and finite scalar program with 58,800 exact outputs, at most 450,394 additions, 509,194 roles and 959,588 XOR updates; every finite-count premise discharged |
| Reversible DAG role allocation | `DAGAllocator`, `DAGAllocatorCount`, `DAGAllocatorFrontier`, `DAGConsumers`, `DAGAllocatorRun`, `DAGCompileCorrect`, `DAGAllocatorBudget`, `DAGValueTransfer`, `DAGInstructionCount` | ✅ | ⬜ | Actual compiler has exact role and scalar-instruction counts, valid bounded shared-pivot layouts, executable reverse and proved output values from actual input initialization; forward support-frame nesting is proved; reverse/global assembly is proved; tape execution remains open |
| Shared-point source spans | `SharedPointLabels` | ✅ | — | Actual rational spans are positive definite and nested; no nondegeneracy hypothesis |
| Actual forward shared-point frames | `FanoutFrames`, `DAGSupportTrace`, `SharedPointOutputLabels`, `Shared50Frames`, `DAGFramedExecution` | ✅ | ⬜ | Actual interleaved frame/scalar execution on arbitrary module states; increasing nondegenerate support labels and zero forward loss, with exact orthogonal output spans; complementary reverse middle frames proved separately; full motif and global rank assembly proved separately |
| Actual complementary inverse frames | `DAGComplementTrace`, `DAGComplementExecution` | ✅ | ⬜ | Exact reversed-complement labels, increasing edges, zero loss and arbitrary-module inverse execution; actual sinks, full invocation and global assembly proved separately |
| Shared circuit stage frames and physical attachments | `DAGSourceRoles`, `Shared50InitialLabels`, `Shared50OutputRoles`, `Shared50ComplementFrames`, `Shared50StageFrames`, `Shared50FiniteTrace` | ✅ | ⬜ | Actual finite forward/reverse middle traces lift into stage tensor labels with exact endpoints, nondegeneracy and zero loss; input/output physical owners and attachment inclusions are proved; whole invocation and global rank assembly proved separately |
| Actual finite physical middle schedules | `BoundedFramedCircuit`, `Shared50FiniteFramed`, `Shared50FiniteReverseTrace` | ✅ | ⬜ | Physical forward and complementary inverse instructions on the certified finite bank preserve exact scalar erasure and arbitrary-module frame identities; full invocation/global physical assembly remains separate |

### Optimized global rank trace

Local histories and stage-reuse matching assemble into a global trace meeting the improved h=50 rank budget.

- Math milestone: `IntegerMultBounds.Networks.Shared50GlobalProjectionRank.branching_bound` — The actual optimized global projection-rank sum plus the source correction, divided by W, is below m^tau.
- Tape milestone: —

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Complete optimized local label histories | `Shared50LabeledInvocation`, `Shared50InvocationRank`, `Shared50OppositeLabels`, `Shared50OppositeRank` | ✅ | ⬜ | Actual forward/opposite finite middle traces plus all sparse-block boundary alignments; exact endpoints, nested nondegenerate edges and loss exactly 2,500 each, including common-input scratch. Exact physical-wrapper linkage is proved; global rank assembly remains separate |
| Complete optimized physical local wrappers | `FramedBlocks`, `FramedEdgeTrace`, `Shared50BlockFrames`, `Shared50FramedInvocation`, `Shared50PhysicalEdges`, `Shared50InvocationPhysicalEdges`, `Shared50OppositeBlockFrames`, `Shared50FramedOpposite` | ✅ | ⬜ | Literal forward/opposite physical programs have exact sparse scalar erasure, arbitrary-module frame identities and exactly the ordered edges of the local rank histories; global physical assembly and tape costs remain open |
| Actual optimized projector operators and global boundaries | `Shared50InvocationProjectionRank`, `Shared50GlobalTrace` | ✅ | ⬜ | Every local physical edge is certified by its genuine rational projector-difference matrix and actual range-rank balance; all reused global boundary attachments have exact endpoints, nondegeneracy and zero loss. Full global trace assembly is proved separately |
| Complete optimized global projection-rank trace | `Shared50GlobalTracePlacement`, `Shared50GlobalTraceNondegenerate`, `Shared50GlobalTraceStages`, `Shared50GlobalProjectionRank` | ✅ | ⬜ | Actual reused three-stage trace reaches the prescribed sinks with nested nondegenerate edges and exact total loss; genuine projector range ranks plus the source correction meet the exact improved rank budget and strict branching bound. Full signed physical interface is proved separately; tape realization remains open |
| Optimized stage-reuse matching and labels | `TripleNeighborPermutation`, `Shared50ReuseLabels` | ✅ | ⬜ | Hall-selected actual neighbor bijection, nested nondegenerate stage boundary joins, zero join loss and exact 125,000 rank saving per joined role; reused scalar schedule proved in Shared50GlobalCircuit; global rank trace is proved in Shared50GlobalTraceStages |
| Optimized two-bank endpoint and numerical budgets | `Shared50GlobalBudget`, `Shared50Parameters` | ✅ | — | Actual padded two-bank world count and rational terminal dimension totals; strict branching inequality for the numerical rank budget. Actual trace balance and loss premises are discharged in Shared50GlobalProjectionRank |

### Optimized physical program and interchange

The optimized two-bank program realizes the full address shear and coordinate interchange modulo a good prime on dirty scratch.

- Math milestone: `IntegerMultBounds.Networks.Shared50FiniteInterchange.certified_interchange` — At every radix exponent over the one good prime, the pre/network/post program transposes both finite address chunks of every routed array including dirty scratch, is realized by its ordered physical field programs, and uses exactly the improved interchange count. Combines `Shared50FiniteInterchange.program_identity`, `Shared50FiniteInterchange.physical_realizes`, `Shared50FiniteInterchange.interchanges_exact`, `Shared50GlobalShear.program_identity`, `Shared50ModularExecution.program_identity`.
- Tape milestone: `IntegerMultBounds.Machine.Shared50RecursiveNodeExecution.finite_interchange_hoare` — Every node segment runs on tapes with its exact field action, the node pre/child/post decomposition composes to the full transpose, the recursive depth contract runs the fixed machine to the exact transpose within the node budget, and the finite interchange program is exact. Combines `Shared50RecursiveSegments.realizes`, `Shared50RecursiveNodeTranspose.transpose_all`, `Shared50RecursiveInduction.contract`, `Shared50FiniteInterchange.program_identity`.

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Complete optimized signed physical shear | `Shared50GlobalFramed`, `Shared50SignedBoundary`, `Shared50ShearEndpoints`, `Shared50GlobalShear` | ✅ | ⬜ | Actual signed physical two-bank program has exact scalar erasure, uniform full rational address shear on arbitrary binary arrays including dirty scratch, and ordered genuine projector-matrix certificates. The exact total range-rank budget satisfies strict branching; finite-radix realization and tape costs remain open |
| Actual optimized modular edge schedule | `Shared50OperatorPairs`, `Shared50ModularOperators`, `ModularFrameSchedule`, `ModularProgramShape`, `Shared50ModularSchedule` | ✅ | ⬜ | Concrete basis and actual matrix pairs; one good prime works at every radix exponent, preserving routed endpoint identities and exact interchange budget. Each edge reduces one fixed rational program with exact field-operation count; full modular physical assembly is proved separately; tape costs remain open |
| Complete optimized modular physical execution | `Shared50SignedFramed`, `Shared50ModularExecution`, `Shared50ModularControl` | ✅ | ⬜ | One fixed prime, every radix exponent, arbitrary finite arrays including dirty scratch: exact routed full shear, actual ordered field programs and the certified interchange budget. Canonical controls reduce fixed rational instructions with exact field-operation counts and lower-triangular transforms; literal tape execution remains open |
| Complete optimized finite address interchange | `Shared50FiniteInterchange` | ✅ | ⬜ | Literal pre/post field programs around the actual network give full coordinate-group interchange on every routed array including dirty scratch. Ordered physical field certificates, exactly the improved recursive interchange count, and fixed rational instruction shape are proved; tape execution remains open |
| Actual optimized dirty invocation | `DirtyLinearCircuit`, `Shared50Dirty`, `Shared50Invocation`, `Shared50Exchange` | ✅ | ⬜ | The actual shared program plus fifty central sums executes the twelve-block identity shear, its inverse and local three-invocation exchange, restoring arbitrary scratch; global reused scalar schedule is proved separately; rank assembly is proved separately |
| Sparse optimized invocation | `SparseCircuit`, `Shared50SparseIO`, `Shared50SparseCentral`, `Shared50SparseInvocation` | ✅ | ⬜ | Actual source/readout/central XOR lists with exact incidences and dense-matrix equivalence; sparse twelve-block shear, inverse and local exchange restore dirty scratch; at most 5,209,540 scalar instructions per invocation, not tape steps |
| Actual optimized two-bank global program | `Shared50GlobalCircuit` | ✅ | ⬜ | Literal sparse three-coordinate schedule, exact first/third scratch reuse, injective per-stage placements, full data-bank exchange and arbitrary scratch restoration; exact scalar list counts. Physical projector-rank assembly is proved in Shared50GlobalShear; tape costs remain open |

### Tape realization of the network

The Shared50 scalar programs and address-shear interfaces run on tapes with exact semantics and stream-time bounds.

- Math milestone: `IntegerMultBounds.Networks.ShearFrame.tape_interface_semantics` — The Shared50 XOR lists compute exactly the sparse invocation and global scalar programs, the rational address shear is the framed full shear, and the corrected physical network applies the full forward tensor transform on data and dirty scratch. Combines `ComplexEndpoints.corrected_network_run`, `ShearFrame.full_shear`, `Shared50XorLists.invocation`, `Shared50GlobalShear.program_identity`.
- Tape milestone: `IntegerMultBounds.Machine.CompactComplexRecursiveExecution.root_runs` — From the root bank, the fixed cyclic node table runs to halt with the full complex tensor transform installed and clean workspace, in total time bounded by the uniform recursive runtime (a constant times native volume times the certified stage factor).

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Actual Shared50 XOR tape circuit | `PointwiseBinaryNormalized`, `PointwiseRoleGate`, `PointwiseRoleCircuit`, `SparseRoleCircuit`, `OneSourceCircuit`, `Shared50XorLists`, `Shared50TapeInvocation`, `Shared50TapeGlobal` | ✅ | ✅ | Actual local/global scalar XOR lists execute on fixed role tapes, exchanging data banks and restoring arbitrary dirty scratch, all heads and binary clock. Concrete linear stream-time bound uses certified gate count; length descriptor supplied. Interleaved address transforms and recursive calls remain separate |
| Rational address-shear interface | `ProjectionRank`, `ShearFrame` | ✅ | ⬜ | Projection ranks, full signed physical frames, finite-radix realization and actual total budget proved; tape realization remains open |
| Phase interfaces and tape compilation | `BinaryRankFactors`, `ComplexPhaseBudget`, `BinaryColumnFrame`, `GroupedModuleFrames`, `FramedFactorExecution`, `ComplexFramedExecution`, `TensorTerminalWeight`, `ComplexEndpoints` | ✅ | ⬜ | Complete physically placed array-factor run with explicit character/phase corrections equals the full coordinate transform on data and dirty scratch, uniformly in columns; internal instruction count includes all scalar gates; the corrections are literal single-wire instructions (27 sign factors per X input, 28 per Y output, one negation per X output, i.e. 28 per data wire beyond the rank total) and every vector factor expands into its per-column Gaussian-dyadic kernels `aI + bX_v` (k per factor, 54k+2 corrections per address); literal tape costs remain open |
