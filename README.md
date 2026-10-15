# Integer multiplication in Lean

**Integer multiplication below `n log n` is proved in Lean on Mathlib's finite Turing machines.**

## Main result

`IntegerMultBounds.MathlibTM2.statement` is unconditional: one fixed
`Turing.FinTM2` machine multiplies every pair of natural numbers, with standard
binary input/output encodings, in worst-case time `O(n (log n)^(1-kappa))`.
The construction proves the positive saving
`kappa = 296 / (10^11 * 2^131)`, approximately `1.09e-48`, where `n` is the
total encoded input length. See [the completed plan](plan/C-mathlib-end-to-end.md).

## Stronger compact-control target

The original target is an actual deterministic machine with a fixed finite alphabet and
a fixed number of one-dimensional tapes, correct on every positive input
length, with worst-case runtime
`O(n (max(ceil(log₂ n), 1))^(1 - 83/10^12))`.

`IntegerMultBounds/Machine.lean` defines the machine semantics and the target
proposition `IntegerMultBounds.Machine.EndToEnd`. This is a proposition to be
proved, not a theorem or an assumed interface. Its transition function only
sees the finite state and scanned symbols. Each step writes at most one cell
per tape and moves each head at most one cell. Constants and the machine are
chosen before quantifying over inputs.

## Mathlib statement

`IntegerMultBounds/MathlibTM2/Statement.lean` states the target with Mathlib definitions only:
`Turing.TM2ComputableInTime` with Mathlib's binary encodings `encodingProd` and
`encodingNatBool`. `MathlibTM2.statement_of_endToEnd` proves `EndToEnd → MathlibTM2.Statement`,
so an auditor of the final result reads only that statement and its axioms. Applied to the
elementary multiplier, the same bridge gives the unconditional `MathlibTM2.mul_quadratic`, a
quadratic-time Mathlib machine. [The note](docs/mathlib-tm2/mathlib-tm2.pdf) explains the
statement and the simulation; `lake env lean MathlibTM2Check.lean` checks the axioms.

`IntegerMultBounds/MathlibTM2/Theorem.lean` proves `MathlibTM2.statement : MathlibTM2.Statement`:
a fixed `Turing.FinTM2` machine multiplies in worst-case time `O(n (log n)^(1-κ))` for an
explicit `κ > 0`. To verify it: read `Statement.lean` (its imports are Mathlib only), run
`lake build`, then `lake env lean FastPathCheck.lean`, which prints nothing when `statement` and
the main intermediate theorems depend on `propext`, `Classical.choice` and `Quot.sound` only
(`#guard_msgs` fails loudly otherwise). [The note](docs/fast-mult/fast-mult.pdf) describes the
machine and the proof.

## Status

The complete Mathlib host route, including recursive calls, transforms,
resampling, table generation, CRT routing, products, output and the total
step bound, is proved by `MathlibTM2.statement`. The remaining work below is
for the original native-machine route and its larger saving `83/10^12`.

On that route, Section 5 remains open. Its complete scalar-prefix/stopped-call and original
corrected-network orientation math milestones are proved. For a nonroot node
of exponent at least two whose children all stop, original coefficient and
tape readiness now gives actual classification, preorientation, corrected
source entry, the event schedule, physical sink correction, contraction,
cyclic rejoin, post-orientation and genuine saved-PC return on one aligned
table. The exact returned source implements the original forward or inverse
full tensor on every original row, polynomial and spectator slice. Output
widths, bounded grids, older saved-call association and all transition costs
are retained. Actual sibling child entry now derives its classifier input bank,
descriptors and clean tails; genuine dependency paths pay nested row divisibility
from the original padding. A scheduled nonstopped child of exponent at least
two whose own children stop now executes from that actual entry bank, retaining
its event trace, exact tensor and paid returned endpoint. Its completed frame transports back to the
original child snapshot, and tensor semantics supplies the tight parent return
grid. From the actual completed child trace and tensor, physical parent
restoration and inverse basis now execute with the original target and ancestor
frames retained. A checked completed-child certificate now joins those paths
and exact values in one compositional nonstopped parent-event Step, with its
result bank defined from the actual terminal frame. A general producer now constructs a completed child from a smaller-node
provider with fixed budgets. Provider-based nonroot execution joins actual
classification, preorientation, corrected entry, the complete mixed schedule,
normalization, finalization and genuine saved-PC return on the same bank,
retaining original forward/inverse tensor values and paid transitions. The
stopped loop now specializes the shared mixed loop with its original assumptions
and cost, removing the duplicate loop proof. Pure recombination lives below
recursive execution, avoiding an import cycle. Genuine Paths derive the
additional child-volume fit and descendant row guards from original padding.
Node-exponent induction now constructs the smaller providers internally with
fixed static budgets. The complete arbitrary-depth mixed schedule retains exact
compiler values, settled frames and target coverage without a child-execution
or child-tensor premise. Actual serialization supplies eventual descendant
packing. The literal nonstopped root now executes classification, physical
corrected entry, internally constructed events and finalization to halt on the
same aligned table. Its emitted array computes the corrected tensor at every
original row, polynomial and spectator address with exact widths and bounded
grid. All transitions are paid by the actual schedule budget. Positive and
exponent-zero stopped roots now execute their original leaf and retained
empty-stack halt on the same aligned table, with exact emitted banks and
all physical transitions paid. The reachable-execution row is complete;
the uniform total runtime and named full-recursion milestones remain open.
The actual schedule cost now splits exactly into its concrete local work and
original nonstopped child-path sum. Actual scalar/stopped-prefix volume
coefficients and the serialized child-volume quotient are proved. Both actual
basis directions now have one fixed certified stage-scale coefficient, and
the complete local-work bound retains every physical join. The expanded
polynomial scale now retains the original per-depth tau exponent, and the
actual completed-child path budget equals the checked fixed linear-volume
boundary plus its event budget. The static runtime invariant now closes,
and arbitrary-depth providers retain runtime certificates on their own
selected budgets with one machine coefficient before every exponent and
Path. Those certified choices now feed the actual node schedule and the
same halted root bank and tensor output, with a real recurrence bound
including the complete root boundary. The actual recurrence and that same
root coefficient now have a closed geometric estimate above the original
stopping cutoff, with forcing derived from complete paid local work.
The cutoff charge now has an explicit fixed-plus-leaf-width allowance,
including exponent zero. The real root classifier selects the cutoff
internally, and the same root coefficient has an explicit estimate in the
original uncontracted width. The classifier powers now yield the original
uniform stage-factor bound with one positive machine constant independent
of geometry and depth. The same selected coefficient is now retained through
provider, node and root execution; the actual nonstopped halted trace and
exact tensor output have one fixed positive uniform runtime coefficient
before every geometry and input bank. The positive and exponent-zero
stopped roots now use that same common coefficient on their actual halted
traces with the original stage factor. The actual uniform-runtime row is
complete. The same nonstopped output now carries explicit cleanup of every
role, entry-frame, leaf, work, scalar and basis tape, with zero heads.
The original-source bank constructor now supplies stopped-root
cleanliness, retained on the same positive and exponent-zero halted
outputs; original blank scalar/basis suffixes give the same clean aligned
endpoint. Stopped tensor readout is now joined to the same halted outputs.
The public native root contracts select the fixed basis compiler internally
and assume data admissibility without execution or total-time callbacks.
The paper-format layer adapter remains open: section six requires literal
MeetsLayer output, physical phase/normalization corrections, original-input
reservation and padding, final Q_p rounding and a complete admissible-call cost
bound; exact gates are listed in the section-five plan. The unconditional
PublicHadamardAddressBridge now proves exact public normalized Hadamard on the
original native rank codec for arbitrary positive suffix sizes and every
coefficient and suffix offset. CompactComplexPublicLayerTensor identifies this
layer with the same anchored fullFrame certified by positive native roots,
retaining the genuine visit positions, source/sink phases and exact normalization.
The fixed unit-weight phase family now physically updates the native source,
restores all 67 private tapes and retains exact tensor-phase readout and the
original grid, with one positive native-volume coefficient. Original-header
assembly and input phase placement are now derived on the exact aligned
root input bank, with tensor readout at every original address. The complete
input-phase/nonstopped-root/output-phase composition now has the same genuine
halted word, complete cleanup, retained phase headers and true grids. Output-phase
readiness derives from that actual returned bank, and the completed two-pass grid
supplies signed guards within the unchanged reservation. Decoded final readout
times the explicit Gaussian-dyadic factor is the normalized Hadamard tensor;
one positive fixed coefficient pays all traces and both joining edges.
Native normalization now has a checked fixed in-place numerator stream pass:
one sum/difference per coefficient, exact signed readout at the increased
denominator, genuine EOF returns, source overwrite and complete scratch cleanup.
The actual recursive Path derives its guards in the unchanged reservation,
with one fixed volume-plus-header coefficient. A complete fixed native
normalization lifecycle now also derives the count and denominator target from
original geometry, physically advances the true live descriptor once, and
erases every generated descriptor. Exact normalized readout and the true new
grid have one fixed serialized-volume bound. Original-header copying and
normalization now execute on the actual returned root source/live ports in the
existing leaf workspace, preserving every scalar/basis suffix and all cleanup.
The literal committed live word and its volume allowance derive from the same
reached root and original Path/ledger. The complete nonstopped phase/root/phase/
normalization trace now gives exact normalized Hadamard readout with no external
factor, actual advanced denominator, retained widths/grid/raw headers and one
positive packing-limit-only runtime coefficient. Positive stopped roots now
execute both phases, their actual stopped leaf and physical normalization on
that same fixed program and common coefficient, including depth-one visits.
Original certificates derive all phase-modified readiness and the actual returned
source/live words; exact normalized Hadamard readout, true leaf-target grid,
widths, raw headers and complete cleanup are retained. Exponent-zero scalar
wrapping, public-format parsing/reservation/padding and final rounding/restoration,
public parameter compatibility and cost, and arbitrary active-piece composition
remain open. Actual axis growth now
justifies eventual exclusion of nonstopped exponent-one nodes; finite small-input
coverage remains separate. The stopped
roundtrip's existing cost still includes its stopped-axis-count factor; the
volume-only tape milestone remains open.
Its recursive geometry math milestone is proved:
canonical axis coverage, fitting descendant intervals, unique exhaustive child
calls, the original rank-sum count and the exact manuscript stop rule are
certified together. Recursive controller execution remains open.
The exceptional-address repair math milestone is also proved: both actual
packed programs have exact repaired output, sparse extracted records and
the three-logical-volume cost bound at common dyadic parameters.
The basis-stage and phase math milestone is proved on one literal word and
coefficient bank, including exact reverse restoration and the full edge phase.
The compact-control math milestone now proves both early and late actual
destinations on the same original layout, including their composed payload endpoint.
Actual scalar successors and forward-child-inverse
returns now derive the original event semantics from their reached arrays;
the child result still requires recursive tensor correctness. Literal child-entry
captures now derive settled frames from the parent, and stopped-leaf execution
preserves those frames through its pre-pop endpoint. Full reachable recursive
execution and actual uniform runtime have explicit partial rows in PLAN.
Actual schedule prefixes now pay their sibling budgets from the original
node-entry Path. Scalar semantics and child-entry grid, ledger and tape ports
use that entry Path while counting preceding child returns exactly once;
the actual event now derives its prefix-to-call ordinal identity. Full physical
event induction remains open. Actual sibling scalar lifecycles now derive
their live capacity and next grid from the entry Path and execute in the fixed
aligned table with exact emitted arrays, saved history and paid runtime.
Sibling return guards now also derive from the original entry Path and
processed-call count, and an explicit-guard physical-return/inverse adapter
preserves the same fixed table and paid cost. Complete aligned stopped-child
classification, leaf, saved-PC pop, physical parent restoration and inverse
basis now compose after counted siblings using the original entry Path.
The installed stopped grid, genuine stopped/nonleaf return Progress and
next-event returned cursor are proved; the saved-target Ledger can be captured
at node entry. Full event induction and nonleaf completed-target coverage
remain open.
Actual forward
basis and physical child entry now also compose after counted siblings on the
unchanged aligned table, retaining the immutable target certificate; their
complete stopped event now runs from event PC to next-call PC with every
join paid. Its literal stopped output derives child tensor correctness, so
the actual forward/returned/inverse witnesses have the original instruction
semantics without a child-transform premise. Nonleaf child correctness and
whole-schedule recursive execution remain open.
Complete stopped-root execution, full stopped-leaf
tensor semantics, genuine halting and paid runtime are checked. Corrected
source entry, sink corrections, contraction/rejoin and saved-PC dispatch also
have checked local paths.

The concrete reached-event invariant now retains actual raw banks and arrays,
physical node exponent, target readiness/growth, numerical grids, live ledger
and associated saved-call list. Corrected entry initializes it, and paid actual
scalar table steps preserve it. Genuine child input readiness, the child Path
and ledger, pushed call frame and paid original child-entry execution derive
from that parent invariant.

Actual coordinate-weighted directions and child address tensors, conjugated by
the literal basis word, match the original residual frame factors. The complete
original array network now has a certificate from the same actual call list,
including chronological coordinate order and exact rank-sum factor count.
Selected-role forward/reverse basis routines have checked permanent and full
source-ready placements with restored headers and private workspace. One fixed
prime-alphabet table contains those passes around actual child entry and return.
Selected-role quotient headers now prepare and restore parent geometry around
both basis passes. Actual quotient-row serializers now supply basis input
readiness, and exact basis permutations preserve the reached parent invariant.
Actual reached scalar events and basis-aligned child-entry prefixes now run in
the aligned table, with literal next banks and every transition paid.
Actual corrected source setup and sink finalization also have paid aligned
table paths, preserving the blank basis workspace. Aligned child returns and
the complete reached event induction remain open. Numerical return grids and
ledgers, actual decoded-return execution and inverse basis restoration now
have checked adapters. Completed-child output width now follows from its reached stored widths
through actual sink correction, contraction, rejoin and orientation. The return
grid and recursive saved-frame preservation remain obligations. Actual aligned root finalization
now reaches its proved empty-stack cell and genuinely halts in the same table;
the preceding full recursive execution remains open. Saved caller prefixes now
have local preservation rules through scalar/basis execution and actual
stack/payload saves and restores. Recursive induction must still prove their
settled completion conditions. Actual corrected source setup now both runs in
the aligned table and establishes the concrete reached event invariant from
original source words, grids, ledger and saved calls. Completed nonroot sink
endpoints now derive the actual physical return ports and pre-pop saved call
association; dormant restoration still needs recursively proved settled frames.
Completed-child return readiness now derives its physical saved-stack equations
and exact record widths, while the full coefficient phase stream has checked
initialization, loop execution, cleanup and a linear transition bound.
Computed native basis destinations now have the original ambient coordinate
map and retain exact stored and decoded coefficients at every polynomial index.
Full slice alignment and the original child factor are now derived.
Actual return geometry derives restored ports, the selected-role payload and
the canonical returned caller from the reached parent. The aligned table also
pops the genuine associated saved call with its exact runtime. The actual
completed child now supplies that path with its derived return stacks retained;
forward child entry and inverse return share one fixed basis program. The
inverse adapter derives width and promotion guards from the child and parent
path. Literal physical return now joins the inverse basis pass and reaches
the original next-call PC. The computed completed child now supplies a joined
guard/pop/physical-return/inverse path with all transitions paid, deriving its
raw, scalar, controller and width readiness. Physical live-exponent budgets
are now independent of returned child-volume accounting. Captured saved-stack equations,
recursive settled frames, output grids and ledger progress remain explicit;
full recursive event induction and total runtime remain open. Actual child-entry
captures now derive the saved header, live, target and payload references.
Corrected source setup, scalar/basis events and completed-child finalization
preserve settled frames on their actual reached witnesses. The recursive
return adapter derives its parent grid and physical budget from child
tensor semantics and actual ledgers. Balanced physical return now preserves
settled ancestor frames on the returned and inverse-basis reached witnesses.
The forward-child-inverse composition now derives the original residual
factor at the unchanged parent address from recursive child tensor semantics.
Child semantics and target coverage still need the full event induction. The actual ordered
site trace now retains every original compiler wire and both frames, including
terminal sink incidences. The actual interleaved child-call and scalar schedule
now has exact original compiler semantics on every wire array. Recursive tape
execution and total runtime remain open.

Complete boundary and event allowances pay classification, corrections,
contraction, genuine return dispatch, both basis passes and their joins. The
basis stage-scale term remains explicit alongside original recursive budgets.
Complete nonleaf recursive correctness and
termination, and the actual total runtime recurrence remain open.

The machine model, the target statement, and a growing set of algorithmic and
analytic components are formalized and checked. See
[COMPONENTS.md](COMPONENTS.md) for a file-by-file summary of what each
component proves and what it leaves open, and [PLAN.md](PLAN.md) for a
detailed status of each row below, broken down by subcomponent.

Rows follow the sections of the OpenAI manuscript, plus the Harvey–van der
Hoeven `O(n log n)` multiplier it uses as a subroutine. *Mathematics* means the
statements the algorithm relies on are proved in Lean. *Tape* means a program in
the literal machine model is proved correct with a runtime bound.

| Part of the proof | Source | Mathematics | Tape | Main gaps |
| --- | --- | --- | --- | --- |
| [Proved Mathlib end-to-end multiplier](plan/C-mathlib-end-to-end.md) | Full host route | ✅ | ✅ | None for the existential sub-n-log-n statement: `MathlibTM2.statement` is unconditional, with positive saving `296 / (10^11 * 2^131)`. The remaining rows track the original native route and its stronger fixed exponent. |
| The machine model and elementary streams | §2 | ✅ | ✅ | Fixed machines execute initialized mixed affine schedules and actual nonrecursive Shared50 segments from sole array and canonical b/W inputs. Exact output, retained headers, dimension synthesis and complete private-workspace cleanup are proved in linear-volume time; every private tape and tracker returns blank at head zero. Counted pointwise finite-symbol operations also have exact tape proofs, including encoded XOR. Cross-view composition and the full recursive call controller remain open. |
| Two finite networks with a rank saving | §3 | ✅ | 🟡 | Optimized finite network algebra and rank certificates are proved. The actual local/global Shared50 scalar XOR lists now execute on fixed tapes with exact data exchange, dirty-scratch restoration and linear stream-time bounds. One width-independent interleaved control list now preserves every role, address operation and scalar gate, with exact recursive-call count and transpose semantics. Certified segment/gate tape machines and explicit call boundaries are available; recursive calls and full network tape assembly remain open. |
| Faster interchange of address chunks | §4 | ✅ | ✅ | The main binary interchange theorem is proved: one fixed machine uses original five canonical headers, physically selects equal or adjacent widths, returns exact binary rectangular transpose, and restores all private storage. Its actual runtime, including comparisons and dispatch, has the certified exponent 1−296/10^11, including zero widths. Multiplication EndToEnd remains open. |
| Fast simultaneous synthetic butterfly layers | §5, §11, CrocSwap | 🟡 | 🟡 | Actual compact-control interchanges, repair, reservation, padding and phase execution have literal tape semantics, clean workspace and certified component costs. Complete named scalar-array sequences now have the original complex-circuit semantics, with every intermediate guard derived from the actual dependency Path and retained-width reserve, eventually paid by the original chunk choice. Actual named scalar sequences execute complete polynomial arrays, replace source streams, restore heads and private tapes, and physically increment a common live denominator once per completed row. A complete actual stopped-call roundtrip now selects and saves its target, enters and executes the original-codec child, pops the real return PC and restores parent geometry and target stacks with full paid cost. Old live7 and generated target8 remain available for the shared-grid handoff. Leaf and nonleaf return policies, physical target-word construction and actual runtime stopping-test selection are proved, with full workspace cleanup and preserved controller stacks. Literal spectator numerator promotion now proves common child-return precision and the advanced sibling budget from actual dependency Paths; fixed all-spectator promotion now physically synthesizes each gap from live/target headers and preserves the selected role and controller frame. Actual role serialization identifies its physical endpoint with these shared-grid arrays; stream-volume headers now physically derive from retained raw geometry and are fully erased after promotion, with uniform actual native/role-volume setup and cleanup bounds. Actual scalar streams now share their named permanent role tapes and storage7 live denominator, preserving the remaining controller frame and reclaiming all private work. Original count-header production is now proved from retained native geometry with complete cleanup; its setup and final header-erasure costs have uniform original-native-volume bounds. The actual root-bank producer now supplies scalar Ready directly from retained geometry and literal native role streams while preserving live7 and all stacks. The complete actual scalar lifecycle now composes original count setup, named role execution and final count erasure, with literal output, advanced live denominator, all private storage blank and a uniform fixed-block linear volume bound. The scalar lifecycle now exposes the dependency-derived numerical output grid; contiguous scalar prefixes share one full-network growth allowance. Actual grouped vertices now derive their named scalar blocks and full-network boundaries internally, with paid physical execution preserving the node budget. Each group now retains the exact next original scalar-prefix grid, enabling successive groups to share the single growth allowance. One combined actual group-step theorem now supplies its literal next native caller, retained widths, tighter numerical grid, physical live header and upper ledger with the full paid runtime. Their literal outputs are now identified with the genuine native polynomial rows consumed by subsequent physical events, retaining dimensions and field widths without conversion. Complete scalar output reconstructs the literal next raw caller bank, preserving all descriptors and stacks while advancing live7 and restoring blank count storage. The fixed promotion/commit sequence now installs the common live denominator after all spectators are physically aligned, with full cleanup and paid joins. The dependency Path now derives target capacity and absorbs promotion/commit header costs into actual role volume, with physical live-progress now propagated through actual scalar lifecycles, genuine child entry and complete stopped aligned returns; every completed event prefix now also has an exact true-denominator formula and counted upper ledger. Instantiating those local endpoint contracts in full unstopped induction remains open. The complete stopped call now composes its ledger roundtrip with a second paid parent codec lifecycle, generated-volume spectator handoff and live installation, restoring the literal parent bank and all private workspace. The complete root enumeration lifecycle now separates the actual callback runtime sum from a controller overhead proved linear in original native/serialized volume, including queue and numeric cleanup. Exact fixed-role precision contraction now has literal tape endpoints and paid runtime, with coarser-grid membership proving exact signed division; the actual controller-bank nonleaf adapter now generates length metadata, contracts all role fields, cleans up and commits the genuine target. The complete all-role contraction, generated metadata cleanup and live commit now have uniform native/role-volume runtime bounds derived from the Path and true live ledger. The actual interleaved schedule now has exact named scalar/call counts and its completed local denominator endpoints derive the lower ledger covering the real nonleaf target. A finite node compiler now uses actual named scalar lifecycle programs and local child machines on one unchanged common caller bank, charging all local costs and joins and restoring private workspace. It remains a local composition theorem; fixed cyclic recursive closure and the child contracts are still open. Completed-network correctness and construction of the local child executions in a fixed cyclic dispatcher remain recursive induction obligations. The fixed cyclic return controller now preserves the literal full scalar/native/role caller bank through actual PC decoding and genuine root halting; the same actual caller return flow now includes a fixed blank workspace suffix for the arithmetic subroutines. Four disjoint fixed entry/stopped/nonleaf/return PCs are now reserved without changing the original saved-return encoding, on that full caller and workspace bank. The original schedule now has unique child/scalar occurrences and exact child-return event successors with injective fixed event PCs. Actual saved call PCs now decode in the common address space with their literal original saved bits unchanged and event-entry disjointness proved. The actual fixed-event path assembly now requires local proofs only at reachable caller prefixes, sums all local costs and connects to genuine root halting. Physical nonleaf payload entry now parks the retained master and spectators with separate generated counts, moves the selected source and restores the literal raw headers, with a uniform native-volume runtime bound paying both header lifecycles and every join. Child geometry/denominator handoff and physical event paths and recursive execution remain open. The fixed cyclic table now contains the original decoded returns, four controls and actual event schedule, with exact successor edges and code independent of runtime depth; Reachability-local path contracts now connect actual scalar successors, shared child entry, decoded continuations and terminal controls in that same fixed table, paying all joins; physical source-ready lifecycle instantiation and full recursive correctness remain open. Completed child semantics now derive the normalized nonleaf return grid while preserving the exact parent scalar-prefix budget and advancing only its returned-volume ledger; concrete address maps and recursive execution remain open. The physical return now recovers an arbitrary supported child result into its parent role and restores spectators, the retained master and the full ancestor stack with both generated-count lifecycles erased and all recovery costs bounded uniformly by native volume. The physical return also preserves an entire simultaneously changed complementary controller bank, including all live, target and stack tapes and their heads; genuine child-result semantics and restored parent geometry remain recursive assembly obligations. Genuine nonleaf row quotient and cyclic child-role splitting now execute directly from the actual entered source, deriving the child divisor from the next descendant and preserving stored live/controller/ancestor data. Arbitrary completed child arrays also physically merge back to the selected source, with a paid multiplication restoring the original parent row descriptor; actual current-node merging now produces the source-ready native endpoint, erases all seven private tapes and retains root rows with a uniform original-volume runtime bound and grouping derived from the actual dependency Path; a separate paid parent-only row-restoration block applies after decoded child return, while decoded child continuations restore the parent count exactly once; both actual split and merge now have uniform parent-native-volume runtime bounds, including row arithmetic and cleanup; physical merge and arbitrary-result parent restoration now compose on one fixed bank with all exact costs paid, a complete uniform parent-native-volume runtime bound and actual word support derived. The raw-to-raw nonleaf spectator promotion and final shared-live commit now execute with exact endpoints and a complete Path-derived volume runtime bound. Combining actual completed-child semantics with that handoff preserves the parent scalar prefix and returned-volume ledger; Actual child-header entry now saves the parent target, live denominator, geometry and original PC, decrements the exponent and synthesizes child headers while retaining the source-ready payload and row descriptor. Complete parent payload parking, one row quotient and that child entry now compose from the original caller, retaining the selected source before the stopping guard; only the nonleaf branch splits current rows, and the complete parking/quotient/header entry has a true-ledger-derived native-volume bound including all joins; Physical reverse continuation now pops genuine parent geometry, restores the control exponent and multiplies the parent row descriptor exactly once, with a literal raw parent endpoint and all costs paid; that continuation now also physically preserves child live in the pending target and restores the saved old parent live word, deriving intermediate readiness from the actual bank; the complete geometry/row/live continuation has a ledger-derived uniform native-volume bound, while actual source-ready payload recovery now derives protected-bank readiness from concrete returned endpoints and restores master, spectators and arbitrary selected result with a uniform native-volume bound; the final paid parent-target pop now derives its saved frame from actual child entry and preserves advanced live after target8 is cleared; spectator promotion and shared-live commit now also have exact placement on the source-ready bank with a fixed ten-tape suffix, preserving the nonblank payload stack and all nine frame tapes; spectator promotion, shared-live commit and the final saved-parent-target pop now compose on that fixed bank with a uniform runtime bound; actual parent geometry/row/live restoration now composes directly with payload recovery, deriving intermediate readiness and paying the join; the actual spectator/target continuation now retains the next parent prefix grid and true returned ledger using concrete child maps and has a paid decoded-return path to the unique event successor; it must still join the payload block in the full decoded continuation, and concrete per-spectator child address maps now derive actual cyclic-role inputs and returned parent arrays; full recursive execution remains open. A paid fixed-stack lifecycle now saves the event-specific parent live denominator and, after child return, copies the child normalized live word to target8 before restoring old parent live7 for spectator promotion; both actual live-stack machines now have Path/ledger-derived original-volume runtime bounds, and no common-grid claim is made before that promotion. The complete stopped call now has a uniform original-volume-times-child-size runtime bound, including both codec lifecycles, generated headers, alignment, live commit and cleanup. Structural runtime budgets now sum every actual child occurrence, absorb quotient rounding and use the certified branching saving to bound width-dependent local costs, with separate stopped-leaf and internal terms. Actual scalar lifecycles and completed-return metadata now have derived aggregate volume bounds; true child target selection and denominator-stack save/restore are separately paid from changing Paths and live ledgers. Literal child-return codec, exact contraction, spectator promotion/live commit and target/PC restoration costs now have separate Path-derived volume bounds and actual-call sums. The node aggregation is still explicitly partial: nonleaf denominator readiness, selected-child splitting/semantics, actual return sequencing/joins and physical interchange execution must still instantiate the recurrence with child execution. Stopped arithmetic and spectator promotion now preserve the tighter original scalar-prefix grid, with guard capacity derived from the actual Path and exact reserved-role reconstruction; the unchanged complete stopped-call tape adapter now accepts current role arrays directly and returns the literal next caller with that exact prefix bound, retaining parent levels and paying all original costs. That stronger prefix adapter now also has the uniform original-volume-times-child-size runtime bound, with capacity derived from the genuine live prefix ledger. The shared source-ready guard now physically tests the original global dimension and current exponent, restores all borrowed scratch and reaches the actual stopped/nonleaf PCs in the cyclic table with paid state-dependent paths. Actual selected child entry likewise reaches the shared entry PC from its genuine scheduled event and saved address. The complete stopped route now continues through real count-dispatched leaf execution to the actual return guard, with one uniform bound paying the test, leaf and both table jumps, including roots and scalar leaves. The four physical controls are direction-specific; the real saved call PC now physically selects forward or inverse stopped-leaf arithmetic while restoring the literal stack and whole bank; the actual scalar lifecycle now has exact placement in a dedicated fixed suffix, preserving the complete existing bank and returning every new scratch tape blank; the original corrected framed network now has a proved genuine inverse tensor endpoint through complex conjugation, retaining its scalar gates and order; actual source65 conjugation now preserves the whole caller bank, has a uniform five-times-native-volume runtime and derives exact decoded conjugation from the original dependency grid guard; actual child-entry and complete decoded child-return paths now also run in the scalar-inclusive table, retaining its arbitrary scratch and every paid join; a fixed runtime wrapper now derives root-forward identity or saved-call inverse conjugation from the real return stack, restoring its literal saved frame and charging all scan/peek/guard traffic; the same actual wrapper now derives exact decoded orientation from the dependency Path and preserves the saved frame, numerical grid and native widths at a uniform volume cost; complete oriented entry/final block composition, actual grouped scalar events now execute in the populated full table with literal next callers, tighter prefix grids, physical live ledgers and paid jumps; actual saved-call orientation now precedes the genuine stopping guard, retaining all controller frames and scalar workspace with original-path native-volume cost; actual nonleaf target generation now composes with the current-row splitter, and exact contraction composes with same-row merge, each with paid native-volume cost; actual nonleaf finalization now retains the saved call frame, executes its post-orientation selector and follows the paid table edge to the return guard; the fixed table now has all four actual controls and its genuine stopping classifier. Actual child/root entry follows the halted marker to the correct branch, and all four stopped child/root branches follow their paid table edge to the return guard. Actual scalar count setup now derives the role-row quotient privately while preserving the parent row descriptor, and the populated scalar event proofs retain this metadata with paid original-parent volume bounds. Original raw-header sign correction now privately derives the role-row quotient, executes the selected character and reclaims all private tapes; original-header sink phase and negation now also derive their counts, replace sources and reclaim all sixty-seven private tapes within linear parent-volume bounds, and one fixed machine now exchanges every actual named X/Y role on the source-ready bank with retained controller frames, leaf and scalar suffix and paid parent-volume cost. Full named-role source/sink boundary assembly is still required to realize the corrected tensor theorem; full reachable recursive execution and its total bound remain open. A direct source-ready stopped block now executes the real directional leaf, synthesizes its target from actual live/volume tapes and commits advanced live7 with the entire fixed leaf-plus-ten suffix reclaimed; exact normalized leaf semantics and all physical costs are proved, the actual positive ChildBank count expansion/restore and exponent-zero runtime dispatch now connect that block to real child headers, with full uniform Path/live-ledger runtime bounds. Public, leaf and spectator components now share one fixed leaf-plus-ten bank through exact executable placements. The complete actual child-return sequence now joins payload recovery, spectator promotion, shared-live commit and saved-target restoration into a paid decoded next-event path, advancing the original parent prefix and returned ledger. Remaining work includes inherited precision propagation, interleaved unstopped recursive execution, root callback discharge and the uniform physical recursive cost sum. Actual basis execution now derives complete original tensor-slice alignment and the original child factor without a supplied alignment premise; complete recursive fixed-table execution and its total runtime remain open. |
| Synthetic transforms and their tape layout | §6 | ✅ | ⬜ | Synthetic ring, principal roots, Bluestein, and the layout counts, round error accumulation, and cost bracket matching the cost table are proved; tape execution is open |
| Resampling with the permutations left in the transform | §7 | ✅ | 🟡 | The factorization `F_s = 2^γ B F_t A` with `‖A‖, ‖B‖ ≤ 1` is proved in one and `d` dimensions, with truncation and Neumann-series error bounds for its pieces; the numerical approximations of `A` and `B` have scaled error below `p²`; the permutation-left variant with its explicit numerical maps, in one and `d` dimensions, and its chirp and cancellation identities is proved; the line counts of the tensor interface match the cost table with negligible setup; on tapes, the row-selecting map `C` is realized by a modular-counter selection machine at linear cost with no numerical error, a signed fixed-point word layer (sign-extending accumulation, negation, truncating multiplication with a quadratic inner product) is in place, and the Gaussian window sums of `Ã` run on a fixed twenty-two-tape machine given the rounded weights, with its accumulators proved equal to the numerical map `Ã`; weight evaluation, `B̃` and the line machines remain open |
| Exact integer multiplication and its cost | §8 | 🟡 | ⬜ | Parameter margins, asymptotics, odd pairwise coprime source lengths (replacing short-interval primes), the size relations, the precision chain to exact recovery of the product, and the cost table rows assembled into `O(n (lg n)^(1-κ))` are proved; the components' row costs remain open. Exact recovered output now has exactly twice the input length even for nondivisible chunk widths; physical carry propagation and installation remain open. |
| A. Fast multiplication subroutine | Schönhage–Strassen | ✅ | 🟡 | The packed products need a multiplier within `m log m (log log m)^c`, whose extra logarithmic overhead is formally absorbed by the certified packed-product margin; the twisted-transform convolution theorem and one Schönhage–Strassen level modulo `2^n + 1` are proved; the recursion, its cost and the tape machines are open |
| B. End-to-end theorem `EndToEnd` | — | 🟡 | 🟡 | The complete fixed ordinary multiplier is proved from original input through genuine halting and exact twice-length product output, with quadratic runtime including empty inputs. Fast-path assembly and the final sub-n-log-n bound remain open. |

✅ done · 🟡 partial · ⬜ not started

## Remaining obligations

The target still requires an explicit multiplication program and proofs of its
execution, stream primitives and counters, finite bit and complex networks,
recursive tape scheduling, modular compact controls and their repair costs,
synthetic transforms, Gaussian resampling, prime selection, exact coefficient
arithmetic, rounding, carry propagation, and the final uniform complexity bound.
The upstream proof also invokes an existing fast multiplier as a subroutine,
citing Harvey and van der Hoeven's `O(n log n)` algorithm. Any multiplier within
`m log m (log log m)^c` suffices, since the cost table absorbs the extra factor,
so the `Schoenhage/` directory formalizes Schönhage–Strassen instead: its
transform, one level modulo `2^n + 1`, and (in progress) the recursion and its
tape machines. The `NLogN/` directory keeps the transform, fixed-point,
Kronecker and Gaussian resampling mathematics that the main proof uses. The Harvey–van der Hoeven recursion itself is not needed: the main proof's packed products only require a multiplier within `m log m (log log m)^c`, which the cost table absorbs, so Schönhage–Strassen (`Schoenhage/`) replaces it. Its 28 recursion-only files (step contract, recurrence, cost model, moduli, power-of-two transforms) were removed; restore them with `git checkout 834ad45 -- IntegerMultBounds/NLogN/CRTMulti.lean IntegerMultBounds/NLogN/Capstone.lean IntegerMultBounds/NLogN/Contract.lean IntegerMultBounds/NLogN/ContractFinal.lean IntegerMultBounds/NLogN/ContractPrep.lean IntegerMultBounds/NLogN/ContractSqrt.lean IntegerMultBounds/NLogN/CostBound.lean IntegerMultBounds/NLogN/CostFinal.lean IntegerMultBounds/NLogN/CostModel.lean IntegerMultBounds/NLogN/ExpCostBound.lean IntegerMultBounds/NLogN/ExpEval.lean IntegerMultBounds/NLogN/JointRecurrence.lean IntegerMultBounds/NLogN/MainParams.lean IntegerMultBounds/NLogN/MainRecurrence.lean IntegerMultBounds/NLogN/MainStep.lean IntegerMultBounds/NLogN/MainTransform.lean IntegerMultBounds/NLogN/ModuliConstruction.lean IntegerMultBounds/NLogN/PowerOfTwoContract.lean IntegerMultBounds/NLogN/PowerOfTwoExact.lean IntegerMultBounds/NLogN/PowerOfTwoExactD.lean IntegerMultBounds/NLogN/PowerOfTwoNumeric.lean IntegerMultBounds/NLogN/PowerOfTwoNumericD.lean IntegerMultBounds/NLogN/PrecisionCheck.lean IntegerMultBounds/NLogN/PrimeSelection.lean IntegerMultBounds/NLogN/Recurrence.lean IntegerMultBounds/NLogN/RecurrenceParams.lean IntegerMultBounds/NLogN/ResamplingOps.lean IntegerMultBounds/NLogN/SmallMultiplierCost.lean` and re-add their imports to `IntegerMultBounds.lean`.
None of these algorithmic contracts may be assumed to claim the requested
end-to-end result.

## Building and verification

Install the version of Lean in `lean-toolchain`, then use the guarded local
verification commands:

```sh
python3 scripts/build-lean-guarded.py IntegerMultBounds
python3 scripts/check-lean-safe.py AxiomAudit.lean
python3 scripts/check-lean-safe.py MathlibTM2Check.lean
python3 scripts/check-lean-safe.py FastPathCheck.lean
```

For local component checks, use `python3 scripts/check-lean-safe.py FILE`.
This runner permits one check per workspace, uses one Lean thread and a
24576 MiB Lean memory limit, and stops the process group if its observed RSS
exceeds 28672 MiB or the check runs past twenty minutes. It also stops child
processes if monitoring fails or the check is interrupted. Dependencies must already have compiled artifacts;
it does not launch a broad build. The guarded build stops at 80 GiB combined
RSS or three hours. Both runners share one workspace-wide lock.

Lean and mathlib are pinned to v4.34.1; `lake-manifest.json` pins transitive
dependencies. No theorem in this project uses a custom axiom or an admitted
proof.

`AxiomAudit.lean` checks public and private project declarations, transitively,
allowing only Lean's standard `propext`, `Quot.sound`, and `Classical.choice`.
It rejects admitted proofs, custom axioms, and native-evaluation axioms. CI
builds the project and runs this audit.

## References

### Primary sources

- Douglas Colkitt, *A sharper exponent for integer multiplication*, research
  draft, [CrocSwap/integer-mult-bounds](https://github.com/CrocSwap/integer-mult-bounds),
  commit [`6e56487`](https://github.com/CrocSwap/integer-mult-bounds/tree/6e564879f51ae16f23d392e9e196c605f36d90df)
  (October 7, 2026).
- Its pinned OpenAI manuscript,
  [*Integer multiplication below n log n*](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026),
  in [openai/math](https://github.com/openai/math), commit `adc7f12`.
- David Harvey and Joris van der Hoeven,
  [*Integer multiplication in time O(n log n)*](https://doi.org/10.4007/annals.2021.193.2.4),
  Annals of Mathematics 193(2), 2021, 563–617. The upstream proof uses this
  multiplier as a subroutine. Lemma and section numbers in `NLogN/` refer to the
  [author-hosted manuscript](https://www.texmacs.org/joris/nlogn/nlogn.pdf).

### Classical results formalized here

- J. W. Cooley and J. W. Tukey, [*An algorithm for the machine calculation of
  complex Fourier series*](https://doi.org/10.1090/S0025-5718-1965-0178586-1),
  Mathematics of Computation 19(90), 1965, 297–301. (`NLogN/FFT.lean`)
- A. Schönhage and V. Strassen, [*Schnelle Multiplikation großer
  Zahlen*](https://doi.org/10.1007/BF02242355), Computing 7, 1971, 281–292.
  (`Schoenhage/`)
- L. I. Bluestein, [*A linear filtering approach to the computation of discrete
  Fourier transform*](https://doi.org/10.1109/TAU.1970.1162132), IEEE
  Transactions on Audio and Electroacoustics 18(4), 1970, 451–455.
  (`NLogN/Bluestein.lean`)
- R. C. Agarwal and J. W. Cooley, [*New algorithms for digital
  convolution*](https://doi.org/10.1109/TASSP.1977.1162981), IEEE Transactions
  on Acoustics, Speech, and Signal Processing 25(5), 1977, 392–410.
  (`NLogN/Multidim.lean`)

### Lean libraries

- [complexitylib](https://github.com/SamuelSchlesinger/complexitylib), commit
  [`3f4b5fe`](https://github.com/SamuelSchlesinger/complexitylib/tree/3f4b5fee8bbd49721a5b70473c81bf3db2e7500d),
  for the machine composition design (no code imported).
- [mathlib4](https://github.com/leanprover-community/mathlib4), v4.34.1.

The local `integer-mult-bounds/` checkout is reference material and is ignored
by this project's Git repository. The Lean project does not execute or trust
the source repository's Python certificates.

## License

[MIT](LICENSE).
