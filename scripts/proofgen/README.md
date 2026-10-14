# Certified sequence pilot

This pilot generates straight-line composition proofs for the existing section 6
layout setup. It reuses `Schoenhage.Cmd`, `Runs.then` and `compile_correct`;
it does not introduce another machine model or proof evaluator.

The reusable Lean interface is `Schoenhage.CertifiedSequence.Block`. `ofRuns`
extracts a command, its exact complete-bank endpoint and its bound from an
existing `Runs` theorem. `Block.then` requires matching intermediate banks and
adds one actual connecting transition. `Block.hoare` proves execution and
halting of the compiled literal machine. This interface can also be used
directly in handwritten Lean, without Python.

## Generate and verify

From the repository root:

```sh
python3 scripts/generate_lean_sequence.py scripts/proofgen/layout_setup.json IntegerMultBounds/Schoenhage/LayoutSequenceGenerated.lean
python3 scripts/generate_lean_sequence.py scripts/proofgen/layout_setup.json IntegerMultBounds/Schoenhage/LayoutSequenceGenerated.lean --check
python3 scripts/proofgen/test_generator.py
python3 scripts/proofgen/verify_pilot.py
```

The verifier uses only `check-lean-safe.py --wait-for-lock`, compiling the small
helper and generated module before checking the manual baseline and transitive
axiom audit. Existing `LayoutGenRun` dependencies must already be built. Its
temporary negative fixtures are removed automatically. A busy workspace queues
these checks behind the other agent; reported times include that wait.

The pilot is intentionally standalone, not imported by the library root and not
counted as a completed milestone. Its verifier applies the same axiom whitelist
as `AxiomAudit.lean` to all declarations in the three pilot namespaces, including
their transitive dependencies. No proof limits are increased.

## Authoring a sequence

The manifest supplies shared Lean binders and arguments, the input and expected
output bank, and one command/proof pair per stage. Expressions are Lean source;
this is an authoring format for repository contributors, not an untrusted-data
execution interface. Each proof must already establish a `Runs` contract with
an exact whole-bank output. Costs are inferred, never copied into the manifest.

Generation emits a fixed command independent of the input values, a certificate,
the total bound, program/output identity checks, a sum-of-phase-costs theorem,
and word-level and literal-machine execution theorems. Lean checks that the
provided commands really are those certified by the proofs. Descriptor work,
primitive cleanup and inner joins remain included in each supplied bound;
the generator adds outer joins. It cannot manufacture a missing primitive proof
or omit a dirty scratch tape from an exact-bank contract.

The two-stage constants/copies case matches an independent manual proof and
its explicit cost exactly. The second case composes all six existing setup
phases through `stF`, including descriptor arithmetic, conversions, arrangement
generation and its existing cleanup. This stops before the prefix moves and
chunk-exchange loop; it does not assert that all scratch is blank at `stF`.

## Evidence and limits

The positive checks establish endpoint and literal-machine correctness. Negative
checks deliberately reorder phases, substitute an uncertified command and remove
a join charge; each must fail Lean elaboration. Five Python tests cover manifest
validation and exact regeneration.

On the initial successful local run, the helper checked in 1.32 seconds, the
generated module in 2.25 seconds and the manual baseline/axiom audit in 2.67
seconds. Observed peak memory was about 2 GiB. These are guarded wall times with
existing dependency artifacts, not a controlled comparison with handwritten
proofs. Token savings and faster elaboration have **not** been demonstrated.

The pilot removes duplicated cost formulas and endpoint plumbing, but short
`Runs.then` chains were already easy to write by hand; the manifest and generator
have their own maintenance cost. Do not expand this into a broad compiler yet.
The next useful experiment would target repeated tape-placement and cleanup
adapters, measuring human-authored changes, retries and check time against a
handwritten adapter with the same endpoint and cost guarantees. Branching,
existential intermediate states, recursive schedules, arbitrary state rewrites,
and asymptotic inequalities remain explicit proof obligations.

## Tape-placement and cleanup extension

The second pilot implements that next experiment, still without changing the
existing production proofs or the library root.

```sh
python3 scripts/generate_lean_adapter.py scripts/proofgen/layout_placements.json IntegerMultBounds/Schoenhage/LayoutPlacementGenerated.lean
python3 scripts/generate_lean_adapter.py scripts/proofgen/twist_cleanup.json IntegerMultBounds/Schoenhage/TwistCleanupGenerated.lean
python3 scripts/proofgen/test_adapters.py
python3 scripts/proofgen/verify_adapters.py
```

Both generation commands accept `--check` for exact reproducibility. The adapter
verifier assumes the first pilot's `CertifiedSequence` artifact is built and
uses the same serialized memory guard for every check.

`CertifiedPlacement.placed_update` lifts any single-output local `Runs` contract
through an injective tape map. The local theorem must establish that its entire
bank is preserved except that output, including scratch cleanup. The lifted
result preserves all other global tapes and retains the original bound.
`CertifiedBinOf` supplies this contract once for the existing binary converter.
The current placement generator intentionally supports this one kernel; adding
more kernels needs corresponding proved contracts, not new assumptions.

The placement manifest contains just names, bank sizes and slot vectors for the
two actual `runs_binPhase` placements. It generates checked injectivity, fixed
programs, exact bank-update contracts and compiled machine contracts. Costs are
inferred from the converter theorem. `LayoutAdapterPilot` proves that these
programs equal the existing `fb1` and `fb2` placements and instantiates both on
the actual layout banks (including an arbitrary previously installed record
word). The original per-site pattern required input readiness, an output
projection proof, and an outside-image preservation proof. The new application
requires only input readiness: two repeated proof obligations disappear at each
use site. The shared single-output lemma and slot-generation infrastructure are
an upfront cost; this is not a measured reduction in total project tokens.

The cleanup manifest specifies one rewind tape and four clear tapes. The emitted
program is proved equal to the existing twist cleanup. Its full-bank theorem
states that exactly the listed tapes are cleared, the rewind tape retains its
words with its head reset, and every other tape is unchanged. Its cost theorem
uses the original bank's word lengths, including all primitive costs and four
connecting steps. Domain-specific bounds on those word lengths remain manual.
Duplicate slots, out-of-range slots, and rewind/clear overlap are rejected by
the authoring tool; the kernel still verifies the emitted proofs independently.

Validation: six additional Python tests, two actual-bank applications, program
identity proofs, and a transitive axiom audit of 84 declarations passed. Lean
also rejected four corrupted outputs: aliased slots, the wrong output tape,
claiming an untouched tape was cleared, and an underpaid cleanup scan. On the
first successful complete run the generated placement file checked in 2.17
seconds, cleanup in 1.62 seconds, and actual-bank applications plus audit in
3.10 seconds, with a maximum observed peak around 2 GiB. These guarded times
include startup and any lock wait, and do not establish a speedup over manual
proofs. No proof limits were increased.

This extension has a concrete reuse benefit beyond short sequence composition:
single-output placement now needs no per-use frame proof, and rewind/clear
bookkeeping comes from a tape list. Prefer adopting these helpers for the next
new matching adapter before undertaking any broad rewrite. General multi-output
contracts and application-specific asymptotic bounds are still outside scope.

## First section 8 application: recovered output installation

`Machine/RecoverOutputInstall.lean` now uses generated cleanup in a production
library theorem. Its input is an already recovered MSB word in the common word
format on tape one, a blank output tape zero, and two arbitrary word-format
scratch tapes. It copies the bits without the separator, moves the source head
past its separator, and runs the generated three-tape cleanup while preserving
the raw output tape. All work tapes finish blank with zero heads; the output
head finishes immediately after the last bit. The same fixed program covers
empty words.

```sh
python3 scripts/generate_lean_sequence.py scripts/proofgen/recovery_cleanup.json IntegerMultBounds/Schoenhage/RecoveryCleanupGenerated.lean
python3 scripts/check-lean-safe.py --wait-for-lock IntegerMultBounds/Schoenhage/RecoveryCleanupGenerated.lean -o .lake/build/lib/lean/IntegerMultBounds/Schoenhage/RecoveryCleanupGenerated.olean
python3 scripts/check-lean-safe.py --wait-for-lock IntegerMultBounds/Machine/RecoverOutputInstall.lean -o .lake/build/lib/lean/IntegerMultBounds/Machine/RecoverOutputInstall.olean
python3 scripts/check-lean-safe.py --wait-for-lock scripts/proofgen/RecoveryInstallAudit.lean
```

`CertifiedSequence.olean` must already exist (the original pilot verifier builds
it). The production library root imports the installer and therefore also its
generated cleanup and certificate helper; these declarations are covered by the
normal full axiom audit as well as the targeted audit above. The other pilot
modules remain standalone.

`runs_install` proves the whole-bank endpoint with cost three times word length
plus twice the total scratch cell lengths plus 13. `runs_recovered` connects this
execution to the existing coefficient recovery semantics and exact product output
contract, giving six times input length plus scratch cleanup and 13. The generator
handles only the three clear phases and their joins; the raw/word representation
bridge, placement of literal programs, and arithmetic endpoint proof are explicit
Lean proofs. No generator extension was needed for this application.

Physical rounding and carry normalization must still produce the installer input;
this does not prove the full section 8 recovery milestone. The existing numerical
and list-level recovery theorem is not treated as an executable tape operation.

## Shared lemmas with real callers

`Schoenhage/TapeBank.lean` extracts the generic update/placement rules formerly
inside `ScriptMain`. The old public names remain compatible aliases; the layout
writer's `upd_lslot` and `CertifiedPlacement.placed_update` now use the same
rules. `runs_place` accepts any exact local output bank, so multiple changed
tapes are supported without adding another generator mode. Repeated updates
can be simplified with `place_update`, ending with `place_self`.

`clear_fold` turns a list of actual endpoint updates into `cleared slots bank`.
The twist generator now emits an application of this lemma instead of a
per-tape conditional case split; section 8 recovery uses the same rule followed
by `cleared_all`. It states only endpoint equality: duplicate clears are allowed
in that equality, and executable cost proofs must still pay for every clear.
The existing adapter manifest continues rejecting duplicate slots.

`Machine/WordTapeBridge.putWord_blank_origin` packages the exact whole-tape
representation equality previously proved cell by cell in the elementary
multiplier and recovery installer. It supports every alphabet and includes
negative cells and blank tails. A broader raw/word-format compiler remains
deferred: the two verified callers justify this small lemma, not an additional
compiler framework.

The existing programs, theorem statements and cost bounds are unchanged by these
refactors. Build/check the new helper modules before their changed callers using
the guarded runner, then check `scripts/proofgen/ProofReuseAudit.lean` for the
shared lemmas and nine named caller dependencies. The changed production callers
are `Schoenhage/ScriptMain`, `Schoenhage/LayoutGenWrap`,
`Machine/ElementaryMultiply`, and `Machine/RecoverOutputInstall`; the adapter
verifier additionally checks generated cleanup and the certified placement helper.
These are demonstrated code reuse opportunities; token savings remain unmeasured.
