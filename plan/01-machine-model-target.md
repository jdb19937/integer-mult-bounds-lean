# 1. Machine model and target statement (§2)

Part of the [plan](../PLAN.md). See [COMPONENTS.md](../COMPONENTS.md) for what each file proves.

## How the proof goes

Section 1 fixes what is being proved. It defines a literal multi-tape machine model and states the end-to-end target as a Lean proposition, so that every later section ultimately produces facts about runs of such machines; an axiom audit confirms that nothing beyond Lean's standard axioms is used.

1. Machine semantics (`Machine.lean`): a deterministic machine with a finite alphabet and a fixed number of one-dimensional tapes, whose transition sees only the finite state and the scanned symbols, writes at most one cell per tape and moves each head at most one cell per step.
2. Target statement (`Machine.EndToEnd`): there exist a fixed machine and constants, chosen before the input, that multiply every pair of n-bit integers correctly within `O(n (lg n)^(1 - 83/10^12))` steps. It is stated as a proposition to be proved, not assumed.
3. Axiom audit (`AxiomAudit.lean`): the main theorems depend only on `propext`, `Quot.sound` and `Classical.choice`.

## Sub-problems

### Machine model and target statement

Defines the literal multi-tape machine semantics and states the EndToEnd proposition the whole development must prove.

- Math milestone: `IntegerMultBounds.Machine.outputCorrect_wellPosed` — For all n-bit x, y there is exactly one output word of length 2n with binaryValue x*y, so outputCorrect pins tape zero to a unique, always-achievable content and EndToEnd is a meaningful (non-vacuous) target. Combines `Machine.product_fits`, `Machine.binaryValue_lt`.
- Tape milestone: `IntegerMultBounds.Machine.step_semantics` — One step of any literal Program writes only the scanned cell of each tape, moves each head by at most one cell, and its result is determined by the state and the scanned symbols. Combines `Move.unit`, `Machine.step_local`, `Machine.step_head_bound`.

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Multi-tape machine semantics | `Machine.lean` | ✅ | ✅ | Finite alphabet, fixed tapes, local transitions |
| Target proposition `EndToEnd` | `Machine.lean` | ✅ | ✅ | Stated, not proved |

### Axiom audit

Checks that the results rely only on Lean's three standard axioms.

- Math milestone: —
- Tape milestone: —

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Axiom audit | `AxiomAudit.lean` | ✅ | — | Only `propext`, `Quot.sound`, `Classical.choice` |
