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

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Multi-tape machine semantics | `Machine.lean` | ✅ | ✅ | Finite alphabet, fixed tapes, local transitions |
| Target proposition `EndToEnd` | `Machine.lean` | ✅ | ✅ | Stated, not proved |

### Axiom audit

Checks that the results rely only on Lean's three standard axioms.

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Axiom audit | `AxiomAudit.lean` | ✅ | — | Only `propext`, `Quot.sound`, `Classical.choice` |
