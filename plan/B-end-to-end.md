# B. End-to-end theorem `EndToEnd`

Part of the [plan](../PLAN.md). See [COMPONENTS.md](../COMPONENTS.md) for what each file proves.

## How the proof goes

Part B proves `EndToEnd` itself by assembling one fixed machine. The machine parses the literal input, decides between a fast path for large inputs and an ordinary quadratic multiplier for the finitely many small ones, and installs the exact twice-length product. The quadratic fallback is complete; the fast path needs the components of sections 2–9 and the time bound of section 9.

1. Input front end (`MultiplicationInputSplit`): a fixed parser reads the literal input, keeps it, and produces reversed operands in linear time, including empty operands.
2. Quadratic multiplier (`ElementaryMultiplyCore`, `DoubleClockReverseCopy`, `ElementaryMultiplyOutputData`, `ElementaryMultiply`): a fixed four-tape machine computes the Horner accumulator, erases the input, and copies exactly twice-length most-significant-first product bits with an operand clock, halting in quadratic time.
3. Fast assembly (`Assembly`): `EndToEnd` is reduced to exhibiting a program running within a cost of the cost-table shape; correctness on every input length and the uniform `O(n log^(1-83/10^12) n)` runtime remain open.

## Sub-problems

### Literal input front end

Parses the literal input into reversed operands in linear time.

- Math milestone: `IntegerMultBounds.Machine.MultiplicationInputSplit.splits` — The fixed three-tape parser preserves the packed input and produces both reversed operands, halting within 3|x| + 2|y| + 12 steps (consumed by ElementaryMultiplyCore).
- Tape milestone: `IntegerMultBounds.Machine.MultiplicationInputSplit.splits_original_input` — From the literal Machine.input configuration the parser halts within 3|x| + 2|y| + 12 steps with the split output tapes.

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Literal multiplication input front end | `MultiplicationInputSplit` | ✅ | ✅ | The actual fixed parser reads the literal input, retains it and produces reversed operands with linear cost, including empty lists. Multiplication execution and exact-width output installation remain separate. |

### Quadratic fallback multiplier

Proves a fixed four-tape machine outputs the exact twice-length product in quadratic time.

- Math milestone: `IntegerMultBounds.Machine.ElementaryMultiplyOutputData.horner_output_spec` — For equal-length operands (including empty) the MSB word read back from the Horner accumulator has length exactly 2n and binary value x*y. Combines `ElementaryMultiplyOutputData.horner_output_length`, `ElementaryMultiplyOutputData.horner_output_value`.
- Tape milestone: `IntegerMultBounds.Machine.ElementaryMultiply.runsWithin` — The fixed four-tape program halts with the exact twice-length product on tape zero for every equal input length within 40(n^2+n+1) steps (Assembly.RunsWithin).

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Original-input elementary multiplication core | `ElementaryMultiplyCore` | ✅ | ✅ | The actual fixed four-tape core computes the exact accumulator product from original packed input, with genuine halting and quadratic runtime. Fixed-width output installation and the fast branch remain open; this is the ordinary fallback core. |
| Unary word-clock output movement and copying | `DoubleClockReverseCopy` | ✅ | ✅ | Actual fixed-state double seeking and reverse copying perform exactly twice the operand-clock length, preserving operands and producing false bits for blank accumulator padding. Product-specific semantics and final output installation remain separate. |
| ElementaryMultiplyOutputData | `ElementaryMultiplyOutputData` | ✅ | ✅ | Connects literal descending accumulator reads to exactly twice-length MSB product bits, padding blanks as zero. Proves output length and value for the Horner accumulator including empty operands; actual output installation is provided separately. |
| ElementaryMultiply | `ElementaryMultiply` | ✅ | ✅ | One fixed four-tape machine parses original multiplication input, computes the Horner accumulator, physically erases input and copies exactly twice-length MSB product bits using an operand clock. Genuine halting, literal outputCorrect and Assembly.RunsWithin at40 times n squared plus n plus one hold for every equal input length, including zero. This completes the ordinary quadratic fallback; fast-path assembly and the sub-n-log-n bound remain open. |

### Fast program assembly and final bound

Reduces EndToEnd to a program within the cost-table bound and assembles correctness and runtime.

- Math milestone: `IntegerMultBounds.Assembly.mainProgram_runsWithin` — The assembled fixed program (input front end, fast path for large n, quadratic fallback below the cutoff) satisfies RunsWithin with a total cost of the cost-table shape.
- Tape milestone: `IntegerMultBounds.Assembly.endToEnd` — Machine.EndToEnd: one fixed literal machine multiplies every pair of n-bit integers correctly within O(n (lg n)^(1 - 83/10^12)) steps (via endToEnd_of_table).

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Explicit multiplication program | `ElementaryMultiply` | 🟡 | 🟡 | Complete ordinary quadratic fallback is proved; fast program assembly and target bound remain open. |
| Correctness on every input length | — | ⬜ | ⬜ | Requires §2–§8 and part A |
| Uniform runtime `O(n log^(1−83/10¹²) n)` | `Assembly` | 🟡 | ⬜ | `EndToEnd` reduced to a program running within a cost of the cost-table shape |
