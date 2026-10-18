# T16 in the layer machine: integration plan

Goal: the main theorem runs the selected T16 complex supplier in the layer machine. Together with
the PR589 bit supplier (`M6/DESIGN.md`), it then retunes `mulInTime` to about `2^-10.8` with
rank-one T16 children, or about `2^-10.4` with variable-rank children.

## (a) What Kenny's T16 work provides

All of this is checked, with standard axioms, in `Networks/Certificates/T16/`.

- **Node program.** `Impl/MachineFit.fittedProgram : List (MInstr NodeUnit)` lists the node's
  instructions, with `NodeUnit = Fin 14336 ⊕ Fin 8` (14,336 data families and 8 private
  centres). Each instruction is a rational gate or `prim w p` with
  `p : MPrim ∈ {factor q v, trans v, xor i j, phase i c, unit c}`.
- **Correctness.** `fittedProgram_cAll`: for arbitrary dirty inputs `y`, every family
  `streamUnit r a i` (`r < 16`, `a < 112`, `i < 8`) ends as `ρ cAll (y _)`, for every
  representation `ρ` of the 73-bit operators. The centres are dirty scratch: their inputs are
  arbitrary and their outputs unspecified.
- **Child calls.** `fittedProgram_children`: exactly `F = 1,041,408` odd kernels
  (`factor q v`, `q` odd), all of rank one.
- **Gates.** `fittedProgram_half`: every gate is half-integral.
- **Moments.** `Layer/SelectedMoments` gives the variable-rank bill at `a = 7/4178`;
  `Layer/VariableRecurrence.t16_variable_closed` is the closed recurrence for it.
- **Machine primitives already on the tape.**
  - Translations: `Node/Translate.transW`, which needs no child calls. It is two compact basis
    changes plus two reversals (`Layer/Reverse`).
  - Unit scalars: `mulIW`.
  - Slot XORs: `compactBasisW fw w x` with `w = e_j` at slot `x = i` is the transvection
    `x_j ← x_j + x_i`, and `Cost/CompactBasis` already prices it.

## (b) What remains

1. **Slot phases.** `phase i c`, multiplying each record with address bit `x_i = 1` by `i^c`,
   needs a tape pass: a stride counter over the record order, the shape of `mulIW`.
2. **Private centres.** The 8 centres become node-private array registers, kept out of `NWire`,
   so `NW = 14336`. Dirty inputs are allowed, so no zeroing is needed. Only space grows, by a
   factor of `14344/14336`.
3. **Layer instruction set.** Extend `Layer.Instr` with `trans`, `xor`, `phase` and `unit`, and
   `execWith` with their semantics. Convert `fittedProgram` to `Layer.Instr` over the families,
   with centres as private registers. Prove the node theorem from `fittedProgram_cAll`, with `ρ`
   the column representation on `Arrays m k`: the node applies `cAll` (the full frame at
   `m = 73`) on every wire.
4. **Retarget `m = 25³ → 73`.**
   - `Layer.m` is one `abbrev`. About 22 files use its value. Almost all of these only need
     `0 < m`, `1 < m` or `2 ≤ m`, which still hold.
   - Real edits: `MatchSynLoop` (`m^5` literal), `Branching` (`= 15625`), `CompactBasis` and
     `LayerCostNat`.
   - `NWire`, `program`, `Directions`, `factorCount` and `gateCount` switch to the T16 data:
     `NW = 14336`, `F = 1,041,408`, a fixed program with no direction choice.
   - The `Node/Body` dispatch gains the four new kinds.
5. **Cost chain.**
   - The uniform branching `F/NW < m^σ` stays: `1041408/14336 = 72.643 < 73^σ` with
     `1 − σ ≈ 1.1431e-3`. `Parameters.sigma` becomes that value, rounded down to a clean
     rational.
   - The non-child instructions form a fixed finite list, so they enter as the existing
     per-node gate overhead.
   - `Cost/Branching`, `Cost/BranchingMoment`, `CompactLayerBound` and `ComplexPhaseBudget` are
     re-instantiated.
6. **Variable-rank children (optional, +0.4 bits).** Batched `C^r` children via
   `t16_variable_closed` need per-occurrence child sizes in the layer machine. This is a separate
   stage after the uniform route.

## (c) κ with both selected suppliers

PR589 gives `τ` just above `1 − 10/5769`, so `a_b ≈ 1.7334e-3`; `ε = 31/64`.

| T16 children | `a_c` | binding margin | κ |
| --- | --- | --- | --- |
| rank one (uniform), `c = 7/8` | `1.1431e-3` | layer `ε(1−λ') < 5.531e-4` | about `2^-10.82` |
| variable rank, `c = 7/8` | `1.6755e-3` | layout `εc·a_b = 7.347e-4` | about `2^-10.41` |
| variable rank, `c = 15/16` | `1.6755e-3` | layout `εc·a_b = 7.872e-4` | about `2^-10.31` |

The CRT margin `(1−ε)a_b = 8.938e-4` and the others don't bind. With uniform T16, `σ > τ`, so
`λ` sits just above `σ`, and `1 − λ' < a_c(1 − β)`, with `β = 1/1000` from the leaf exponent.

## (d) Stages

| stage | content | estimate |
| --- | --- | --- |
| T0 | `Layer.Instr` extension, T16 program conversion, node semantics at `m = 73` from `fittedProgram_cAll` (new files) | 1–2 weeks |
| T1 | slot-phase pass, slot XOR wrapper over `compactBasisW`, private centre registers | 2–4 weeks |
| T2 | retarget `m` and switch `NWire` and `program` through `Layer/*`, `Node/*` and the cost files | 3–6 weeks |
| T3 | cost chain: `σ`, branching bound, margins; retune with PR589's `τ` to about `2^-10.8` | 1–2 weeks after PR589 |
| T4 | variable-rank T16 children (+0.4 bits) | 1–3 months |

Kenny is active in exactly this area, on T1-type primitives and the `m` retarget. Upstream is
merged before every stage.

## Status

**T0: checked** (`M6/T16Node.lean`, standard axioms).
- `cAll_eq_frame`: `C_all = frame weightPhase`.
- `colRep k`: the column representation, a monoid homomorphism.
- `colRep_kernel`: `colRep k (kernel q v) = vectorFactor k (q, v)`, so every T16 child is the
  layer machine's factor.
- `family_streamUnit`: every data family is a stream unit.
- `fitted_fullFrame`: on `k`-column banks the fitted program applies
  `frameEquiv k weightPhase` to every data family, for arbitrary centre contents.

**T1: slot phase on the tape, checked** (`Node/SlotPhase.lean`).
- `maskPass_exec`: `signPass` generalized to any slot vector, constant `c` and wire.
- `slotPhase_exec`: the slot phase `i^(c x_x)` as one pass, giving
  `phaseZ (signMask actMap e_x) c`.

**T1: checked** (`M6/T16Arr.lean`, `Layer/ZeroFill.lean`, standard axioms).
- Column operators: `tensorColumns_pullOp` (a pull-back in every column is `pullCols`), with
  `kernel_two` and `translation_eq_pullOp`; `tensorColumns_diag`; `tensorColumns_unit` (the unit
  `i^c` in every column is `i^(c k)`).
- Tape passes after decoding: `view_pullMH` (change of basis), `view_phaseZ_slot` (slot phase),
  `view_unitZ`. `view_tapeZ`: every primitive without a child call (`factor 0` and `factor 2`,
  `trans`, `xor`, `phase`, `unit`) is, after decoding, `liftRep` of its operator. Children are
  `vectorFactor` by `colRep_kernel`.
- `liftRep` and `fittedArr_cfull`: on decoded arrays the fitted program sends every data family
  to `Cfull` (the conclusion form of `NodeArr.nodeA_correct`), for any centre contents.
- Centres on the tape: `zeroFill_exec` writes the zero array of a wire's shape onto a centre
  register, keeping the source. This needs alphabet `A ≥ 77`. `uclear` clears a centre at node
  exit.

T2 instantiates these at `m = 73` (`pullMH = NodeZ.pullM`), sets `NWire := Fin 14336` with eight
centre registers, and builds the T16 node body: split, zero-fill the centres, the program with
the five primitive passes plus the child calls, clear the centres, merge.

## κ with rank-one T16 and bit-side fallbacks

`ε = 31/64`, `β = 1/1000`, rank-one `a_c = 1.1431e-3`. The layer margin is
`ε · min(a_b, (1 − β) a_c)`, the layout margin `ε c a_b`, the exposure margin `(1 − ε) a_b`.

| bit saving `a_b` | κ at `c = 7/8` | κ at `c = 15/16` | binding |
| --- | --- | --- | --- |
| today's `2.96e-9` | `2^-29.57` | `2^-29.47` | layout |
| `1e-4` | `2^-14.53` | `2^-14.43` | layout |
| `5e-4` | `2^-12.20` | `2^-12.10` | layout |
| `1.7334e-3` (PR589) | `2^-10.82` | `2^-10.82` | layer |
