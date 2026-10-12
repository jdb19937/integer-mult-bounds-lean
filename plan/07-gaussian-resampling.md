# 7. Gaussian resampling (§7)

Part of the [plan](../PLAN.md). See [COMPONENTS.md](../COMPONENTS.md) for what each file proves.

## How the proof goes

Section 7 changes transform lengths by Gaussian resampling: a length-`s` DFT is written as `2^γ B F_t A` with a length-`t` DFT in the middle and contractions `A`, `B`, so the main recursion can work at convenient sizes. The mathematics proves this factorization and its numerical approximations; the tape part builds fixed machines that evaluate the numerical maps on fixed-point words and applies them along tensor axes within the cost table.

1. Exact resampling (`Gaussian`, `Resampling`, `ResamplingNorm`, `ResamplingInverse`, `ResamplingMulti`): Poisson summation gives the resampling identity (Thm 4.2), `‖S‖ ≤ 1 + 1/α` (Lemma 4.5), and a Neumann-series inverse of `T` (Lemma 4.6), assembling `F_s = 2^γ B F_t A` with `‖A‖, ‖B‖ ≤ 1` in one and `d` dimensions.
2. Numerical maps (`ResamplingApprox`, `NeumannHalved`, `ResamplingNumeric`, `ResamplingPermuted`, `ResamplingManuscript`): truncated Gaussian windows and a finite, clamp-free Neumann iteration give explicit `Ã` and `B̃₀ = D̃' J̃' C` with scaled error below `p²` per coordinate, including the permutation-left variant the main proof uses.
3. Word layer (`TwosComplement`, `FixedMul`, `RecordTape`, `PairJoin`): signed fixed-point words, sign-extending accumulation, negation, truncating multiplication via the fast multiplier, and record-tape plumbing.
4. Weights (`PiApprox`, `ExpApprox`, `WeightTable`, `TabATape`, ...): integer weight tables within two units of the scaled Gaussian weights are computed on tapes from Machin's `π` and a Taylor `exp`.
5. Maps on tapes (`RowSelect`, `GaussianLine`, `OffDiagSum`, `NeumannLoop`, `B0Tape`): the row selection `C`, the window sums of `Ã`, the off-diagonal `Ẽ`, `p` Neumann steps for `J̃'` and the assembled `B̃₀` run as fixed machines whose outputs equal the numerical maps exactly.
6. Tensor interface (`LineCost`, `LineApply`, `LineValue`): applying the one-dimensional maps along every axis costs what the cost table allows (Lemma 7.2), with negligible per-line setup.

## Sub-problems

### Exact Gaussian resampling factorization

Proves F_s = 2^γ B F_t A with contractions A, B in one and d dimensions via Poisson summation and a Neumann inverse.

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Gaussian sums and Poisson summation | `Gaussian` | ✅ | — | |
| Resampling identity (Thm 4.2) | `Resampling`, `ResamplingCLM` | ✅ | — | |
| Norm bound on `S` (Lemma 4.5) | `ResamplingNorm` | ✅ | — | `‖S‖ ≤ 1 + 1/α` |
| Inversion of `T` (Lemma 4.6, Prop 4.7(i)) | `ResamplingInverse`, `ResamplingAssembly`, `Neumann` | ✅ | — | `F_s = 2^γ B F_t A`, `‖A‖, ‖B‖ ≤ 1` |
| `d`-dimensional resampling (Thm 4.1) | `ResamplingMulti` | ✅ | — | |

### Numerical resampling maps and error bounds

Gives explicit truncated maps Ã and B̃₀ with scaled error below p², including the permutation-left variant.

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Truncation and Neumann errors (Lemmas 4.8–4.12) | `ResamplingApprox`, `OffDiagApprox`, `OffDiagApproxSqrt`, `NeumannApprox`, `NeumannHalved` | ✅ | — | Square-root windows as in the paper; the manuscript's clamp-free form (halve the input, `‖E‖ ≤ 0.46`, iterates stay in the unit disk) gives `B̃₀ = D̃' J̃' C` with error `24m + 27 < p²` and no clamp (`NeumannHalved`) |
| Numerical `Ã`, `B̃` (Prop 4.7(ii)) | `ResamplingNumeric`, `ResamplingMultiNumeric`, `ExplicitNumeric` | ✅ | — | Explicit maps with error below `p²` in one dimension and `d p²` in `d`, no side conditions; on tapes, the window sums of `Ã` are computed by a fixed twenty-two-tape machine over blank-separated fixed-point words (`GaussianLine`) given the rounded weights as a word tape, and its accumulator words are proved to be `2^(p+1)` times the parts of `resampANum` (`WindowSum.accumulators_eq`); run with stride one and a zero centre weight the same machine computes the off-diagonal map `Ẽ` of the Neumann iteration, its accumulators being `2^p` times the parts of `offDiagNum` (`OffDiagSum.accumulators_eq`); the Neumann recursion on words (cyclic extension, stride-one window sums, truncate, negate, add the halved input) is proved to give `J̃'` exactly (`NeumannWords.resampJNumH_eq_iter`); the weight evaluation and the tape loop of `B̃₀` remain open; the tape target for `B̃₀` is the clamp-free `resampB₀NumH` |
| Permutation-left variant | `ResamplingPermuted`, `ResamplingPermutedNumeric`, `ResamplingManuscript` | ✅ | — | `P_s F_s = 2^γ B₀ P_t F_t A` in one and `d` dimensions with explicit clamped `Ã`, `B̃₀` of error below `p²` per coordinate; with the manuscript's unclamped maps (`ResamplingManuscript.permuted_numeric_manuscript`: for `α ≥ 2`, `‖A‖ ≤ 3/4`, so `Ã` and the clamp-free `B̃₀` approximate with errors below `p²` and map the unit disk to itself); weighted chirp for the retained frequency permutation; source permutation cancels in convolutions; the row-selecting map `C` is realized on tapes: with the constants `2s`, `2t`, `2t−s−1` the modular-counter selection machine copies exactly the records at `[tj/s]` in order, at the input volume plus `O(log t)` per record and with no numerical error; the numerical maps on tapes remain open; a signed fixed-point word layer on tapes (two's complement add, negate, truncating multiply `FixedMul`) is in place for the numerical maps, with the multiplication cost still quadratic |

### Fixed-point word and record layer

Provides signed fixed-point arithmetic and record manipulation on tapes for the resampling machines.

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Signed fixed-point word layer | `TwosComplement`, `SignExtendAdd`, `Negate`, `RulerAdvance`, `RulerCopy`, `FixedMul`, `FixedMulValue`, `Schoenhage/FixedMulPlaced` | ✅ | ✅ | Two's complement add into a wider accumulator, negate, and truncating multiply with `signed_result`; on tapes the multiply is `Schoenhage.fastMul`, `O(w log w log log w)` steps, used by `GaussianLineFast`, `NeumannLoopFast`, `B0TapeFast` and `LineApplyFast` |
| Record-tape plumbing | `RecordTape`, `RecordRewind`, `RecordCopy`, `PairJoin` | ✅ | ✅ | Rewind, erase, copy and skip blank-separated records; join and split complex records around `RowSelect` |

### Gaussian weight tables on tapes

Computes integer weight tables within two units of the scaled weights from π and exp on tapes.

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Weight evaluation | `PiApprox`, `ExpApprox`, `WeightTable`, `WeightNat`, `PiNat`, `PiTape`, `ExpTape`, `TableIdx`, `TabATape`, `TabETape`, `TabDTape`, `TableValue` | ✅ | ✅ | Integer tables within 2 units of `2^p` times the weights (`tables_ok`), from Machin's `π` and a Taylor `exp` in fixed point; register machines compute `π`, `exp` and the A, E, D and halving tables as `w`-bit word tapes (D and halving negated); `TableValue.a_tables` and `b0_tables` feed these words to the `Ã` window sums and the `B̃₀` machine with the tables of `tables_ok` |

### Resampling maps on tapes

Runs C, Ã, Ẽ, the Neumann loop and B̃₀ as fixed machines whose outputs equal the numerical maps.

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Row-selecting map `C` on tapes | `OrderedSelect`, `RowSelect` | ✅ | ✅ | Modular-counter selection machine copies exactly the records at `[tj/s]` in order, at the input volume plus `O(log t)` per record, with no numerical error |
| Gaussian window sums of `Ã` | `GaussianLine`, `GaussianLineValue`, `WindowSum` | ✅ | ✅ | Fixed twenty-two-tape machine; its accumulators are `2^(p+1)` times the parts of `resampANum` (`WindowSum.accumulators_eq`); rounded weights are supplied as a word tape |
| Off-diagonal map `Ẽ` | `OffDiagSum` | ✅ | ✅ | The same machine with stride one and a zero centre weight; accumulators are `2^p` times the parts of `offDiagNum` |
| Neumann iteration `J̃'` | `NeumannWords`, `SubPass`, `NeumannStepLemmas`, `NeumannLoop` | ✅ | ✅ | Word-level recursion gives `J̃'` exactly (`resampJNumH_eq_iter`); the twenty-seven-tape loop runs `p` steps around the Gaussian line machine (`loop_hoare`) |
| Assembled `B̃₀ = D̃' J̃' C` on tapes | `B0Words`, `B0Tape`, `B0Value` | ✅ | ✅ | Forty-two-tape machine: join, select, split, halve (one window-radius-zero step with weights `-2^(p-1)`), copy to the start tape, `p` Neumann steps, then `D̃'` (weights `-ρ(2^p d')`); runtime `b0Bound`; `b0_value` identifies its output words with the numerators of `resampB₀NumH p (⌊√p⌋+1) s t α w`; weight tables come from the table machines (`TableValue.b0_tables`) |

### Tensor interface line costs

Applies the one-dimensional maps along each axis within the cost-table budget.

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Tensor interface line counts (Lemma 7.2 costs) | `LineCost`, `LineApply`, `LineValue` | ✅ | 🟡 | Linewise sums give `d C T X`, the Gaussian row times `T p`; at most `2 d T / r` lines; polynomial setup per line is `o(T p)`. On tapes, the innermost axis is done: a twenty-nine-tape loop applies `Ã` to each of `L` consecutive lines (`LineApply.loop_hoare`) and line `ℓ`'s output words are its `Ã` numerators with the machine-built weights (`line_value`); each line costs at most `lineBound`, linear in the extended line `2(s+2m+1)(W+1)` plus `t` window passes of the line machine, so `L` lines cost `L (lineBound + 2)`; the other axes live in the paper's padded box (every `tᵢ ∈ {r/2, r}`), so exposing an axis needs only equal or adjacent binary-width interchanges, which `BinaryInterchangeRun.runs` covers. Open on tapes: the bridge between record tapes and the interchange's bit array, padded-line versions of the line loops, the axis driver over `d` axes, and the cost charge |
