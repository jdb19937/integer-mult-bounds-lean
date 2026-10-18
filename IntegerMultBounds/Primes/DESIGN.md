# The prime moduli

The transform needs `d` pairwise coprime source lengths `s_i` in windows of relative width
`η = 1/(4d)` below the axis lengths `t_i`. The source lengths are primes: the first `numHalf`
primes above `(1 - 2η) r/2` and the first `d - numHalf` primes above `(1 - 2η) r`. This note
describes their supply, the machine that finds them and their place in the parameter chain.

## (a) Why primes

The elementary moduli of `MathlibTM2/Mult/Moduli.lean` (`oddProd d = ∏_{i<2d} (2i+1)`, the
progressions `N(x₀ + 2i) + 1` and `N(2x₀ + 1 + 2j) + 2`, `src_good_oddProd`) need the room
`8 d² N + 4d ≤ 2^(ℓ-1)` with `N ≤ (4d)^(2d)`. That forces `ℓ ≳ 2d log₂(4d)`, and with
`dℓ ≈ log₂ T ≈ b` it means `d² log d ≲ b`, i.e. `ε < 1/2`.

Primes need no room condition. The window `((1 - 2η) t, (1 - η) t]` holds at least `d`
primes once `d ≤ (log₂ t)^B` for a fixed `B` (strong prime number theorem), and at the sizes
`d ≤ p^ε`, `ℓ ≥ p/(12d)` give `d ≤ (12ℓ)^(ε/(1-ε))`. Any `ε < 1` works with `B > ε/(1-ε)`.
**With primes the moduli constrain `ε` only by `ε < 1`.** The Gaussian arithmetic (`B̃₀`, Kenny's
M7) still does: its exposure margin is `1/2 - δ - ε(1 + c₀/2)` (`MathlibTM2/NearOne/DESIGN.md`).

## (b) The supply

* `Primes/ShortInterval.lean`: `primes_in_window (B)`, eventually in `t`, every
  `d ≤ (log t)^B` has at least `d` primes in `(⌊(1 - 1/(2d)) t⌋₊, ⌊(1 - 1/(4d)) t⌋₊]`;
  `primes_in_window_two_pow` at `t = 2^ℓ`. From the vendored strong prime number theorem.
* `Primes/Window.lean`: `window_card_two_pow`, `windowPrime_two_pow`.
* `Primes/WindowLo.lean`: the window ends in integer arithmetic, `winLo d t = t - ⌈t/(2d)⌉`,
  `winHi d t = t - ⌈t/(4d)⌉`, their real floors, and `axisBounds_of_mem`.
* `Primes/NextPrime.lean`: `nextPrimeAfter`, `windowPrime lo k = nextPrimeAfter^[k+1] lo`, and
  `windowPrime_mem`: with `d` primes in `(lo, hi]` the first `d` outputs are window primes.
* `Primes/Moduli.lean`: `primeSrc d a R i`, the first `a` primes above `winLo d R`, then the
  first `d - a` above `winLo d (2R)`; `primeSrc_good`: with enough primes in both windows,
  `Moduli.Good (primeSrc …) (Moduli.box d a e)` at `R = 2^e`, `e ≥ 3`.
* `Primes/SizeFacts.lean`: `eventually_le_pow_pred`, the bound `d ≤ (ℓ - 1)^(M'+1)` for any
  sizing with `d^M ≤ b^M'`, `M' < M`, `b ≤ C d ℓ`; this is the supply hypothesis at every
  `ε < 1`.

**At the sizes** (`Mult/Sizes.lean`):

* `PrimeSupply n`: `d ≥ 2`, `ℓ ≥ 4`, and both windows, below `R = 2^(ℓ-1)` and below `2R`,
  hold at least `d` primes. `eventually_primeSupply` proves it for all large `n` from
  `d ≤ 2ℓ ≤ (ℓ - 1)²` and `window_card_two_pow 2`.
* `srcLen n i` is `primeSrc (d n) (numHalf n) R i` under `PrimeSupply n` and `windowPrime 2 i`
  otherwise, so `s n` is pairwise coprime and positive for every `n` (`s_pairwise_coprime`,
  `srcLen_prime`, `three_le_srcLen`); the CRT maps of the pipeline take these as arguments.
* The threshold of `eventually_primeSupply` is existential. The prime supply is one of the
  regime facts `BigFacts`; `bigDim` is `d` at their common threshold plus one, and `Big n` is
  `2 ≤ n ∧ 2^192 + bigDim ≤ d n`. Since `d` is monotone (`d_mono`), `Big n` gives
  `PrimeSupply n` (`Big.primeSupply`), so `Big.good`, `Big.srcLen_eq` and every other `Big.*` fact
  stay deterministic.

## (c) The machine

All registers are TableVM words of `W ≥ 4b + 32` bits (`pmW`).

**Primality by trial division**, `ptPrimeC : TblCode 7` (`Primes/PrimeTest.lean`).

* `one := 1; x1 := x + 1; y := 2; sq := 4; f := [2 ≤ x]`, then
  `while sq < x1 do (r := x mod y; if r < 1 then f := 0; y := y + 1; sq := y·y)`.
* The loop runs `sqrt x - 1` times, with no early exit; afterwards `f = 1 ↔ x.Prime`.
* Atoms `ptPrimeAtoms x = 13 + 7 (sqrt x - 1)`; words `3x + 4 < 2^W`.

**Next prime**, `ptNextC : TblCode 7`: `f := 0; one := 1; while f < one do (x := x + 1;
ptPrimeC)`. It ends at `nextPrimeAfter x₀` within `ptNextAtoms x₀` atoms.

**The packed source lengths** (`Primes/Pack.lean`). The readers of the source lengths (the
axis loop of `Fast/DistAxis.lean`, the CRT loop of `Fast/DistCrt.lean`) visit the axes in order
and recompute `s_i` at each one; a search per visit would repeat the whole search `d` times. The
parameter table therefore keeps all `d` primes in one word, the mixed-radix value
`packVal s t d = Σ_{i<d} s_i P_i` with `P_i = ∏_{j<i} t_j`. It is below `T`, and every digit is
`(packVal / P_i) mod t_i` (`packVal_digit`), two atoms for a reader that holds `P_i` and `t_i`.

* `ptRunC`: `m` times `ptNextC`, adding `x · P` to the value and multiplying the weight `P` by
  the radix.
* `ptPackC`: `x := winLo d R`, a run of `a` primes with radix `R`, `x := winLo d (2R)`
  (`winLoC`, seven atoms), a run of `d - a` primes with radix `2R`. `ptPackC_do`: the result is
  `packVal (primeSrc d a R) (pmTv a R (2R)) d`, within `ptPackAtoms d a R ≤ 100 (d + 1) 4^ℓ`
  atoms (`ptPackAtoms_le`).
* `ptProdPC`: the product of the digits, `9d + 7` atoms. `ptEmitPC`: the emission of the
  digits in the format of the parameter program, `9d + 5` atoms.
* `SourcePrimes.lean` also holds `ptSrcC`, which emits the primes directly from two window
  searches. It needs ten scratch registers, one more than the nine free variables of the
  parameter table at `pmCode2`, and it does not serve the readers, so the parameter program does
  not use it.

**Cost.** The search is `O(d 4^ℓ)` atoms, times `tblC W W = O(b²)` host steps per atom, which
outgrows every power of `log n`. Under `Big`, `8ℓ ≤ b`, and `Big.search_cost_le` gives
`2^18 (b + 6)^3 4^ℓ ≤ n`: the search costs at most `n` host steps.

## (d) The parameter chain

| file | role |
| --- | --- |
| `Mult/Sizes.lean` | `PrimeSupply`, `eventually_primeSupply`, `BigFacts`, `bigDim`, `srcLen`, `s`, `Big`, `Big.primeSupply`, `Big.srcLen_eq`, `Big.good` |
| `Mult/Pipeline.lean`, `Mult/BandSpec.lean` | `s_pairwise`, `neZero_s` from the primes |
| `Fast/ParamProg.lean` | variable 16 is `winLo d R` (`winLoC`, stage 16); variable 17 is the packed source lengths (`ptPackC`, stage 17, `pmSearchAtoms n` atoms); variable 18 is `S` (`ptProdPC`); `pmCode2` emits the digits (`ptEmitPC`); `pmAtoms1 n ≤ 2500 (b + 1)² + pmSearchAtoms n` |
| `Fast/ParamMath.lean` | `pm_S_prod`, `pm_S_lt` from `S < T` |
| `Fast/ParamMachine.lean` | `pmCost_le` for `Big n`: `17 n + 2^23 (size n + 5)^4 + pmUnaryCost` |
| `Cost/MatchParam.lean`, `Fast/DistMain.lean` | `mt_pm_le`, `mt_pm_le_real` for `Big n`; `dsAll_cost_le` adds `eventually_big`. The bounds keep their constants. |
| `Fast/DistAxis.lean` | `dsS n i = srcLen n i`; the axis code reads `s_i = (v₁₇ / P_i) mod t_i` |
| `Fast/DistCrt.lean` | the CRT axis code reads `s_j` the same way, with `t_j` by `j < numHalf` |
| `Fast/DistWidth.lean` | `dsS_le` from `s_i < t_i ≤ r` |

The elementary moduli of `Mult/Moduli.lean` and their programs in `Fast/ParamSub.lean`
(`pmOddC`, `pmStartC`, `pmModC`, `pmProdSC`, `pmEmitSC`) stay in the library and leave the main
route.

## (e) Status

| stage | content | status |
| --- | --- | --- |
| 1 | `NextPrime.lean`: `nextPrimeAfter`, `windowPrime`, enumeration and window lemmas | checked |
| 2 | `PrimeTest.lean`: `ptPrimeC`, `ptNextC` with correctness and atom counts | checked |
| 3 | `WindowEmit.lean`, `Window.lean`: emission of window primes, membership below `2^ℓ` | checked |
| 3b | `WindowLo.lean`, `Moduli.lean`, `SourcePrimes.lean`: window ends, `primeSrc`, `winLoC`, `ptSrcC` | checked |
| 4 | `primeSrc_good`; `SizeFacts.lean`: `eventually_le_pow_pred`, `Big.search_cost_le` | checked |
| 5 | `Pack.lean` and the parameter chain of (d) | integrated |

All files use the standard axioms only.
