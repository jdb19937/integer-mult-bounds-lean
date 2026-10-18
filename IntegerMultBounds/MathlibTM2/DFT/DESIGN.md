# The prime-field DFT below `n log n`: machine design

Target: `dft_in_time : DFTStatement` (`DFT/Statement.lean`, Mathlib imports only), from a host
multiplier with `time n = O(n (log n) ^ (1 - κ))`. The transform inherits the exponent `κ` of
the multiplier.

## Sizes

An instance is `p`, `ω`, `a 0, …, a (n - 1)`. Write `w = Nat.size p`. The input has length
`N = (n + 2) (w + 1)`. For `n ≥ 1`, `ω` has order `n` in `(ZMod p)ˣ`, so `n ∣ p - 1`, `n < p`
and `Nat.size n ≤ w`. Every size below is `O(w)` per scalar and `O(N)` for the one big product.

* Reciprocal precision `r = 2 w`: `recip_exec` returns `μ = ⌊2 ^ (k' + w) / p⌋` with
  `2 w < k' ≤ 4 w`, so every value below `2 ^ (3w + 1)` reduces by Barrett's method.
* Kronecker base `B = 2 ^ s`, `s = 3 w`, so `n (p - 1) ^ 2 < 2 ^ w · 2 ^ (2w) = B` (the
  hypothesis `hB` of `fastDFT_transform`).
* The product has two factors of `(n + 1) s` and `2 n s` bits: input length at most
  `(3 n + 1) s + 2 ≤ 9 N + 2`.

Small cases need no separate code: for `n = 0` every loop runs zero rounds and nothing is
printed. Since `p` is prime, `2 ^ (w - 1) ≤ p < 2 ^ w` with `w ≥ 2` normalizes the divisor of
the reciprocal.

## The arithmetic (`DFT/Algorithm.lean`, proved)

* `chirp_identity`: `ω' ω = 1 → ω' ^ C(k,2) (ω' ^ C(j,2) ω ^ C(j+k,2)) = ω ^ (j k)`, from
  `choose_two_add`. No square root of `ω` and no division by 2.
* `pack B u n = ∑ i < n, u i B ^ i`; `pack_mul` (product of packs is the pack of `conv`);
  `pack_div_pow_mod` (digit read-back when all digits are `< B`); `conv_le` (digits at most
  `n c ^ 2`); `conv_reflect` (digit `n - 1 + k` of reversed-input times chirp is the
  correlation `∑ j < n, u j v (j + k)`).
* `packProduct_digit`, `correlation_cast`: the same for arbitrary representatives.
* `fastDFT p ω n B a k`: the whole computation on naturals with `% p` reductions;
  `fastDFT_cast` (equal to `dft` in `ZMod p` when `ω ^ n = 1`, `n (p-1)^2 < B`),
  `fastDFT_eq_val`, `fastDFT_transform` (equal to `DFTInstance.transform` on an instance).

## Reduction (`DFT/Reduction.lean`, proved)

* `redc p R p' t`: Montgomery's REDC; for `R ∣ p p' + 1` and `t < p R`, `redc_lt` (below `p`)
  and `redc_cast` (`redc t · R = t` in `ZMod p`).
* `henselStep`, `henselInv`: `-p⁻¹` modulo `2 ^ (2 ^ i)` by `y ↦ y (2 + p y)`;
  `henselInv_dvd`, `montInv_dvd` (the Montgomery constant for `R = 2 ^ r`, `r ≤ 2 ^ i`).
* `barrett_le`, `barrett_lt`, `barrett_mod`: Barrett reduction with `μ = ⌊4 ^ w / p⌋`.

The machine reduces with Barrett's method (`barrett2_le`, `barrett2_lt` in `DFT/Newton.lean`:
for `μ = ⌊2 ^ s / p⌋` and `x < 2 ^ s`, `q = ⌊x μ / 2 ^ s⌋` has `q p ≤ x < q p + 2 p`, so one
conditional subtraction finishes). All register values are plain residues below `p`; they enter
through `packProduct_digit` (any digits `≤ p - 1`) and `correlation_cast` (with `c₁ = c₂ = 1`),
and the printed value is the unique representative below `p`. REDC, the Hensel inverse and
`montMul` (§5) are proved and unused by the pipeline.

## Machine layers

All host code uses Kenny's structured stack language (`Stack.lean`: `Prog`, `Exec` with exact
step counts, `Prog.machine`, `Exec.toOutputs`) and the host register file (`Host/Core.lean`:
keys `HK T`, alphabets `HΓ A`, local state `HS T Q A U`, binary registers `binSyms L x`, least
significant bit on top).

### 1. Keys with `Γ'` stacks (`DFT/Keys.lean`, proved)

The host keys `.inp`, `.out` have alphabets `Bool ⊕ Bool` and `Bool`, so no host machine can
read or write `Γ'`. The DFT machine runs over

```
inductive DK (K : Type) | gin | gout | host (k : K)
abbrev DΓ (Γ : K → Type) : DK K → Type   -- gin, gout ↦ Γ'; host k ↦ Γ k
```

with `K = HK T`, `Γ = HΓ A` (`DecidableEq` derived, `Fintype` through `Bool ⊕ K`).

* `hostProg ι : Prog P Γ σ → Prog P' (DΓ Γ) σ` maps every key `k` to `.host k` (no casts) and
  every call `f` to `ι f`. `hostExt s gi go` is the host store `s` with `gi` on `gin` and `go`
  on `gout`; `hostExt_res` writes every store over `DK K` this way.
* `exec_hostProg`: if `body' (ι f) = hostProg ι (body f)` for every `f`, then
  `Exec body p s n t` gives `Exec body' (hostProg ι p) (hostExt s gi go) n (hostExt t gi go)`.
  `hostCode p` (`P = Empty`, `exec_hostCode`) runs a host program without calls in any table:
  every library procedure of `Host/*` is used this way.

### 2. Top level (`DFT/Keys.lean`, `DFT/Top.lean`, proved)

`computableInTime` builds `TM2ComputableInTime ea eb f` from `Stack.machine body main .gin .gout
σ₀` (input and output alphabets `Equiv.refl Γ'`) and `ComputesWithin`: for every `a`, an
execution of `main` from `Store.only σ₀ .gin (ea a)` to `Store.only σ₀ .gout (eb (f a))` in `m`
steps with `m + 2 ≤ time |ea a|`. `dftInTime_of_computes` adds the bound
`time =O N (log N) ^ (1 - κ)` and gives `DFTInTime κ`. The time function is a monotone
majorant of the step bound over all instances of length `N`.

`.main` is `parse ; pipeline ; print`, ending with a `load` of `σ₀`.

### 3. Parsing and printing (`DFT/IO.lean`, `DFT/Fields.lean`, `DFT/Parse.lean`, proved)

Lists of numbers live on one register with a `separator` after each number: `fieldSyms w l`
(each `binSyms w x`, least significant bit on top) and `natSyms l` (each in shortest form).

* `readIn r` / `writeOut r`: `gin` onto register `r` and register `r` onto `gout`, one symbol per
  two steps, coding `Γ'` bits as `bitSymbol` and the comma as `separator` (`gamCode`,
  `gamDecode`). `encodeFixedList_map`: the input codes to `fieldSyms w (p :: ω :: as)`.
  `natSyms_map`: `natSyms X` decodes to `encodeNatList X`, from
  `encodeNat x = binBits (Nat.size x) x`.
* `takeField i j t`: the first field of register `i` onto the empty register `j`
  (`4 |l| + 5` steps).
* `emitNat s o`: `binSyms w x` from register `s` onto register `o` without high zeros, under a
  separator (`binSyms_size_pad`, `stripZeros`); emitting `X 0, …, X (n-1)` in order leaves
  `natSyms X` reversed on `o`.
* `parse_exec`: from empty registers `a, b, pr, wr, t`, `b` ends with `fieldSyms w as`, `pr`
  with `binSyms w p`, `wr` with `binSyms w ω`, `gin` empty, in `4 N + 8 w + 14` steps.
* `print_exec`: register `o` holding `natSyms X` reversed prints `encodeNatList X` on `gout`.
* `only_gin`, `only_gout`: the stores of `ComputesWithin` are `dmk` stores with every host
  stack empty.

### 4. The multiplier as a subroutine (`DFT/MulIO.lean`, `DFT/MulCall.lean`, proved)

`HostMultiplier κ` holds a host table (`T Q A U P`, `body`, `pm`, `v₀`), its time function, the
contract `∀ x y, HostMulWithin body pm v₀ time x y` (from `Store.only v₀ .inp (pairEnc (x, y))`
to `Store.only v₀ .out (encodeNat (x y))` in `m` steps, `m + 2 ≤ time |pairEnc (x, y)|`) and
`time =O n (log n) ^ (1 - κ)`. `dispatch_exec` (`Fast/Glue.lean`) gives the contract for every
`x y` from the final multiplier's large-input execution; `DFT/DFTCheck.lean` builds the instance.
Nothing in `DFT/` depends on the value of `κ`.

The DFT machine runs on `M.T + D` registers: the multiplier's first (`M.emb D = Fin.castAdd D`),
the DFT's after (`M.dreg D j = Fin.natAdd M.T j`, `emb_eq_dreg`). Its local state is
`HS (M.T + D) M.Q M.A (M.U × B)`, with the DFT's own component `B`. The table `M.tab D B main`
holds `main` at `none` and, at `some f`, the multiplier's procedure `f` embedded on its registers
(`embProg`), lifted to `M.U × B` (`liftProg`, `splitUser`) and put on the host keys
(`hostProg some`).

* `pushNat` (`10 L + 12` steps): `.inp` gains `(encodeNat y).map tag` from `binSyms L y`, through
  `bcopy`, `moveR`, `stripZeros` and `drainInp`.
* `readProduct` (`4 |z| + 20 W + 36` steps): `.out = encodeNat z` onto an empty register as
  `binSyms W z`, `W = |a| + |b|`, through `drainOut`, `moveR`, two `bcopy`s and `bwiden`.
* `call_exec`: with `.inp = pairEnc (x, y)`, `.out` empty and the multiplier's registers and all
  left stacks empty, `.call (some M.pm)` from `setV₀` (the multiplier's part of the state set to
  `v₀` through `embUp`, `B` kept) leaves `.inp` empty and `.out = encodeNat (x y)` in `m + 2`
  steps. Proof: `exec_emb_ovr`, `exec_lift`, `exec_hostProg`.
* `mulCall_exec`: `mulCall a b c t₁ … t₅` puts `binSyms (La + Lb) (x y)` on the empty register
  `c` from `a = binSyms La x`, `b = binSyms Lb y`, in `30 (La + Lb) + 4 |x y| + m + 63` steps
  with `m + 2 ≤ M.time (|x| + |y|)`; every other stack and `B` are kept.

For step bounds, `time` is replaced by a monotone majorant `Tm L = C₀ L (log (L+2))^(1-κ) + C₀`
(from the big-O bound and a finite maximum over small `L`).

### 5. Reduction on the host

Shared pieces (`DFT/Trunc.lean`, `DFT/HostSteps.lean`): `btrunc` (low `r` bits), `usub` by a
width register (`bhigh_exec`, high bits), `push_exec`, `peek_exec`, `update3_idem`.

**The Newton reciprocal** (`DFT/Newton*.lean`, proved). For `2 ^ (N - 1) ≤ D < 2 ^ N` let
`μ k = ⌊2 ^ (2k) / ⌊D / 2 ^ (N - k)⌋⌋`, the reciprocal of the top `k` bits.

* `newton_step` (`DFT/Newton.lean`): with `d` the top `2 k` bits and `a = μ k`, the guess
  `y = 2 ^ (k+1) a - (⌊d a² / 4 ^ k⌋ + 1)` has `y d < 16 ^ k < (y + 9) d`.
  `newton_level_arith` (`DFT/NewtonLevel.lean`): `μ (2k) = y + (2 ^ (4k) - y d) / d`, the
  correction at most `8`.
* Host blocks in `L = 4 k + 4` bits: `newtonPrep` (counter, width registers `2 k` and `L`,
  `ONE`, `SIX = 2 ^ (4k)`, `DFT/NewtonSetup.lean`), `newtonLoad` (`d` from the top of `Dp`, which
  holds `D` most significant bit first, `DFT/NewtonBlocks.lean`), `newtonSq`, `newtonGuessProg`,
  `newtonFinish` (`R := 2 ^ (4k) - y d`, then `corrLoop`: at most `8` rounds of `R := R - d`,
  `Y := Y + 1`, `DFT/NewtonHost.lean`, `DFT/NewtonGuess.lean`).
* `newtonLevel_exec` (`DFT/NewtonLevel.lean`): the blocks with the three products `a · a`,
  `d · a²`, `y · d` take `A` from `binSyms (2k + 4) (μ k)` to `binSyms (4k + 4) (μ (2k))` in
  `(3200 + 12 h) k + 4000 + 15 h` steps, for `M.time n ≤ (n + 1) H n`, `H` monotone,
  `h = H (4k + 4)`. The proof is split in `newtonLevelA_exec` and `newtonLevelB_exec` to stay
  under the default heartbeat limit.
* `recip_exec` (`DFT/NewtonLoop.lean`): from `Pw = binSyms w p`, `2 ^ (w - 1) ≤ p < 2 ^ w`, and a
  width register of `r ≥ w` symbols, `recipProg` builds `D = 2 ^ (2r) p` in `N = 2 r + w` bits,
  starts from `μ 1 = 4`, runs levels while a unary copy of `r` (losing `k` symbols per level) is
  nonempty, and leaves `A = binSyms (2k' + 4) ⌊2 ^ (k' + w) / p⌋` and `k'` symbols in `wK`, for
  some `r < k' ≤ 2 r` (`recip_value`). At most `(7200 + 27 H (4r + 4)) (2r + 1) + 20 r + 10 w + 40`
  steps.

**Barrett reduction** (`DFT/Barrett.lean`, proved). `μ = ⌊2 ^ (k + w) / p⌋` in `A` (width
`2k + 4`, `recip_le`), `k` symbols in `wK`, `w ≤ k`.

* `barrett_tail_val`: after `q p ≤ x < q p + 2 p`, one conditional subtraction of `p` from
  `x - q p` gives `x mod p`.
* `barrettTail_exec`: from `X = binSyms L x` and `Q2 = binSyms (L + e) (q p)`, `O := x mod p` in
  `w` bits (`btrunc`, `bsub`, `bcopy` and `bwiden` of `p`, `blt`, `bcopy` or `bsub`, `btrunc`),
  the work registers end empty, in `2 |Q1| + 60 L + 2 e + 12 w + 100` steps.
* `barrett_exec`: `barrettProg` (`mulCall` for `x μ`, `usub` by `wK` and by `Pw` for `q`,
  `mulCall` for `q p`, `barrettTail`) puts `binSyms w (x mod p)` on `O` for `x < 2 ^ (k + w)`,
  in `150 L + 120 k + 600` steps plus the two products.
* `modMul_exec`: `modMulProg` (`mulCall` for `x y`, `barrettProg`, the product cleared) puts
  `binSyms w (x y mod p)` on `O` for `x, y < p`, in `(520 + 9 h) k + 700 + 12 h` steps for
  `h = H (3k + 3)`.

**Montgomery arithmetic** (`DFT/Reduction.lean`, `DFT/RedcTail.lean`, `DFT/Redc.lean`,
`DFT/Montgomery.lean`, `DFT/Hensel*.lean`, proved, unused by the pipeline): `redc_exec`
(`redcProg`, `binSyms r (redc p R p' t)` from `t < p R`, `R ∣ p p' + 1`, in
`250 r + 200 + m₁ + m₂` steps), `montMul_exec` (`330 r + 270` steps plus three products) and
`hensel_exec` (`-p⁻¹ mod 2 ^ r` for odd `p` by rounds `y ↦ 2 y + (p y mod 2 ^ (2k)) y`, in
`(400 + 8 H (3r)) (2r + 1) + 270 r + 20` steps).

Entering Montgomery form needs `R² mod p` for `R = 2 ^ r`. From `R mod p` it takes either `r`
modular doublings, `O(r)` bit operations each and `O(r²)` in all, or a Montgomery power with
`log r` squarings of `M(r)` each, `O(M(w) log w)` for `r = O(w)`. The budget of the transform is
`O(N (log N) ^ (1 - κ))` with `N = Θ(n w)`, about `n M(w)`, and both costs exceed it when
`n < log w`. The Newton reciprocal costs `O(M(r))`: the precisions double, so the products of
the levels sum geometrically. The pipeline therefore reduces by Barrett's method.

### 6. The pipeline (`DFT/PipeA.lean` … `DFT/Main.lean`, proved)

Widths: `w = Nat.size p` (so `2 ^ (w - 1) ≤ p < 2 ^ w`), digit width `s = 3 w` (`B = 2 ^ s`),
reciprocal precision `r = 2 w`. For `n ≥ 1`, `n ∣ p - 1`, so `n < p ≤ 2 ^ w`: every correlation
`T k < n p ^ 2 < 2 ^ s = B` (the hypothesis `hB` of `fastDFT_transform`), and `s < k' + w` for
the `k' > r` of `recip_exec`, so Barrett applies to every `T k` and every product of residues.
No `Nat.size n` is computed.

Registers of the DFT part are concrete numerals of `Fin D` for one fixed `D`, so register
disequalities in the composition proofs are decided by `simp` on literals; the loop and block
lemmas stay generic in their registers.

1. Widths `wR = 2 w` and `w3 = 3 w` (copies of `Pw`); `recipProg` for `μ`. `O(w H (8w + 4))`.
2. Chirps, natural order. `C := 1`, `E := 1`. Loop A over a copy of the entry register (`n`
   rounds, round `m`): `Winv := E`, push `binSyms s (c m)` widened, most significant bit first,
   onto `V` (`bwiden`, `moveR`), `C := C E mod p`, `E := E ω mod p` (`modMul`). Loop B over a
   second copy: the same without `Winv`. Then `C m = ω ^ C(m,2) mod p` (`choose_two_succ`),
   `Winv = ω ^ (n - 1) mod p = inverseRoot p ω n`, and `moveR V V2` leaves
   `V2 = binSyms (2 n s) (pack B (chirp p ω) (2 n))`. `O(n w H(12 w + 3))`.
3. Chirped input, reversed. `C' := 1`, `E' := 1`. Loop I over the entry register (round `j`
   takes `a j`): `U := binSyms s (a j · C' mod p) ++ U` (`bcopy` prepends in order),
   `C' := C' E'`, `E' := E' Winv`, one tick onto `Ncnt`. Then
   `U = binSyms (n s) (pack B (chirpedInput p ω n a) n)`; `Dw := U` (a width register of `n s`
   symbols); `s` zeros pushed onto `U`, so `U = binSyms ((n + 1) s) (B · pack …)`.
4. One product: `mulCall U V2 Z`, then `usub Dw Z`: `Z = binSyms _ (chirpProduct' / B ^ n)`
   with `chirpProduct' = B · chirpProduct` on `2 n` chirp digits; digit `n + k` of it is the
   correlation `T k = ∑ j < n, chirpedInput (n - 1 - j) · chirp (j + k)` (`packProduct_digit`
   for `m ≥ n + k` chirp digits). `Tm(9 n w + 2) + O(n w)`.
5. Unpack and reduce. `C' := 1`, `E' := 1`. Loop over `Ncnt` (round `k`): the low `s` bits of
   `Z` onto `Tk` (`splitLow`), `O := T k mod p` (`barrettProg`), `X k = C' · O mod p`
   (`modMulProg`), `emitNat` onto `Out`, `C' := C' E'`, `E' := E' Winv`. `O(n w H(12w + 3))`.
6. Every work register cleared; `writeOut Out` prints `encodeNatList (fastDFT …)`
   (`print_exec`), equal to `DFTInstance.transform` (`fastDFT_transform`).

For `n = 0` every loop runs zero rounds and the output is empty, with no separate case.

`dftMain_exec` (`DFT/Main.lean`): `dftMain = parse ; pipeline ; clearAll ; writeOut rOut ;
load σ₀` runs, on every instance `x`, from `Store.only σ₀ .gin x.encode` to
`Store.only σ₀ .gout (encodeNatList x.transform)` in at most `dftBound H n w` steps, for any
monotone `H` with `M.time m ≤ (m + 1) H m`.

The loops share one lemma: a round `iter` followed by a test of the counter register runs while
the counter is nonempty, from an invariant `Inv i` with `Inv i → (counter nonempty ↔ i < n)`,
and each round takes `Inv i` to `Inv (i + 1)` in at most `c` steps.

Total: `O(n w H(12 w + 3) + Tm(9N) + w H(8w + 4) + N)` = `O(N (log N)^(1-κ))`, since `n w ≤ N`.

### 7. `DFT/Top.lean` and `DFT/DFTCheck.lean` (proved)

* `tH m = max_{m' ≤ m} ⌈M.time m' / (m' + 1)⌉` is monotone with `M.time m ≤ (m + 1) tH m`,
  and `tH m ≤ K + c (log m) ^ (1 - κ) + 1` (`tH_le`, from `M.isBigO`).
* `dftTimeOf H N = 100000 (N + 1) (H (16 N + 16) + 1)` bounds `dftBound H n w + 2` at
  `N = (n + 2) (w + 1)` (`dftBound_le`); `computesWithin` gives `ComputesWithin` for
  `M.tab 50 Unit (M.dftMain Unit M.dftσ₀)`, and `dftTime_isBigO` gives
  `dftTimeOf M.tH =O N (log N) ^ (1 - κ)` for `κ ≤ 1`. `HostMultiplier.dftInTime`:
  `κ ≤ 1 → DFTInTime κ`.
* `finalHostMultiplier : Nonempty (HostMultiplier (88279 / 2 ^ 46))` packages the rounded compact
  multiplier (`compactRetunedPrefixR_exec`, `compactCompletedR_hostMul`, `dispatch_exec`,
  `compactMain_runs_time_isBigO`), and

```
theorem dft_in_time : DFTStatement
#print axioms dft_in_time   -- propext, Classical.choice, Quot.sound
```

## Files

| file | content | status |
|---|---|---|
| `DFT/Statement.lean` | statement, Mathlib only | written |
| `DFT/Algorithm.lean` | transform arithmetic | written |
| `DFT/Reduction.lean` | REDC, Hensel inverse, Barrett with `4 ^ w` | written |
| `DFT/Keys.lean` | `DK`, `hostProg`, `exec_hostProg`, `computableInTime` | written |
| `DFT/IO.lean` | `readIn`, `writeOut`, symbol codes, encodings | written |
| `DFT/Fields.lean` | `takeField`, `stripZeros`, `emitNat` | written |
| `DFT/Parse.lean` | `parse`, `print_exec` | written |
| `DFT/MulIO.lean` | `pushNat`, `readProduct` | written |
| `DFT/MulCall.lean` | `HostMultiplier`, `tab`, `mulCall_exec` | written |
| `DFT/HostSteps.lean` | `push_exec`, `peek_exec`, `update3_idem` | written |
| `DFT/Trunc.lean` | `btrunc`, `bhigh_exec` | written |
| `DFT/RedcTail.lean` | `redcTail` | written, unused |
| `DFT/Redc.lean` | `dreg` lemmas, `redcProg`, `redc_exec` | written; `redcProg` unused |
| `DFT/Montgomery.lean` | `montMulProg`, `montMul_exec` | written, unused |
| `DFT/HenselHost.lean`, `DFT/Hensel.lean`, `DFT/HenselLoop.lean` | `hensel_exec` | written, unused |
| `DFT/Newton.lean` | `newton_step`, `barrett2_le`, `barrett2_lt` | written |
| `DFT/NewtonHost.lean` | `bcopyTop`, `corrStep`, `corrLoop` | written |
| `DFT/NewtonSetup.lean` | `pushS`, `newtonPrep` | written |
| `DFT/NewtonBlocks.lean` | `newtonLoad`, `newtonSq` | written |
| `DFT/NewtonGuess.lean` | `newtonGuessProg`, `newtonFinish` | written |
| `DFT/NewtonLevel.lean` | `newton_level_arith`, `newtonLevel_exec` | written |
| `DFT/NewtonLoop.lean` | `recipSetup`, `newtonLoop_aux`, `recip_exec` | written |
| `DFT/Barrett.lean` | `barrettTail`, `barrettProg`, `modMulProg` | written |
| `DFT/CountLoop.lean` | `countLoop_exec`, the loop over a counter register | written |
| `DFT/PipeMath.lean` | chirp recurrences, packed registers, `chirpProduct2_digit` | written |
| `DFT/PipeHost.lean`, `DFT/PipeSetup.lean` | host blocks between the loops | written |
| `DFT/Regs.lean` | the `50` pipeline registers as numerals | written |
| `DFT/Chirp.lean`, `DFT/ChirpLoop.lean` | `chirpStep`, loops A and B | written |
| `DFT/Input.lean`, `DFT/Unpack.lean` | the input loop, the unpacking loop | written |
| `DFT/PipeA.lean`, `DFT/PipeB.lean`, `DFT/PipeC.lean`, `DFT/Pipeline.lean` | §6 steps 1–5 | written |
| `DFT/Output.lean` | the printed values are `DFTInstance.transform` | written |
| `DFT/Main.lean` | `dftMain`, `dftMain_exec` | written |
| `DFT/Top.lean` | `tH`, `dftTimeOf`, `computesWithin`, `dftTime_isBigO`, `dftInTime` | written |
| `DFT/DFTCheck.lean` | `finalHostMultiplier`, `dft_in_time` | written |
