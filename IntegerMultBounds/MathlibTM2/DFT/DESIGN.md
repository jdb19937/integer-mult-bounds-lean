# The prime-field DFT below `n log n`: machine design

Target: `dft_in_time : DFTStatement` (`DFT/Statement.lean`, Mathlib imports only), from a host
multiplier with `time n = O(n (log n) ^ (1 - κ))`. The transform inherits the exponent `κ` of
the multiplier.

## Sizes

An instance is `p`, `ω`, `a 0, …, a (n - 1)`. Write `w = Nat.size p`. The input has length
`N = (n + 2) (w + 1)`. For `n ≥ 1`, `ω` has order `n` in `(ZMod p)ˣ`, so `n ∣ p - 1`, `n < p`
and `Nat.size n ≤ w`. Every size below is `O(w)` per scalar and `O(N)` for the one big product.

* Montgomery radix `R = 2 ^ r`, `r = w + Nat.size n`, so `n p < R` and `p < R`.
* Kronecker base `B = 2 ^ s`, `s = 2 w + Nat.size n`, so `n (p - 1) ^ 2 < B` (the hypothesis
  `hB` of `fastDFT_cast`).
* The product has two factors of `n s` and `(2 n - 1) s` bits: input length at most
  `3 n s + 2 ≤ 9 N`.

Small cases: `n = 0` prints nothing; `n = 1` prints `a 0` (`ω = 1`, `dft = a`). For `n ≥ 2`,
`p ≥ 3` is odd, which Montgomery reduction needs.

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

The machine reduces with Montgomery's REDC. Its representatives enter through
`packProduct_digit` (any digits `≤ p - 1`) and `correlation_cast` (casts equal to the chirped
input and the chirp up to factors `c₁`, `c₂`, here powers of `R`); the printed value is the
unique representative below `p`.

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

### 2. Top level (`DFT/Keys.lean`, proved; `DFT/Top.lean`, to do)

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
`x y` from the final multiplier's large-input execution; `DFTCheck.lean` builds the instance.
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

### 5. Montgomery arithmetic (`DFT/Trunc.lean`, `DFT/RedcTail.lean`, `DFT/Redc.lean`)

Registers of width `r`, `R = 2 ^ r`, `2 p ≤ R`; values `< p` unless stated.

* `btrunc` (low `r` bits) and `usub` by a width register (`bhigh_exec`, high bits).
* `redcTail`: `oR := (t + q) / R`, minus `p` when not below `p` (`badd`, `usub`, `blt`, `bcopy`
  or `bsub`).
* `redc_exec`: `redcProg` puts `binSyms r (redc p R p' t)` on `oR` from `t < p R`,
  `R ∣ p p' + 1`: `mulCall` for `t p'`, `btrunc` to `m = t p' mod R`, `mulCall` for `m p`, then
  `redcTail`. At most `250 r + 200 + m₁ + m₂` steps; `m₁`, `m₂` are bounded by the multiplier's
  time on the two products.
* `montMul_exec` (`DFT/Montgomery.lean`): `montMulProg` puts `binSyms r (redc p R p' (x y))` on
  `oR` for `x, y < p` (`mulCall`, `redcProg`, `bclear`), at most `330 r + 270` steps plus the
  three products. `redc_cast`, `redc_lt` identify the value as `x y R⁻¹` below `p`.

To do:

| procedure | interface | correctness | steps |
|---|---|---|---|
| `hensel` | `p` (odd) → `p' = -p⁻¹ mod R` | `henselStep`, `montInv_dvd` (`DFT/Reduction.lean`); round `k → 2k` by `y ↦ 2 y + (p y mod 2 ^ (2k)) y mod 2 ^ (2k)`, run while a unary copy of `r`, losing `k` symbols per round, is nonempty | `O(r)` plus the products, geometric in `k` |
| `modDouble` | `x` → `2 x mod p` | shift, compare, subtract | `O(r)` |
| `montPow` | `x`, exponent register `e` → Montgomery power | square and multiply over the bits of `e` | `O(size e · Tm(2r))` |
| `rSquare` | `p` → `R ^ 2 mod p` | `R mod p` by doublings from `2 ^ w - p`; `R ^ 2 mod p` as the Montgomery power `2 ^ r` of `2 R mod p` | `O(r log n + log r · Tm(2r))` |
| `toMont`, `fromMont` | `x ↦ REDC (x R²)`, `x ↦ REDC x` | `redc_cast` | `montMul` |

Every correctness statement is an exact congruence plus a bound below `p`.

### 6. The pipeline (`DFT/Pipeline.lean`)

Vector registers hold `fieldSyms` lists (fields of width `w`, `r` or `s`, first field on top);
the two Kronecker factors hold packs `binSyms (n s) (pack B u n)` with no separators.

1. Precompute `pinv`, `R² mod p`; `ω̃ = toMont ω`; `ω̃⁻¹ = montPow ω̃ (n - 1)`.
   `O(log n · Tm(2r) + Tm(4r) log r)`.
2. Chirps: `c̃ m = ω̃ ^ C(m,2)` for `m < 2n - 1` by `c̃ (m+1) = montMul (c̃ m) (ω̃ ^ m)` and
   `ω̃ ^ (m+1) = montMul (ω̃ ^ m) ω̃`; the same with `ω̃⁻¹` for `m < n`. Fields of width `s`
   (high zeros). `O(n Tm(2r) + n s)`.
3. Chirped input, reversed: `u i = montMul (toMont (a (n-1-i))) (c̃⁻¹ (n-1-i))`, pushed so that
   the vector register is `binSyms (n s) (pack B u n)`. `O(n Tm(2r) + n s)`.
4. One product: `mulCall` of the two packs, into width `(3n - 1) s`.
   `Tm(3 n s + 2) + O(n s)`.
5. Unpack and reduce: drop the low `(n - 1) s` bits; for `k < n`, field `k` is
   `T k = ∑ j, u j c̃ (j + k)` (`pack_div_pow_mod`, `conv_reflect`), `T k < n p² < p R`;
   `X k = fromMont (montMul (redc (T k)) (c̃⁻¹ k))`. `O(n Tm(2r) + n s)`.
6. Each `X k` (width `r`, `< p`) goes through `emitNat` onto the output register, which then
   holds `natSyms X` reversed for `print_exec`. `O(n r)`.

Total: `O(n Tm(2r) + Tm(9N) + log n · Tm(2r) + Tm(4r) log r + N)` = `O(N (log N)^(1-κ))`,
since `n r = O(N)` and `Tm` is superadditive up to constants.

Correctness: each register value is pinned by its cast to `ZMod p` and a bound below `p`; the
final `X k` equal `(dft ω a k).val` by `correlation_cast`.

### 7. `DFTCheck.lean`

```
theorem dft_in_time : DFTStatement
#print axioms dft_in_time
```

from `HostMultiplier κ → DFTInTime κ` and the final multiplier.

## Files

| file | content | status |
|---|---|---|
| `DFT/Statement.lean` | statement, Mathlib only | written |
| `DFT/Algorithm.lean` | transform arithmetic | written |
| `DFT/Reduction.lean` | REDC, Hensel inverse, Barrett | written |
| `DFT/Keys.lean` | `DK`, `hostProg`, `exec_hostProg`, `computableInTime` | written |
| `DFT/IO.lean` | `readIn`, `writeOut`, symbol codes, encodings | written |
| `DFT/Fields.lean` | `takeField`, `stripZeros`, `emitNat` | written |
| `DFT/Parse.lean` | `parse`, `print_exec` | written |
| `DFT/MulIO.lean` | `pushNat`, `readProduct` | written |
| `DFT/MulCall.lean` | `HostMultiplier`, `tab`, `mulCall_exec` | written |
| `DFT/Trunc.lean` | `btrunc`, `bhigh_exec` | written |
| `DFT/RedcTail.lean` | `redcTail` | written |
| `DFT/Redc.lean` | `redcProg`, `redc_exec` | written |
| `DFT/Montgomery.lean` | `montMulProg`, `montMul_exec` | written |
| `DFT/Montgomery.lean` (rest) | Hensel, `montPow`, `rSquare`, conversions | to do |
| `DFT/Pipeline.lean` | §6 | to do |
| `DFT/Top.lean` | `ComputesWithin` for the pipeline, `HostMultiplier κ → DFTInTime κ` | to do |
| `DFTCheck.lean` | `dft_in_time` | to do |
