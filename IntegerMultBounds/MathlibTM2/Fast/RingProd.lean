module

public import IntegerMultBounds.MathlibTM2.Fast.RingProdRegs

/-!
# The pointwise ring products of two record streams

`rpProg` computes the pointwise negacyclic products `pwC p u v n = Q_p(u_n v_n / r)` (`r = 2^l`,
`Mult/SynthErr`) of the first `M` records of two numerator arrays `X`, `Y` by running the
vendored signed ring product (`RingProdBase`) once on all `M` record pairs as a placed foreign
machine.

**Formats.** A numerator array `X : ℕ → Fin r → GaussianInt` has grid records
`rpGrid p X n c = X n c / 2^p`. Its stream on a host register is
`cstream A w (rpStream M X)`: the coefficients of records `0, …, M - 1` in order, the first on
top, each as `csyms A w z = coeffSyms A w (red w z)` (`w` pair symbols, least significant first,
real bit and imaginary bit per symbol, two's complement modulo `2^w`). The vendored array of the
same records (`array w`, `rpRec`) holds per coefficient the real and then the imaginary numerator
as separate `w`-bit words, most significant bit first (`rpChunk`). The output stream is
`cstream A w (rpStream M (rpOut p X Y))`, where `rpOut p X Y n` are the numerators of the
vendored record `prodRec p (rpRec X n) (rpRec Y n)`; `rp_pwC_grid`:
`pwC p (rpGrid p X) (rpGrid p Y) n c = rpOut p X Y n c / 2^p`, so the output stream is the stream
of `pwC p u v` numerators at scale `2^p`. Inside the vendored product each record pair is one
packed Schönhage–Strassen product with truncation by `s = p + l` bits: division by `r = 2^l`
and by the product scale `2^(2p)` back to scale `2^p`.

**Program** (`rpProg`).
1. `rpEnc xs d1`, `rpEnc ys d2`: per coefficient (`rpWhile`), one word of `rpEncAuto` pops its
   `w` pair symbols, saves them on `sv` and splits them into real and imaginary bit symbols on
   `ta`, `tb` (most significant on top); moving `ta` and then `tb` onto `acc` appends the
   coefficient's vendored chunk to `acc` in reverse. Finally `acc` moves onto the data register
   and `sv` back onto the operand register.
2. `placedRun` of `rpMachine` on the 91 registers `ι`: header on `d0 = ι 0`, the operand arrays on
   `d1`, `d2`, the output array onto `d3` (`rp_placed_runs`).
3. `uclear` empties `d1` and `d2`.
4. `rpDec`: per coefficient, two words of `rpCpyAuto` move its real and its imaginary word from
   `d3` to `ta`, `tb` (least significant bit on top), one word of `rpZipAuto` pairs them into the
   coefficient's pair symbols on `acc`; finally `acc` moves onto `out`.

**Register interface** (`RpLayout`, `RpReg`; module `RingProdRegs`). Before: `xs`, `ys` hold the operand
streams, `wn` holds `w` symbols, `d0 = ι 0` holds the header `(header p (2^l) w).map bitSymbol`;
`sv`, `ta`, `tb`, `acc`, `tmp`, `d1`, `d2`, `d3` and the private registers `ι j` (`j ≥ 4`) are
empty, and every left stack of `ι` is empty (`RpClean`). After: `out` gains the output stream on
top; every other stack and the `user` component are unchanged (`rpProg_exec`). Hypotheses:
`91 ≤ T`, `rpStates ≤ Q`, `4 ≤ A`, `1 ≤ p`, `p + 2 ≤ w`, and every input record is a disk-grid
record: `re² + im² ≤ 2^(2p)` per coefficient (`DiskGrid`; `rp_diskGrid_of_norm` from
`‖rpGrid p X n c‖ ≤ 1`).

**Cost.** `rpCost T p l w M = (T + 1097) · rpTime p l w M + 100 M 2^l w + 6 H + 2 T + 600`,
`H` the header length: the vendored time `rpTime` (`pwCost` and sealing) at `T + 1097` host steps
per transition (`T + 5` for `foreign`, `12 · 91` for the placement passes), and the format
conversions. `rpCost_eq`: `rpCost = M · rpRecCost + rpFixCost`, with
`rpRecCost T p l w = (T + 1097) (ringCost W r w (p + l) (W r) + r (180 w + 400) + 204) + 100 r w`
(`W = wOf p l w`) and `rpFixCost` independent of `M`. `rpCost_le`: the same with
`rpRecBound`, where `ringCost` is replaced by the vendored bound `rpRingBound N`
(`4 costC (N + 1)(bitlen N + 1)(bitlen (bitlen N ^ 3) + 1) + 11000 N + 250000`, `N = W r`,
`ringCost_le`).
-/

@[expose] public section


set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Spec.SignedRingProduct

noncomputable section

/-! ### The programs -/

section Programs

variable {T Q A : ℕ} {U : Type} {P : Type} (rg : RpReg → Fin T)

/-- One coefficient of an operand stream: split its pair symbols into bits (saving the symbols
on `sv`), then push its reversed real and imaginary words onto `acc`. -/
def rpEncBody (src : RpReg) : Pr P T Q A U :=
  .seq (rpWord rg (![src] : Fin 1 → RpReg) (![.sv, .ta, .tb] : Fin 3 → RpReg) (rpEncAuto A))
    (.seq (moveR (rg .ta) (rg .acc) id) (moveR (rg .tb) (rg .acc) id))

/-- Write the vendored array of the operand stream `src` onto `dst`, restoring `src`. -/
def rpEnc (src dst : RpReg) : Pr P T Q A U :=
  .seq (rpWhile rg src (rpEncBody rg src))
    (.seq (moveR (rg .acc) (rg dst) id) (moveR (rg .sv) (rg src) id))

/-- One coefficient of the output array: its real and its imaginary word onto `ta`, `tb`
(least significant bit on top), then their pair symbols onto `acc`. -/
def rpDecBody : Pr P T Q A U :=
  .seq (rpWord rg (![.d3] : Fin 1 → RpReg) (![.ta] : Fin 1 → RpReg) (rpCpyAuto A))
    (.seq (rpWord rg (![.d3] : Fin 1 → RpReg) (![.tb] : Fin 1 → RpReg) (rpCpyAuto A))
      (rpWord rg (![.ta, .tb] : Fin 2 → RpReg) (![.acc] : Fin 1 → RpReg) (rpZipAuto A)))

/-- Push the host stream of the output array `d3` onto `out`, consuming `d3`. -/
def rpDec : Pr P T Q A U :=
  .seq (rpWhile rg .d3 (rpDecBody rg)) (moveR (rg .acc) (rg .out) id)

/-- The pointwise ring products of the operand streams `xs`, `ys` onto `out`: encode both
operands onto `d1`, `d2`, run the placed vendored ring product, clear `d1`, `d2`, decode `d3`. -/
def rpProg (ι : Fin 91 → Fin T) (hι : Function.Injective ι) (hT : 91 ≤ T)
    (hQ : rpStates ≤ Q) : Pr P T Q A U :=
  .seq (rpEnc rg .xs .d1) <| .seq (rpEnc rg .ys .d2) <|
  .seq (placedRun (rpMachine A hQ) ι hι hT) <|
  .seq (uclear (rg .d1)) <| .seq (uclear (rg .d2)) (rpDec rg)

end Programs

/-! ### One coefficient -/

section Coeff

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U} {rg : RpReg → Fin T}
  {ι : Fin 91 → Fin T}

/-- A word of a stateless automaton whose output `j` is a function of input register `i`. -/
lemma rp_out_one {ni no : ℕ} (M : Auto A ni no) (hM : ∀ s c, (M.step s c).1 = s)
    (L : Fin ni → List (Fin (A + 4))) (i : Fin ni) (c rest : List (Fin (A + 4)))
    (hL : L i = c ++ rest) {len : ℕ} (hc : c.length = len) (j : Fin no)
    (g : Fin (A + 4) → Fin (A + 4)) (hg : ∀ col, (M.step M.init col).2 j = g (col i)) :
    (M.runWord M.init (Auto.cols L len 0)).map (· j) = c.map g := by
  rw [rp_word_out M hM, rp_cols_one L i c rest hL hc _ g hg]

/-- Encoding one coefficient `z` from the top of `src`: `9 w + 10` steps. -/
theorem rp_encBody_runs (h : RpLayout rg ι) (hA : 4 ≤ A) {src : RpReg}
    (hs : src = .xs ∨ src = .ys) {w : ℕ} {ρ : RpReg → List (Fin (A + 4))} (z : GaussianInt)
    (rest : List (Fin (A + 4))) (hsrc : ρ src = csyms A w z ++ rest) (hwn : (ρ .wn).length = w)
    (hta : ρ .ta = []) (htb : ρ .tb = []) (htmp : ρ .tmp = []) :
    RpRuns body rg ι (rpEncBody rg src) ρ
      (Function.update (Function.update (Function.update ρ src rest)
        .sv ((csyms A w z).reverse ++ ρ .sv))
        .acc (((rpChunk w z).map bitSymbol).reverse ++ ρ .acc)) (9 * w + 10) := by
  have n1 : src ≠ .sv := by rcases hs with rfl | rfl <;> decide
  have n2 : src ≠ .ta := by rcases hs with rfl | rfl <;> decide
  have n3 : src ≠ .tb := by rcases hs with rfl | rfl <;> decide
  have n4 : src ≠ .acc := by rcases hs with rfl | rfl <;> decide
  have n5 : src ≠ .wn := by rcases hs with rfl | rfl <;> decide
  have n6 : src ≠ .tmp := by rcases hs with rfl | rfl <;> decide
  set re := (rpLsb w (z.re : ZMod (2 ^ w)).val).map (bitSymbol (a := A))
  set im := (rpLsb w (z.im : ZMod (2 ^ w)).val).map (bitSymbol (a := A))
  have hlen : (csyms A w z).length = w := by simp [csyms]
  set ρ₁ := Function.update (Function.update (Function.update (Function.update ρ src rest)
    .sv ((csyms A w z).reverse ++ ρ .sv)) .ta re.reverse) .tb im.reverse with hρ₁
  have s1 : RpRuns body rg ι (rpWord rg (![src] : Fin 1 → RpReg)
      (![.sv, .ta, .tb] : Fin 3 → RpReg) (rpEncAuto A)) ρ ρ₁ (5 * w + 6) := by
    refine rp_word_runs h (fun a b _ => Subsingleton.elim a b) (by decide)
      (fun i j => by fin_cases i; fin_cases j <;> simp [n1, n2, n3])
      (fun i => by fin_cases i; simp [n5]) (fun i => by fin_cases i; simp [n6])
      (by decide) (by decide) (rpEncAuto A) hwn htmp ?_ ?_ ?_
    · intro i
      fin_cases i
      simp [ρ₁, n1, n2, n3, hsrc, hlen]
    · intro j
      fin_cases j
      · show ρ₁ .sv = (((rpEncAuto A).runWord (rpEncAuto A).init
          (Auto.cols (fun i => ρ (![src] i)) w 0)).map (· 0)).reverse ++ ρ .sv
        rw [rp_out_one (rpEncAuto A) (fun _ _ => rfl) (fun i => ρ (![src] i)) 0 (csyms A w z)
          rest hsrc hlen 0 id (fun _ => rfl)]
        simp [ρ₁]
      · show ρ₁ .ta = (((rpEncAuto A).runWord (rpEncAuto A).init
          (Auto.cols (fun i => ρ (![src] i)) w 0)).map (· 1)).reverse ++ ρ .ta
        rw [rp_out_one (rpEncAuto A) (fun _ _ => rfl) (fun i => ρ (![src] i)) 0 (csyms A w z)
          rest hsrc hlen 1 (fun x => bitSymbol (pairRe x)) (fun _ => rfl), rp_csyms_map_re hA]
        simp [ρ₁, hta, re]
      · show ρ₁ .tb = (((rpEncAuto A).runWord (rpEncAuto A).init
          (Auto.cols (fun i => ρ (![src] i)) w 0)).map (· 2)).reverse ++ ρ .tb
        rw [rp_out_one (rpEncAuto A) (fun _ _ => rfl) (fun i => ρ (![src] i)) 0 (csyms A w z)
          rest hsrc hlen 2 (fun x => bitSymbol (pairIm x)) (fun _ => rfl), rp_csyms_map_im hA]
        simp [ρ₁, htb, im]
    · intro r hr₁ hr₂
      have m1 : src ≠ r := hr₁ 0
      have m2 : RpReg.sv ≠ r := hr₂ 0
      have m3 : RpReg.ta ≠ r := hr₂ 1
      have m4 : RpReg.tb ≠ r := hr₂ 2
      simp [ρ₁, m1.symm, m2.symm, m3.symm, m4.symm]
  have s2 := rp_moveR_runs (body := body) h (show RpReg.ta ≠ .acc by decide) (ρ := ρ₁) (n := w)
    (by simp [ρ₁, re])
  have s3 := rp_moveR_runs (body := body) h (show RpReg.tb ≠ .acc by decide)
    (ρ := Function.update (Function.update ρ₁ .ta []) .acc (re.reverse.reverse ++ ρ₁ .acc))
    (n := w) (by simp [ρ₁, im])
  refine ((s1.seq h (s2.seq h s3)).mono (by omega)).congr ?_
  funext r
  by_cases hr : r = src
  · subst hr
    simp [ρ₁, n1, n2, n3, n4]
  · cases r <;> simp [ρ₁, hta, htb, rpChunk, rp_compWord_eq_rev, re, im, List.map_reverse,
      Function.update_apply, hr]

/-- Decoding one coefficient `z` from the top of `d3`: `15 w + 18` steps. -/
theorem rp_decBody_runs (h : RpLayout rg ι) {w : ℕ} {ρ : RpReg → List (Fin (A + 4))}
    (z : GaussianInt) (rest : List (Fin (A + 4)))
    (hd3 : ρ .d3 = (rpChunk w z).map bitSymbol ++ rest) (hwn : (ρ .wn).length = w)
    (hta : ρ .ta = []) (htb : ρ .tb = []) (htmp : ρ .tmp = []) :
    RpRuns body rg ι (rpDecBody rg) ρ
      (Function.update (Function.update ρ .d3 rest) .acc ((csyms A w z).reverse ++ ρ .acc))
      (15 * w + 18) := by
  set re := (compWord w z.re).map (bitSymbol (a := A))
  set im := (compWord w z.im).map (bitSymbol (a := A))
  have hre : re.length = w := by simp [re, compWord]
  have him : im.length = w := by simp [im, compWord]
  have hd3' : ρ .d3 = re ++ (im ++ rest) := by rw [hd3]; simp [rpChunk, re, im]
  set ρ₁ := Function.update (Function.update ρ .d3 (im ++ rest)) .ta re.reverse with hρ₁
  have s1 : RpRuns body rg ι (rpWord rg (![.d3] : Fin 1 → RpReg) (![.ta] : Fin 1 → RpReg)
      (rpCpyAuto A)) ρ ρ₁ (5 * w + 6) := by
    refine rp_word_runs h (fun a b _ => Subsingleton.elim a b) (fun a b _ => Subsingleton.elim a b)
      (by decide) (by decide) (by decide) (by decide) (by decide) (rpCpyAuto A) hwn htmp ?_ ?_ ?_
    · intro i
      fin_cases i
      simp [ρ₁, hd3', hre]
    · intro j
      fin_cases j
      show ρ₁ .ta = (((rpCpyAuto A).runWord (rpCpyAuto A).init
        (Auto.cols (fun i => ρ (![.d3] i)) w 0)).map (· 0)).reverse ++ ρ .ta
      rw [rp_out_one (rpCpyAuto A) (fun _ _ => rfl) (fun i => ρ (![.d3] i)) 0 re (im ++ rest)
        hd3' hre 0 id (fun _ => rfl)]
      simp [ρ₁, hta]
    · intro r hr₁ hr₂
      have m1 : RpReg.d3 ≠ r := hr₁ 0
      have m2 : RpReg.ta ≠ r := hr₂ 0
      simp [ρ₁, m1.symm, m2.symm]
  set ρ₂ := Function.update (Function.update ρ₁ .d3 rest) .tb im.reverse with hρ₂
  have s2 : RpRuns body rg ι (rpWord rg (![.d3] : Fin 1 → RpReg) (![.tb] : Fin 1 → RpReg)
      (rpCpyAuto A)) ρ₁ ρ₂ (5 * w + 6) := by
    refine rp_word_runs h (fun a b _ => Subsingleton.elim a b) (fun a b _ => Subsingleton.elim a b)
      (by decide) (by decide) (by decide) (by decide) (by decide) (rpCpyAuto A)
      (by simp [ρ₁, hwn]) (by simp [ρ₁, htmp]) ?_ ?_ ?_
    · intro i
      fin_cases i
      simp [ρ₂, ρ₁, him]
    · intro j
      fin_cases j
      show ρ₂ .tb = (((rpCpyAuto A).runWord (rpCpyAuto A).init
        (Auto.cols (fun i => ρ₁ (![.d3] i)) w 0)).map (· 0)).reverse ++ ρ₁ .tb
      rw [rp_out_one (rpCpyAuto A) (fun _ _ => rfl) (fun i => ρ₁ (![.d3] i)) 0 im rest
        (by simp [ρ₁]) him 0 id (fun _ => rfl)]
      simp [ρ₂, ρ₁, htb]
    · intro r hr₁ hr₂
      have m1 : RpReg.d3 ≠ r := hr₁ 0
      have m2 : RpReg.tb ≠ r := hr₂ 0
      simp [ρ₂, m1.symm, m2.symm]
  set ρ₃ := Function.update (Function.update (Function.update ρ₂ .ta []) .tb [])
    .acc ((csyms A w z).reverse ++ ρ .acc) with hρ₃
  have e₁ : re.reverse = (rpLsb w (z.re : ZMod (2 ^ w)).val).map bitSymbol := by
    simp [re, rp_compWord_eq_rev, List.map_reverse]
  have e₂ : im.reverse = (rpLsb w (z.im : ZMod (2 ^ w)).val).map bitSymbol := by
    simp [im, rp_compWord_eq_rev, List.map_reverse]
  have s3 : RpRuns body rg ι (rpWord rg (![.ta, .tb] : Fin 2 → RpReg) (![.acc] : Fin 1 → RpReg)
      (rpZipAuto A)) ρ₂ ρ₃ (5 * w + 6) := by
    refine rp_word_runs h (by decide) (fun a b _ => Subsingleton.elim a b)
      (by decide) (by decide) (by decide) (by decide) (by decide) (rpZipAuto A)
      (by simp [ρ₂, ρ₁, hwn]) (by simp [ρ₂, ρ₁, htmp]) ?_ ?_ ?_
    · intro i
      fin_cases i
      · simp [ρ₃, ρ₂, ρ₁, hre]
      · simp [ρ₃, ρ₂, ρ₁, him]
    · intro j
      fin_cases j
      show ρ₃ .acc = (((rpZipAuto A).runWord (rpZipAuto A).init
        (Auto.cols (fun i => ρ₂ (![.ta, .tb] i)) w 0)).map (· 0)).reverse ++ ρ₂ .acc
      rw [rp_word_out _ (fun _ _ => rfl), rp_cols_two (fun i => ρ₂ (![.ta, .tb] i)) 0 1
        re.reverse im.reverse [] [] (by simp [ρ₂, ρ₁]) (by simp [ρ₂, ρ₁])
        (by simp [hre]) (by simp [him]) (fun c => ((rpZipAuto A).step (rpZipAuto A).init c).2 0)
        (fun x y => pairSym A (symBit x) (symBit y))
        (fun _ => rfl), e₁, e₂, rp_zip_csyms]
      simp [ρ₃, ρ₂, ρ₁]
    · intro r hr₁ hr₂
      have m1 : RpReg.ta ≠ r := hr₁ 0
      have m2 : RpReg.tb ≠ r := hr₁ 1
      have m3 : RpReg.acc ≠ r := hr₂ 0
      simp [ρ₃, m1.symm, m2.symm, m3.symm]
  refine ((s1.seq h (s2.seq h s3)).mono (by omega)).congr ?_
  funext r
  cases r <;> simp [ρ₃, ρ₂, ρ₁, hta, htb]

/-! ### Whole streams -/

lemma rp_length_chunks (w : ℕ) (zs : List GaussianInt) :
    (zs.flatMap (rpChunk w)).length = zs.length * (2 * w) := by
  induction zs with
  | nil => simp
  | cons z zs ih => simp [List.flatMap_cons, ih]; ring

/-- Encoding a whole operand stream from `src` onto `dst`: `|zs| (15 w + 12) + 6` steps. -/
theorem rp_enc_runs (h : RpLayout rg ι) (hA : 4 ≤ A) {src dst : RpReg}
    (hs : src = .xs ∧ dst = .d1 ∨ src = .ys ∧ dst = .d2) {w : ℕ} (hw : 1 ≤ w)
    (zs : List GaussianInt) {ρ : RpReg → List (Fin (A + 4))} (hsrc : ρ src = cstream A w zs)
    (hwn : (ρ .wn).length = w) (hsv : ρ .sv = []) (hta : ρ .ta = []) (htb : ρ .tb = [])
    (hacc : ρ .acc = []) (htmp : ρ .tmp = []) :
    RpRuns body rg ι (rpEnc rg src dst) ρ
      (Function.update ρ dst ((zs.flatMap (rpChunk w)).map bitSymbol ++ ρ dst))
      (zs.length * (15 * w + 12) + 6) := by
  have hs' : src = .xs ∨ src = .ys := by rcases hs with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1]
  have n1 : src ≠ .sv := by rcases hs' with rfl | rfl <;> decide
  have n2 : src ≠ .ta := by rcases hs' with rfl | rfl <;> decide
  have n3 : src ≠ .tb := by rcases hs' with rfl | rfl <;> decide
  have n4 : src ≠ .acc := by rcases hs' with rfl | rfl <;> decide
  have n5 : src ≠ .wn := by rcases hs' with rfl | rfl <;> decide
  have n6 : src ≠ .tmp := by rcases hs' with rfl | rfl <;> decide
  have m0 : dst ≠ src := by rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have m1 : dst ≠ .sv := by rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have m4 : dst ≠ .acc := by rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  set K := zs.length with hK
  set F : ℕ → RpReg → List (Fin (A + 4)) := fun k =>
    Function.update (Function.update (Function.update ρ src (cstream A w (zs.drop k)))
      .sv (cstream A w (zs.take k)).reverse)
      .acc (((zs.take k).flatMap (rpChunk w)).map bitSymbol).reverse with hF
  have hF0 : F 0 = ρ := by
    funext r
    by_cases hr : r = src
    · subst hr; simp [F, n1, n4, hsrc]
    · cases r <;> simp [F, hr, hsv, hacc]
  have hFsrc : ∀ k, F k src = cstream A w (zs.drop k) := fun k => by simp [F, n1, n4]
  have hloop := rpWhile_runs (body := body) (src := src) (p := rpEncBody rg src) h K F
    (fun k hk => by
      rw [hFsrc, List.drop_eq_getElem_cons hk, cstream_cons]
      exact List.append_ne_nil_of_left_ne_nil (csyms_ne_nil hw _) _)
    (by rw [hFsrc, List.drop_of_length_le (le_of_eq hK.symm)]; rfl)
    (fun k hk => by
      refine (rp_encBody_runs h hA hs' zs[k] (cstream A w (zs.drop (k + 1)))
        (by rw [hFsrc, List.drop_eq_getElem_cons hk, cstream_cons])
        (by simp [F, hwn, n5.symm]) (by simp [F, hta, n2.symm]) (by simp [F, htb, n3.symm])
        (by simp [F, htmp, n6.symm])).congr ?_
      funext r
      have ht : zs.take (k + 1) = zs.take k ++ [zs[k]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl
      by_cases hr : r = src
      · subst hr; simp [F, n1, n4]
      · cases r <;> simp only [F, Function.update_apply, reduceCtorEq, ite_false, ite_true, hr]
        · rw [ht, cstream_append]; simp
        · rw [ht, List.flatMap_append]; simp)
  have hFK : F K = Function.update (Function.update (Function.update ρ src [])
      .sv (cstream A w zs).reverse) .acc ((zs.flatMap (rpChunk w)).map bitSymbol).reverse := by
    simp only [F, List.drop_of_length_le (le_of_eq hK.symm), List.take_of_length_le
      (le_of_eq hK.symm), cstream_nil]
  rw [hF0, hFK] at hloop
  set ρ₁ := Function.update (Function.update (Function.update ρ src [])
      .sv (cstream A w zs).reverse) .acc ((zs.flatMap (rpChunk w)).map bitSymbol).reverse
  have s2 := rp_moveR_runs (body := body) h (show RpReg.acc ≠ dst from m4.symm) (ρ := ρ₁)
    (n := K * (2 * w)) (by simp [ρ₁, hK])
  have s3 := rp_moveR_runs (body := body) h (show RpReg.sv ≠ src from n1.symm)
    (ρ := Function.update (Function.update ρ₁ .acc []) dst ((ρ₁ .acc).reverse ++ ρ₁ dst))
    (n := K * w) (by simp [ρ₁, Function.update_apply, m1.symm, length_cstream, hK])
  refine ((hloop.seq h (s2.seq h s3)).mono ?_).congr ?_
  · have : K * (9 * w + 10 + 2) + 2 + (2 * (K * (2 * w)) + 2 + (2 * (K * w) + 2)) =
        K * (15 * w + 12) + 6 := by ring
    omega
  · funext r
    by_cases hr : r = src
    · subst hr; simp [ρ₁, Function.update_apply, n1, n4, m0, m0.symm, m1.symm, hsrc]
    by_cases hr' : r = dst
    · subst hr'; simp [ρ₁, Function.update_apply, m0, m1, m4, m0.symm, m1.symm]
    · cases r <;> simp [ρ₁, Function.update_apply, hr, Ne.symm hr, hr', Ne.symm hr', hsv, hacc]

/-- Decoding the output array on `d3` onto `out`: `|zs| (17 w + 20) + 4` steps. -/
theorem rp_dec_runs (h : RpLayout rg ι) {w : ℕ} (hw : 1 ≤ w) (zs : List GaussianInt)
    {ρ : RpReg → List (Fin (A + 4))} (hd3 : ρ .d3 = (zs.flatMap (rpChunk w)).map bitSymbol)
    (hwn : (ρ .wn).length = w) (hta : ρ .ta = []) (htb : ρ .tb = []) (hacc : ρ .acc = [])
    (htmp : ρ .tmp = []) :
    RpRuns body rg ι (rpDec rg) ρ
      (Function.update (Function.update ρ .d3 []) .out (cstream A w zs ++ ρ .out))
      (zs.length * (17 * w + 20) + 4) := by
  set K := zs.length with hK
  set F : ℕ → RpReg → List (Fin (A + 4)) := fun k =>
    Function.update (Function.update ρ .d3 (((zs.drop k).flatMap (rpChunk w)).map bitSymbol))
      .acc (cstream A w (zs.take k)).reverse with hF
  have hF0 : F 0 = ρ := by
    funext r
    cases r <;> simp [F, hd3, hacc]
  have hloop := rpWhile_runs (body := body) (src := .d3) (p := rpDecBody rg) h K F
    (fun k hk => by
      simp only [F, Function.update_apply, reduceCtorEq, ite_false, ite_true]
      rw [List.drop_eq_getElem_cons hk, List.flatMap_cons, List.map_append]
      refine List.append_ne_nil_of_left_ne_nil ?_ _
      intro he
      have := congrArg List.length he
      simp at this
      omega)
    (by simp [F, List.drop_of_length_le (le_of_eq hK.symm)])
    (fun k hk => by
      refine (rp_decBody_runs (w := w) h zs[k]
        (((zs.drop (k + 1)).flatMap (rpChunk w)).map bitSymbol)
        (by simp only [F, Function.update_apply, reduceCtorEq, ite_false, ite_true]
            rw [List.drop_eq_getElem_cons hk, List.flatMap_cons, List.map_append])
        (by simp [F, hwn]) (by simp [F, hta]) (by simp [F, htb]) (by simp [F, htmp])).congr ?_
      funext r
      have ht : zs.take (k + 1) = zs.take k ++ [zs[k]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl
      cases r <;> simp only [F, Function.update_apply, reduceCtorEq, ite_false, ite_true]
      rw [ht, cstream_append]; simp)
  have hFK : F K = Function.update (Function.update ρ .d3 []) .acc (cstream A w zs).reverse := by
    simp only [F, List.drop_of_length_le (le_of_eq hK.symm), List.take_of_length_le
      (le_of_eq hK.symm), List.flatMap_nil, List.map_nil]
  rw [hF0, hFK] at hloop
  have s2 := rp_moveR_runs (body := body) h (show RpReg.acc ≠ .out by decide)
    (ρ := Function.update (Function.update ρ .d3 []) .acc (cstream A w zs).reverse)
    (n := K * w) (by simp [length_cstream, hK])
  refine ((hloop.seq h s2).mono ?_).congr ?_
  · have : K * (15 * w + 18 + 2) + 2 + (2 * (K * w) + 2) = K * (17 * w + 20) + 4 := by ring
    omega
  · funext r
    cases r <;> simp [hacc]

/-! ### The placed vendored run -/

/-- The cells of the raw bank. -/
lemma rp_sum_cells (A : ℕ) (hdr F G out : List Bool) :
    ∑ j : Fin 91, (rpCells A hdr F G out j).length =
      hdr.length + F.length + G.length + out.length := by
  set f : ℕ → ℕ := fun n => if n = 0 then hdr.length else if n = 1 then F.length
    else if n = 2 then G.length else if n = 3 then out.length else 0 with hf
  have e : ∀ j : Fin 91, (rpCells A hdr F G out j).length = f j.val := by
    intro j
    simp only [rpCells, hf]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun j _ => e j), Fin.sum_univ_eq_sum_range f 91, Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (by norm_num : 0 ≤ 4) (by norm_num : 4 ≤ 91),
    Finset.sum_eq_zero (s := Finset.Ico 4 91) (fun i hi => by
      simp only [Finset.mem_Ico] at hi
      simp only [hf]
      split_ifs <;> omega)]
  simp [Finset.sum_range_succ, hf]

/-- A register outside the data registers is not a placed register. -/
lemma RpLayout.ι_ne (h : RpLayout rg ι) {r : RpReg} (h0 : r ≠ .d0) (h1 : r ≠ .d1) (h2 : r ≠ .d2)
    (h3 : r ≠ .d3) (j : Fin 91) : ι j ≠ rg r := by
  intro e
  by_cases j4 : 4 ≤ j.val
  · exact h.priv r j j4 e.symm
  · rcases (show j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 by omega) with hj | hj | hj | hj
    · obtain rfl : j = 0 := Fin.ext hj
      exact h0 (h.rg_inj (e.symm.trans h.d0.symm))
    · obtain rfl : j = 1 := Fin.ext hj
      exact h1 (h.rg_inj (e.symm.trans h.d1.symm))
    · obtain rfl : j = 2 := Fin.ext hj
      exact h2 (h.rg_inj (e.symm.trans h.d2.symm))
    · obtain rfl : j = 3 := Fin.ext hj
      exact h3 (h.rg_inj (e.symm.trans h.d3.symm))

/-- The placed vendored ring product: the output array onto `d3`. -/
theorem rp_placed_runs (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) {p l w : ℕ}
    {fs gs : List (Rec (2 ^ l))} (hp : 1 ≤ p) (hw : p + 2 ≤ w) (hlen : fs.length = gs.length)
    (hf : ∀ f ∈ fs, DiskGrid p f.1 f.2) (hg : ∀ g ∈ gs, DiskGrid p g.1 g.2)
    {ρ : RpReg → List (Fin (A + 4))} (h0 : ρ .d0 = (header p (2 ^ l) w).map bitSymbol)
    (h1 : ρ .d1 = (array w fs).map bitSymbol) (h2 : ρ .d2 = (array w gs).map bitSymbol)
    (h3 : ρ .d3 = []) :
    RpRuns body rg ι (placedRun (rpMachine A hQ) ι h.ι_inj hT) ρ
      (Function.update ρ .d3 ((array w (List.zipWith (prodRec p) fs gs)).map bitSymbol))
      ((T + 1097) * rpTime p l w fs.length +
        6 * ((header p (2 ^ l) w).length + 4 * 2 ^ l * w * fs.length) + 2 * T + 555) := by
  intro v S hc hS
  set hdr := header p (2 ^ l) w
  set out := array w (List.zipWith (prodRec p) fs gs)
  have hR : ∀ j, S.R (ι j) = rpCells A hdr (array w fs) (array w gs) [] j := by
    intro j
    by_cases j0 : j.val = 0
    · obtain rfl : j = 0 := Fin.ext j0
      rw [← h.d0, hS, h0]; simp [rpCells, hdr]
    by_cases j1 : j.val = 1
    · obtain rfl : j = 1 := Fin.ext j1
      rw [← h.d1, hS, h1]; simp [rpCells]
    by_cases j2 : j.val = 2
    · obtain rfl : j = 2 := Fin.ext j2
      rw [← h.d2, hS, h2]; simp [rpCells]
    by_cases j3 : j.val = 3
    · obtain rfl : j = 3 := Fin.ext j3
      rw [← h.d3, hS, h3]; simp [rpCells]
    rw [hc.2 j (by omega)]
    simp [rpCells, j0, j1, j2, j3]
  obtain ⟨v', n, R', hu, hn, hR'ι, hR'o, he⟩ := rp_placedRun_exec body (rpMachine A hQ) ι
    h.ι_inj hT (rpMachine_hoare A hQ hp hw hlen hf hg) (rp_blank_not_mem_cells A _ _ _ _) v S
    hc.1 hR
  have hpriv : ∀ j : Fin 91, 4 ≤ j.val → R' (ι j) = S.R (ι j) := by
    intro j hj
    rw [hR'ι, hc.2 j hj]
    have : ¬ j.val = 0 ∧ ¬ j.val = 1 ∧ ¬ j.val = 2 ∧ ¬ j.val = 3 := by omega
    simp [rpCells, this]
  refine ⟨v', _, n, hu, ?_, he, ?_, ⟨rfl, rfl, rfl, ?_⟩⟩
  · have hsum : ∑ j, (S.R (ι j)).length = hdr.length + 4 * 2 ^ l * w * fs.length := by
      simp only [hR]
      rw [rp_sum_cells]
      simp [length_array, hlen]
      ring
    rw [hsum] at hn
    simpa using hn
  · intro r
    show R' (rg r) = _
    cases r
    case d0 => rw [h.d0, hR'ι]; simp [rpCells, h0, hdr]
    case d1 => rw [h.d1, hR'ι]; simp [rpCells, h1]
    case d2 => rw [h.d2, hR'ι]; simp [rpCells, h2]
    case d3 => rw [h.d3, hR'ι]; simp [rpCells, out]
    all_goals
      rw [hR'o _ (fun j => h.ι_ne (by decide) (by decide) (by decide) (by decide) j), hS]
      simp
  · intro k hk
    by_cases hk' : ∃ j, ι j = k
    · obtain ⟨j, rfl⟩ := hk'
      by_cases j4 : 4 ≤ j.val
      · exact hpriv j j4
      · exfalso
        rcases (show j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 by omega) with
          hj | hj | hj | hj
        · obtain rfl : j = 0 := Fin.ext hj
          exact hk .d0 h.d0
        · obtain rfl : j = 1 := Fin.ext hj
          exact hk .d1 h.d1
        · obtain rfl : j = 2 := Fin.ext hj
          exact hk .d2 h.d2
        · obtain rfl : j = 3 := Fin.ext hj
          exact hk .d3 h.d3
    · exact hR'o k (fun j hj => hk' ⟨j, hj⟩)

end Coeff

/-! ### The stage -/

section Data

/-- Record `n` of a numerator array, as a vendored record. -/
def rpRec {r : ℕ} (X : ℕ → Fin r → GaussianInt) (n : ℕ) : Rec r :=
  (fun c => (X n c).re, fun c => (X n c).im)

/-- The coefficients of records `0, …, M - 1` of a numerator array, in order. -/
def rpStream {r : ℕ} (M : ℕ) (X : ℕ → Fin r → GaussianInt) : List GaussianInt :=
  (List.range M).flatMap fun n => List.ofFn (X n)

/-- The numerators of the records `Q_p(u_n v_n / r)` (`prodRec`). -/
def rpOut {r : ℕ} (p : ℕ) (X Y : ℕ → Fin r → GaussianInt) (n : ℕ) (c : Fin r) : GaussianInt :=
  ⟨(prodRec p (rpRec X n) (rpRec Y n)).1 c, (prodRec p (rpRec X n) (rpRec Y n)).2 c⟩

/-- The grid records of a numerator array: coefficient `c` of record `n` is `X n c / 2^p`. -/
def rpGrid (p : ℕ) {r : ℕ} (X : ℕ → Fin r → GaussianInt) : IntegerMultBounds.MathlibTM2.Mult.Rounds.Recs r :=
  fun n => gridPoly p (rpRec X n).1 (rpRec X n).2

lemma rpCoeffs_rpRec {r : ℕ} (M : ℕ) (X : ℕ → Fin r → GaussianInt) :
    rpCoeffs ((List.range M).map (rpRec X)) = rpStream M X := by
  simp only [rpCoeffs, rpStream, rpRec, List.flatMap_map]

lemma rp_zipWith_rpRec {r : ℕ} (p M : ℕ) (X Y : ℕ → Fin r → GaussianInt) :
    List.zipWith (prodRec p) ((List.range M).map (rpRec X)) ((List.range M).map (rpRec Y)) =
      (List.range M).map (rpRec (rpOut p X Y)) := by
  rw [List.zipWith_map, List.zipWith_self]
  rfl

@[simp] lemma length_rpStream {r : ℕ} (M : ℕ) (X : ℕ → Fin r → GaussianInt) :
    (rpStream M X).length = M * r := by
  induction M with
  | zero => simp [rpStream]
  | succ M ih =>
      simp only [rpStream, List.range_succ, List.flatMap_append] at ih ⊢
      simp [ih]
      ring

/-- The output records are the computed pointwise products `pwC` of the grid records:
`pwC p u v n c = Q_p(negacyclicMul (u n) (v n) c / r)` has numerators `rpOut p X Y n c`. -/
theorem rpGrid_rpOut (p : ℕ) {r : ℕ} [NeZero r] (X Y : ℕ → Fin r → GaussianInt) (n : ℕ) :
    rpGrid p (rpOut p X Y) n = IntegerMultBounds.MathlibTM2.Mult.SynthErr.pwC p (rpGrid p X) (rpGrid p Y) n := by
  rw [IntegerMultBounds.MathlibTM2.Mult.SynthErr.pwC_eq_gridPoly]
  rfl

/-- Coefficientwise: `pwC p u v n c = (rpOut p X Y n c) / 2^p`. -/
theorem rp_pwC_grid (p : ℕ) {r : ℕ} [NeZero r] (X Y : ℕ → Fin r → GaussianInt) (n : ℕ)
    (c : Fin r) :
    IntegerMultBounds.MathlibTM2.Mult.SynthErr.pwC p (rpGrid p X) (rpGrid p Y) n c =
      ⟨((rpOut p X Y n c).re : ℝ) / 2 ^ p, ((rpOut p X Y n c).im : ℝ) / 2 ^ p⟩ := by
  rw [← rpGrid_rpOut]
  rfl

/-- Records of modulus at most one have disk-grid numerators. -/
theorem rp_diskGrid_of_norm (p : ℕ) {r : ℕ} (X : ℕ → Fin r → GaussianInt) (n : ℕ)
    (h : ∀ c, ‖rpGrid p X n c‖ ≤ 1) : DiskGrid p (rpRec X n).1 (rpRec X n).2 := by
  intro c
  have h1 := h c
  have h2 : ‖rpGrid p X n c‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (rpGrid p X n c)]
  rw [Complex.sq_norm, Complex.normSq_apply] at h2
  simp only [rpGrid, gridPoly, rpRec] at h2 ⊢
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have h3 : ((X n c).re : ℝ) ^ 2 + ((X n c).im : ℝ) ^ 2 ≤ ((2 : ℝ) ^ p) ^ 2 := by
    have e : ((X n c).re : ℝ) / 2 ^ p * (((X n c).re : ℝ) / 2 ^ p) +
        ((X n c).im : ℝ) / 2 ^ p * (((X n c).im : ℝ) / 2 ^ p) =
        (((X n c).re : ℝ) ^ 2 + ((X n c).im : ℝ) ^ 2) / ((2 : ℝ) ^ p) ^ 2 := by
      field_simp
    rw [e, div_le_one (by positivity)] at h2
    exact h2
  have h4 : ((X n c).re ^ 2 + (X n c).im ^ 2 : ℤ) ≤ ((2 : ℤ) ^ p) ^ 2 := by exact_mod_cast h3
  rw [← pow_mul, mul_comm] at h4
  exact h4

end Data

section Main

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U} {rg : RpReg → Fin T}
  {ι : Fin 91 → Fin T}

open IntegerMultBounds.Schoenhage IntegerMultBounds.Schoenhage.Schedule in
/-- The step bound of the stage: the vendored time `rpTime` scaled by the host's simulation
factor `T + 1097`, and linear format conversions. -/
def rpCost (T p l w M : ℕ) : ℕ :=
  (T + 1097) * rpTime p l w M + 100 * (M * 2 ^ l * w) + 6 * (header p (2 ^ l) w).length +
    2 * T + 600

/-- The ring-product stage on register files. -/
theorem rpProg_runs (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {p l w M : ℕ} (hp : 1 ≤ p) (hw : p + 2 ≤ w) (X Y : ℕ → Fin (2 ^ l) → GaussianInt)
    (hX : ∀ n < M, DiskGrid p (rpRec X n).1 (rpRec X n).2)
    (hY : ∀ n < M, DiskGrid p (rpRec Y n).1 (rpRec Y n).2)
    {ρ : RpReg → List (Fin (A + 4))} (hxs : ρ .xs = cstream A w (rpStream M X))
    (hys : ρ .ys = cstream A w (rpStream M Y)) (hwn : (ρ .wn).length = w)
    (hsv : ρ .sv = []) (hta : ρ .ta = []) (htb : ρ .tb = []) (hacc : ρ .acc = [])
    (htmp : ρ .tmp = []) (hd0 : ρ .d0 = (header p (2 ^ l) w).map bitSymbol)
    (hd1 : ρ .d1 = []) (hd2 : ρ .d2 = []) (hd3 : ρ .d3 = []) :
    RpRuns body rg ι (rpProg rg ι h.ι_inj hT hQ) ρ
      (Function.update ρ .out (cstream A w (rpStream M (rpOut p X Y)) ++ ρ .out))
      (rpCost T p l w M) := by
  set fs := (List.range M).map (rpRec X) with hfs
  set gs := (List.range M).map (rpRec Y) with hgs
  have hw1 : 1 ≤ w := by omega
  have hfl : fs.length = M := by simp [fs]
  have hF : array w fs = (rpStream M X).flatMap (rpChunk w) := by
    rw [rp_array_eq_chunks, rpCoeffs_rpRec]
  have hG : array w gs = (rpStream M Y).flatMap (rpChunk w) := by
    rw [rp_array_eq_chunks, rpCoeffs_rpRec]
  have hO : array w (List.zipWith (prodRec p) fs gs) =
      (rpStream M (rpOut p X Y)).flatMap (rpChunk w) := by
    rw [hfs, hgs, rp_zipWith_rpRec, rp_array_eq_chunks, rpCoeffs_rpRec]
  have hdf : ∀ f ∈ fs, DiskGrid p f.1 f.2 := by
    intro f hf
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hf
    exact hX n (List.mem_range.1 hn)
  have hdg : ∀ g ∈ gs, DiskGrid p g.1 g.2 := by
    intro g hg
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hg
    exact hY n (List.mem_range.1 hn)
  have s1 := rp_enc_runs (body := body) h hA (src := .xs) (dst := .d1) (Or.inl ⟨rfl, rfl⟩) hw1
    (rpStream M X) hxs hwn hsv hta htb hacc htmp
  set ρ₁ := Function.update ρ .d1 (((rpStream M X).flatMap (rpChunk w)).map bitSymbol ++ ρ .d1)
  have s2 := rp_enc_runs (body := body) h hA (src := .ys) (dst := .d2) (Or.inr ⟨rfl, rfl⟩) hw1
    (rpStream M Y) (ρ := ρ₁) (by simp [ρ₁, hys]) (by simp [ρ₁, hwn]) (by simp [ρ₁, hsv])
    (by simp [ρ₁, hta]) (by simp [ρ₁, htb]) (by simp [ρ₁, hacc]) (by simp [ρ₁, htmp])
  set ρ₂ := Function.update ρ₁ .d2 (((rpStream M Y).flatMap (rpChunk w)).map bitSymbol ++ ρ₁ .d2)
  have s3 := rp_placed_runs (body := body) h hT hQ (fs := fs) (gs := gs) hp hw
    (by simp [fs, gs]) hdf hdg (ρ := ρ₂) (by simp [ρ₂, ρ₁, hd0]) (by simp [ρ₂, ρ₁, hd1, hF])
    (by simp [ρ₂, ρ₁, hd2, hG]) (by simp [ρ₂, ρ₁, hd3])
  set ρ₃ := Function.update ρ₂ .d3 ((array w (List.zipWith (prodRec p) fs gs)).map bitSymbol)
  have s4 := rp_uclear_runs (body := body) h .d1 (ρ := ρ₃) (n := 2 * 2 ^ l * w * M)
    (by simp [ρ₃, ρ₂, ρ₁, hd1]; ring)
  have s5 := rp_uclear_runs (body := body) h .d2 (ρ := Function.update ρ₃ .d1 [])
    (n := 2 * 2 ^ l * w * M) (by simp [ρ₃, ρ₂, ρ₁, hd2]; ring)
  have s6 := rp_dec_runs (body := body) h hw1 (rpStream M (rpOut p X Y))
    (ρ := Function.update (Function.update ρ₃ .d1 []) .d2 [])
    (by simp [ρ₃, hO]) (by simp [ρ₃, ρ₂, ρ₁, hwn]) (by simp [ρ₃, ρ₂, ρ₁, hta])
    (by simp [ρ₃, ρ₂, ρ₁, htb]) (by simp [ρ₃, ρ₂, ρ₁, hacc]) (by simp [ρ₃, ρ₂, ρ₁, htmp])
  refine ((s1.seq h (s2.seq h (s3.seq h (s4.seq h (s5.seq h s6))))).mono ?_).congr ?_
  · simp only [length_rpStream, hfl]
    unfold rpCost
    have hw3 : 3 ≤ w := by omega
    have hK : M * 2 ^ l * 44 ≤ M * 2 ^ l * (21 * w) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  · funext r
    cases r <;> simp [ρ₃, ρ₂, ρ₁, hd1, hd2, hd3]

/-- **The ring-product stage.** The registers `rg .xs`, `rg .ys` hold the coefficient streams of
the first `M` records of the numerator arrays `X`, `Y` (records of `2^l` Gaussian-integer
numerators at scale `2^p`, each coefficient `w` pair symbols least significant first, the first
coefficient on top), `rg .wn` holds `w` symbols, `rg .d0 = ι 0` the header `Γ(p)Γ(2^l)Γ(w)`; the
scratch registers, the other data registers and the private registers `ι j`, `j ≥ 4`, are empty,
and every left stack of `ι` is empty. Then `rpProg` pushes the stream of the numerators
`rpOut p X Y` of the pointwise products `Q_p(u_n v_n / 2^l)` (`rp_pwC_grid`) onto `rg .out`;
every other stack and the `user` component are unchanged; at most `rpCost T p l w M` steps. -/
theorem rpProg_exec (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {p l w M : ℕ} (hp : 1 ≤ p) (hw : p + 2 ≤ w) (X Y : ℕ → Fin (2 ^ l) → GaussianInt)
    (hX : ∀ n < M, DiskGrid p (rpRec X n).1 (rpRec X n).2)
    (hY : ∀ n < M, DiskGrid p (rpRec Y n).1 (rpRec Y n).2)
    (v : HS T Q A U) (S : Stacks T A) (hc : RpClean ι S)
    (hxs : S.R (rg .xs) = cstream A w (rpStream M X))
    (hys : S.R (rg .ys) = cstream A w (rpStream M Y)) (hwn : (S.R (rg .wn)).length = w)
    (hsv : S.R (rg .sv) = []) (hta : S.R (rg .ta) = []) (htb : S.R (rg .tb) = [])
    (hacc : S.R (rg .acc) = []) (htmp : S.R (rg .tmp) = [])
    (hd0 : S.R (rg .d0) = (header p (2 ^ l) w).map bitSymbol) (hd1 : S.R (rg .d1) = [])
    (hd2 : S.R (rg .d2) = []) (hd3 : S.R (rg .d3) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ rpCost T p l w M ∧
      Exec body (rpProg rg ι h.ι_inj hT hQ) (mk v S) n
        (mk v' { S with
          R := Function.update S.R (rg RpReg.out)
            (cstream A w (rpStream M (rpOut p X Y)) ++ S.R (rg RpReg.out)) }) := by
  obtain ⟨v', S', n, hu, hn, he, hS', hf⟩ := rpProg_runs (body := body) h hT hQ hA hp hw X Y hX hY
    (ρ := fun r => S.R (rg r)) hxs hys hwn hsv hta htb hacc htmp hd0 hd1 hd2 hd3 v S hc
    (fun _ => rfl)
  refine ⟨v', n, hu, hn, he.cast rfl ?_⟩
  congr 1
  refine Stacks.ext hf.1 hf.2.1 hf.2.2.1 ?_
  funext k
  show S'.R k = Function.update S.R (rg RpReg.out)
    (cstream A w (rpStream M (rpOut p X Y)) ++ S.R (rg RpReg.out)) k
  by_cases hk : ∃ r, rg r = k
  · obtain ⟨r, rfl⟩ := hk
    rw [hS' r]
    by_cases hr : r = RpReg.out
    · subst hr; simp
    · rw [Function.update_of_ne hr, Function.update_of_ne (h.rg_inj.ne hr)]
  · rw [hf.2.2.2 k (fun r hr => hk ⟨r, hr⟩),
      Function.update_of_ne (fun e => hk ⟨RpReg.out, e.symm⟩)]

end Main

/-! ### The bound per record -/

section Cost

open IntegerMultBounds.Schoenhage IntegerMultBounds.Schoenhage.Schedule

/-- The per-record part of `rpCost`: the host's simulation factor `T + 1097` times the vendored
per-record time (the packed product's bound `ringCost` at `W = wOf p l w` with truncation by
`p + l` bits, and the record's packing and unpacking), and the record's format conversions. -/
def rpRecCost (T p l w : ℕ) : ℕ :=
  (T + 1097) * (ringCost (wOf p l w) (2 ^ l) w (p + l) (wOf p l w * 2 ^ l) +
    2 ^ l * (180 * w + 400) + 204) + 100 * (2 ^ l * w)

/-- The part of `rpCost` independent of the record count: header decoding, constants, sealing. -/
def rpFixCost (T p l w : ℕ) : ℕ :=
  (T + 1097) * (headerCost p (2 ^ l) w (header p (2 ^ l) w).length + constCost p l w +
    100 * 2 ^ l + 60 * l + 10 * (p + l + w) + 6 * (wOf p l w * 2 ^ l) +
    4 * 2 ^ l * (wOf p l w + 2) + 10 * wOf p l w + 4 * (header p (2 ^ l) w).length + 1060) +
    6 * (header p (2 ^ l) w).length + 2 * T + 600

theorem rpCost_eq (T p l w M : ℕ) :
    rpCost T p l w M = M * rpRecCost T p l w + rpFixCost T p l w := by
  unfold rpCost rpRecCost rpFixCost rpTime pwCost
  ring

/-- The vendored bound of the packed ring product on `N` packed bits (`ringCost_le`). -/
def rpRingBound (N : ℕ) : ℕ :=
  4 * costC cA cB cC0 * (N + 1) * (bitlen N + 1) * (bitlen (bitlen N ^ 3) + 1) + 11000 * N +
    250000

/-- `rpRecCost` with the packed product's bound in the packed size `N = wOf p l w · 2^l`. -/
def rpRecBound (T p l w : ℕ) : ℕ :=
  (T + 1097) * (rpRingBound (wOf p l w * 2 ^ l) + 2 ^ l * (180 * w + 400) + 204) +
    100 * (2 ^ l * w)

theorem rpRecCost_le (T p l w : ℕ) : rpRecCost T p l w ≤ rpRecBound T p l w := by
  unfold rpRecCost rpRecBound rpRingBound
  have hW := mW_lt_wOf p l w
  unfold mW at hW
  have := ringCost_le (Wd := wOf p l w) (r := 2 ^ l) (w := w) (s := p + l)
    (N := wOf p l w * 2 ^ l) Nat.one_le_two_pow (by omega) (by omega) rfl
  gcongr

/-- The stage's bound: `M` records at `rpRecBound` each, plus `rpFixCost`. -/
theorem rpCost_le (T p l w M : ℕ) :
    rpCost T p l w M ≤ M * rpRecBound T p l w + rpFixCost T p l w := by
  rw [rpCost_eq]
  gcongr
  exact rpRecCost_le T p l w

end Cost

end

end IntegerMultBounds.MathlibTM2.Fast
