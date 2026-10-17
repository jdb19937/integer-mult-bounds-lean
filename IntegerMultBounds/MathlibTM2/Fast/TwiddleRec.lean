module

public import IntegerMultBounds.MathlibTM2.Fast.TwiddleRuns
public import IntegerMultBounds.MathlibTM2.Fast.TwiddleMath

/-!
# One record times `y^e`

A record of `ℛ_r = ℂ[y]/(y^r + 1)`, `r = 2^ℓ`, is `r` coefficients on a stream register:
`cstream A w rec`, `w` pair symbols per coefficient. `twRecP` multiplies the record on top of
`src` by `y^e`, for `e` held in binary on `f` (`binSyms (ℓ + 1) e`, least significant bit on top),
and pushes the product onto `acc` (reversed, as a stream program accumulates).

**Algorithm.** With `s = e mod r` and `g` bit `ℓ` of `e`:
1. move the `r w` symbols of the record from `src` onto `x` (counted by `rwn`), so `x` holds
   the record reversed;
2. split `f`: its top bit `g` (the last symbol) goes onto `sg`, the low `ℓ` bits stay on `f`;
3. move `s w` symbols from `x` onto `tl` by a binary-controlled counted move: a block counter
   `c` starts with `w` symbols (a copy of `wn`); for bit `j` of `s` (`scanP` over `f`), if the bit
   is set, `|c| = 2^j w` symbols move from `x` onto `tl`; then `c` doubles (`twDblBody`). Now `tl`
   holds the last `s` coefficients (the wrapped tail) in order, and the rest of `x` moves onto
   `hd`: the first `r - s` coefficients in order;
4. if `g = 0`: `acc` gains the negated tail (the Gaussian automaton of `[[−1]]`, `twNeg`), then
   the head; if `g = 1`: the tail, then the negated head;
5. clear `c`, `f`, `sg`.

**Result** (`twRec_runs`): `src` loses the record, `acc` gains
`(cstream A w (twShiftL ℓ e rec)).reverse` on top, `f` ends empty and every other register ends as
it started; `twShiftL_ofFn` and `twShiftZ_toComplex` identify `twShiftL ℓ e` with `shiftNegZ e`.
The register holds `binSyms (ℓ + 1) e`, so `e` acts modulo `2^(ℓ+1) = 2r`. `twRecInv_runs`: `twRecInvP` first replaces `e` by
`(2r - e) mod 2r` (`twNegE`, a subtraction from zero), so the record is multiplied by `y^(-e)`
(`shiftInv e`, `twShiftZ_shiftInv`).

**Registers** (`TwReg`, layout `tg` injective; one register type for all twiddle machines, the
registers `pa`, `pz`, `ps`, `pv`, `nn`, `nm` serve the permuted layout of `Fast/TwiddleL`): `src`,
`acc` (stream in and out), `f` (the exponent), `wn` (`w` symbols), `rwn` (`r w` symbols), `hn`
(`ℓ + 1` symbols, inverse only); the scratch registers `x`, `tl`, `hd`, `c`, `sg`, `z`, `g`, `t1`,
`t2`, `t3`, `t4`, `t5` start and end empty. The scan slots `tg .st` (automaton state) and `tg .cy` (carry) serve as scratch.
Conditions: `5 ≤ A`, `1 ≤ w`.

**Cost** (`twRecCost ℓ w = 33 · 2^ℓ · w + 20 ℓ + 40`): `O(r w)` for the moves, the doublings
(geometric) and the negations, `O(ℓ)` for the exponent bits.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.NLogN IntegerMultBounds.Spec.SignedRingProduct

set_option maxHeartbeats 1000000

/-- The registers of the twiddle machines. -/
inductive TwReg
  | src | dst | acc | wn | rwn | ad | rl | hn | lh
  | x | tl | hd | c | v | vp | f | g | z | sg | as | t1 | t2 | t3 | t4 | t5 | cy | st
  | pa | pz | ps | pv | nn | nm
  deriving DecidableEq

section Programs

variable {T Q A : ℕ} {U P : Type} (tg : TwReg → Fin T)

/-- The body of the doubling loop: on bit `1` move `|c|` symbols of `x` onto `tl`; double `c`. -/
def twDblBody : Pr P T Q A U :=
  .cond (fun v => symBit (v.sym.getD blank))
    (.seq (twCMv (tg .c) (tg .x) (tg .tl) (tg .t3)) (udbl (tg .c) (tg .t2)))
    (udbl (tg .c) (tg .t2))

/-- The sign step: the tail before the head, the tail negated when `sg` holds `0`, the head
negated when it holds `1`. -/
def twSignP : Pr P T Q A U :=
  twIfTop (tg .sg)
    (.seq (moveR (tg .tl) (tg .acc) id) (twNeg (tg .hd) (tg .acc) (tg .st) (tg .wn) (tg .t2)))
    (.seq (twNeg (tg .tl) (tg .acc) (tg .st) (tg .wn) (tg .t2)) (moveR (tg .hd) (tg .acc) id))

/-- **One record times `y^e`**, `e` on `f` in `ℓ + 1` bits. -/
def twRecP : Pr P T Q A U :=
  .seq (twCMv (tg .rwn) (tg .src) (tg .x) (tg .t1)) <|
  .seq (moveR (tg .f) (tg .t1) id) <|
  .seq (.act (twMvTop (tg .t1) (tg .sg) .done)) <|
  .seq (moveR (tg .t1) (tg .f) id) <|
  .seq (ucopy (tg .wn) (tg .c) (tg .t2)) <|
  .seq (scanP (tg .f) (tg .t1) (twDblBody tg)) <|
  .seq (uclear (tg .c)) <|
  .seq (moveR (tg .x) (tg .hd) id) <|
  .seq (twSignP tg) <|
  .seq (uclear (tg .f)) (uclear (tg .sg))

/-- Replace the `L`-bit value `e` on `f` by `(2^L - e) mod 2^L`, `L` the length of the unary
register `u`: subtract from zero. -/
def twNegE (u : TwReg) : Pr P T Q A U :=
  .seq (zeroBits (tg u) (tg .z) (tg .t1)) <|
  .seq (bsub (tg .z) (tg .f) (tg .g) (tg .t3) (tg .t4) (tg .t5) (tg .cy)) <|
  .seq (uclear (tg .z)) <|
  .seq (uclear (tg .f)) <|
  .seq (moveR (tg .g) (tg .t1) id) (moveR (tg .t1) (tg .f) id)

/-- **One record times `y^(-e)`.** -/
def twRecInvP : Pr P T Q A U := .seq (twNegE tg .hn) (twRecP tg)

end Programs

/-- The step bound of `twRecP`. -/
def twRecCost (ℓ w : ℕ) : ℕ := 33 * 2 ^ ℓ * w + 20 * ℓ + 40

/-- The step bound of `twNegE` on `L` bits. -/
def twNegECost (L : ℕ) : ℕ := 20 * L + 30

lemma tw_sum_pow_two (w : ℕ) : ∀ ℓ : ℕ,
    ∑ j ∈ Finset.range ℓ, (8 * (2 ^ j * w) + 9 + 3) + 8 * w ≤ 8 * (2 ^ ℓ * w) + 12 * ℓ
  | 0 => by simp
  | ℓ + 1 => by
      have ih := tw_sum_pow_two w ℓ
      rw [Finset.sum_range_succ, pow_succ]
      nlinarith [Nat.zero_le (2 ^ ℓ * w)]

section Runs

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {tg : TwReg → Fin T}
  (htg : Function.Injective tg)
include htg

/-- The register file of the doubling loop after `j` bits. -/
def twDblSt (ρ : TwReg → List (Fin (A + 4))) (X : List (Fin (A + 4))) (w e : ℕ) (j : ℕ) :
    TwReg → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update ρ .c (List.replicate (2 ^ j * w) tick))
    .x (X.drop (w * (e % 2 ^ j)))) .tl ((X.take (w * (e % 2 ^ j))).reverse)

theorem twRuns_dbl {ℓ w e : ℕ} (ρ : TwReg → List (Fin (A + 4)))
    (X : List (Fin (A + 4))) (hX : X.length = 2 ^ ℓ * w) (ht2 : ρ .t2 = []) (ht3 : ρ .t3 = []) :
    TwRuns body tg (scanP (tg .f) (tg .t1) (twDblBody tg))
      (twAT .f .t1 (binSyms ℓ e) (twDblSt ρ X w e) 0)
      (Function.update (Function.update (twDblSt ρ X w e ℓ) .f (binSyms ℓ e)) .t1 [])
      (∑ j ∈ Finset.range ℓ, (8 * (2 ^ j * w) + 9 + 3) + 2 * ℓ + 4) := by
  have h := twRuns_scanP (body := body) htg (a := TwReg.f) (t := TwReg.t1) (by decide)
    (p := twDblBody tg) (binSyms ℓ e) (twDblSt ρ X w e) (fun j => 8 * (2 ^ j * w) + 9) ?_
  · simpa using h
  intro j hj
  rw [length_binSyms] at hj
  rw [getElem_binSyms]
  have hm := Nat.mod_pow_succ (b := 2) (x := e) (k := j)
  have hjl : 2 ^ (j + 1) ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlt : e % 2 ^ (j + 1) < 2 ^ (j + 1) := Nat.mod_lt _ (by positivity)
  have hbit : e / 2 ^ j % 2 = (e.testBit j).toNat := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (e / 2 ^ j) with h | h <;> simp [h]
  have hc : twATin .f .t1 (binSyms ℓ e) (twDblSt ρ X w e) j .c =
      List.replicate (2 ^ j * w) tick := by simp [twATin, twDblSt]
  have hx : twATin .f .t1 (binSyms ℓ e) (twDblSt ρ X w e) j .x = X.drop (w * (e % 2 ^ j)) := by
    simp [twATin, twDblSt]
  have ht2' : twATin .f .t1 (binSyms ℓ e) (twDblSt ρ X w e) j .t2 = [] := by
    simp [twATin, twDblSt, ht2]
  have ht3' : twATin .f .t1 (binSyms ℓ e) (twDblSt ρ X w e) j .t3 = [] := by
    simp [twATin, twDblSt, ht3]
  have hrep : (List.replicate (2 ^ j * w) (tick : Fin (A + 4))).flatMap (List.replicate 2) =
      List.replicate (2 ^ (j + 1) * w) tick := by
    rw [flatMap_replicate_of_replicate, pow_succ]; congr 1; ring
  cases hb : e.testBit j with
  | true =>
      rw [hb] at hbit
      have hq1 : e % 2 ^ (j + 1) = e % 2 ^ j + 2 ^ j := by rw [hm, hbit]; simp
      have hle : w * (e % 2 ^ j) + 2 ^ j * w ≤ X.length := by
        rw [hX, show w * (e % 2 ^ j) + 2 ^ j * w = (e % 2 ^ j + 2 ^ j) * w by ring]
        exact Nat.mul_le_mul_right w (by omega)
      have hcm := twRuns_cmv (body := body) htg (c := .c) (src := .x) (dst := .tl) (t := .t3)
        (by decide) (twATin .f .t1 (binSyms ℓ e) (twDblSt ρ X w e) j) ht3'
        (by rw [hc, hx]; simp; omega)
      rw [hc, hx] at hcm
      simp only [List.length_replicate] at hcm
      have hud := twRuns_udbl (body := body) htg (b := .c) (t := .t2) (by decide)
        (Function.update (Function.update (twATin .f .t1 (binSyms ℓ e) (twDblSt ρ X w e) j) .x
          ((X.drop (w * (e % 2 ^ j))).drop (2 ^ j * w))) .tl
          (((X.drop (w * (e % 2 ^ j))).take (2 ^ j * w)).reverse ++
            twATin .f .t1 (binSyms ℓ e) (twDblSt ρ X w e) j .tl)) (by simp [ht2'])
      have hdr : (X.drop (w * (e % 2 ^ j))).drop (2 ^ j * w) = X.drop (w * (e % 2 ^ (j + 1))) := by
        rw [List.drop_drop, hq1]; congr 1; ring
      have htk : ((X.drop (w * (e % 2 ^ j))).take (2 ^ j * w)).reverse ++
          (X.take (w * (e % 2 ^ j))).reverse = (X.take (w * (e % 2 ^ (j + 1)))).reverse := by
        rw [hq1, show w * (e % 2 ^ j + 2 ^ j) = w * (e % 2 ^ j) + 2 ^ j * w by ring,
          List.take_add, List.reverse_append]
      refine twRunsS_mono (twRunsS_cond_true (fun v hv => by simp [hv])
        (twRunsS_of (twRuns_congr (twRuns_seq hcm hud) ?_))) ?_
      · rw [hdr]
        funext r
        cases r <;> simp [twAT, twATin, twDblSt, hrep, ← htk]
      · simp [hc]
        omega
  | false =>
      rw [hb] at hbit
      have hq1 : e % 2 ^ (j + 1) = e % 2 ^ j := by rw [hm, hbit]; simp
      have hud := twRuns_udbl (body := body) htg (b := .c) (t := .t2) (by decide)
        (twATin .f .t1 (binSyms ℓ e) (twDblSt ρ X w e) j) ht2'
      refine twRunsS_mono (twRunsS_cond_false (fun v hv => by simp [hv])
        (twRunsS_of (twRuns_congr hud ?_))) ?_
      · rw [hc, hrep]
        funext r
        cases r <;> simp [twAT, twATin, twDblSt, hq1]
      · rw [hc]; simp; omega

/-- The sign step on a tail `TL` and a head `HD`. -/
theorem twRuns_sign (hA : 5 ≤ A) {w : ℕ} (hw : 1 ≤ w) (ρ : TwReg → List (Fin (A + 4)))
    (TL HD : List GaussianInt) (bt : Bool) (htl : ρ .tl = cstream A w TL)
    (hhd : ρ .hd = cstream A w HD) (hsg : ρ .sg = [bitSymbol bt]) (hwn : (ρ .wn).length = w)
    (ht2 : ρ .t2 = []) :
    TwRuns body tg (twSignP tg) ρ
      (Function.update (Function.update (Function.update ρ .tl []) .hd []) .acc
        ((cstream A w (if bt then TL ++ HD.map (fun z => -z) else TL.map (fun z => -z) ++ HD)).reverse
          ++ ρ .acc))
      ((TL.length + HD.length) * (5 * w + 6) + 6) := by
  have hst : ∀ r : TwReg, r ≠ .st → tg r ≠ tg .st := fun r hr => htg.ne hr
  refine twRuns_mono (twRuns_ifTop (g := TwReg.sg) (bt := bt) (rest := []) hsg ?_ ?_) le_rfl
  · rintro rfl
    have h1 := twRuns_moveR (body := body) htg (a := .tl) (b := .acc) (by decide) ρ
    have h2 := twRuns_neg (body := body) htg (ins := .hd) (outs := .acc) (ctr := .wn) (tmp := .t2)
      (by decide) (hst .hd (by decide)) hA hw
      (Function.update (Function.update ρ .tl []) .acc ((ρ .tl).reverse ++ ρ .acc))
      (HD.map (red w)) (by simp [hhd, tw_cstream_eq]) (by simp [hwn]) (by simp [ht2])
    refine twRuns_mono (twRuns_congr (twRuns_seq h1 h2) ?_) ?_
    · rw [tw_cstream_neg, htl]
      funext r
      cases r <;> simp
    · simp [htl]
      nlinarith
  · rintro rfl
    have h1 := twRuns_neg (body := body) htg (ins := .tl) (outs := .acc) (ctr := .wn) (tmp := .t2)
      (by decide) (hst .tl (by decide)) hA hw ρ (TL.map (red w)) (by simp [htl, tw_cstream_eq])
      hwn ht2
    have h2 := twRuns_moveR (body := body) htg (a := .hd) (b := .acc) (by decide)
      (Function.update (Function.update ρ .tl []) .acc
        ((((TL.map (red w)).map fun z => -z).flatMap (coeffSyms A w)).reverse ++ ρ .acc))
    refine twRuns_mono (twRuns_congr (twRuns_seq h1 h2) ?_) ?_
    · rw [tw_cstream_neg]
      funext r
      cases r <;> simp [hhd]
    · simp [hhd]
      nlinarith

/-- **One record times `y^e`.** -/
theorem twRec_runs (hA : 5 ≤ A) {ℓ w e : ℕ} (hw : 1 ≤ w) (ρ : TwReg → List (Fin (A + 4)))
    (rec : List GaussianInt) (rest : List (Fin (A + 4))) (hrec : rec.length = 2 ^ ℓ)
    (hsrc : ρ .src = cstream A w rec ++ rest) (hf : ρ .f = binSyms (ℓ + 1) e)
    (hwn : (ρ .wn).length = w) (hrwn : (ρ .rwn).length = 2 ^ ℓ * w)
    (hx : ρ .x = []) (htl : ρ .tl = []) (hhd : ρ .hd = []) (hc : ρ .c = []) (hsg : ρ .sg = [])
    (ht1 : ρ .t1 = []) (ht2 : ρ .t2 = []) (ht3 : ρ .t3 = []) :
    TwRuns body tg (twRecP tg) ρ
      (Function.update (Function.update (Function.update ρ .src rest) .acc
        ((cstream A w (twShiftL ℓ e rec)).reverse ++ ρ .acc)) .f [])
      (twRecCost ℓ w) := by
  have hX0 : (cstream A w rec).length = 2 ^ ℓ * w := by rw [length_cstream, hrec]
  -- 1. the record onto `x`
  have h1 := twRuns_cmv (body := body) htg (c := .rwn) (src := .src) (dst := .x) (t := .t1)
    (by decide) ρ ht1 (by rw [hrwn, hsrc]; simp [hX0])
  rw [hrwn, hsrc, List.drop_left' hX0, List.take_left' hX0, hx, List.append_nil] at h1
  set ρ₁ := Function.update (Function.update ρ .src rest) .x (cstream A w rec).reverse with hρ₁
  -- 2. split the exponent
  have h2 := twRuns_moveR (body := body) htg (a := .f) (b := .t1) (by decide) ρ₁
  have hf₁ : ρ₁ .f = binSyms (ℓ + 1) e := by simp [hρ₁, hf]
  have ht₁ : ρ₁ .t1 = [] := by simp [hρ₁, ht1]
  rw [hf₁, ht₁, List.append_nil, length_binSyms, binSyms_succ', List.reverse_append] at h2
  have h3 := twRuns_mvTop (body := body) htg (src := .t1) (dst := .sg) (by decide)
    (ρ := Function.update (Function.update ρ₁ .f []) .t1
      ([bitSymbol (e.testBit ℓ)].reverse ++ (binSyms ℓ e).reverse))
    (y := bitSymbol (e.testBit ℓ)) (rest := (binSyms ℓ e).reverse) (by simp)
  set ρ₃ := Function.update (Function.update (Function.update (Function.update ρ₁ .f []) .t1
      ([bitSymbol (e.testBit ℓ)].reverse ++ (binSyms ℓ e).reverse)) .t1 (binSyms ℓ e).reverse) .sg
      (bitSymbol (e.testBit ℓ) ::
        Function.update (Function.update ρ₁ .f []) .t1
          ([bitSymbol (e.testBit ℓ)].reverse ++ (binSyms ℓ e).reverse) .sg) with hρ₃
  have h4 := twRuns_moveR (body := body) htg (a := .t1) (b := .f) (by decide) ρ₃
  have ht₃ : ρ₃ .t1 = (binSyms ℓ e).reverse := by simp [hρ₃]
  have hf₃ : ρ₃ .f = [] := by simp [hρ₃]
  rw [ht₃, hf₃, List.reverse_reverse, List.append_nil, List.length_reverse,
    length_binSyms] at h4
  set ρ₄ := Function.update (Function.update ρ₃ .t1 []) .f (binSyms ℓ e) with hρ₄
  -- 3. the block counter and the doubling loop
  have h5 := twRuns_ucopy (body := body) htg (a := .wn) (b := .c) (t := .t2) (by decide)
    (by decide) (by decide) ρ₄ (by simp [hρ₄, hρ₃, hρ₁, ht2])
  have hc₄ : ρ₄ .c = [] := by simp [hρ₄, hρ₃, hρ₁, hc]
  have hw₄ : (ρ₄ .wn).length = w := by simp [hρ₄, hρ₃, hρ₁, hwn]
  rw [hc₄, hw₄, List.append_nil] at h5
  set ρ₅ := Function.update ρ₄ .c (List.replicate w tick) with hρ₅
  have h6 := twRuns_dbl (body := body) htg (ℓ := ℓ) (w := w) (e := e) ρ₅
    (cstream A w rec).reverse (by simp [hX0]) (by simp [hρ₅, hρ₄, hρ₃, hρ₁, ht2])
    (by simp [hρ₅, hρ₄, hρ₃, hρ₁, ht3])
  have h6' := twRuns_congr_left h6 (ρ := ρ₅) (by
    funext r
    cases r <;> simp [twAT, twDblSt, hρ₅, hρ₄, hρ₃, hρ₁, htl, 
      Nat.mod_one])
  set ρ₆ := Function.update (Function.update (twDblSt ρ₅ (cstream A w rec).reverse w e ℓ) .f
    (binSyms ℓ e)) .t1 [] with hρ₆
  have h7 := twRuns_uclear (body := body) htg .c ρ₆
  have hc₆ : (ρ₆ .c).length = 2 ^ ℓ * w := by simp [hρ₆, twDblSt]
  rw [hc₆] at h7
  -- 4. the head onto `hd`
  have h8 := twRuns_moveR (body := body) htg (a := .x) (b := .hd) (by decide)
    (Function.update ρ₆ .c [])
  set s := e % 2 ^ ℓ with hs
  have hsr : s < 2 ^ ℓ := Nat.mod_lt _ (by positivity)
  have hsw : 2 ^ ℓ * w - w * s = (2 ^ ℓ - s) * w := by rw [Nat.sub_mul]; ring_nf
  have hx₆ : (Function.update ρ₆ .c [] .x).reverse = cstream A w (rec.take (2 ^ ℓ - s)) := by
    simp only [Function.update_apply, hρ₆, twDblSt]
    simp only [reduceCtorEq, ↓reduceIte]
    rw [List.drop_reverse, List.reverse_reverse, hX0, hsw, tw_cstream_take]
  have hx₆l : (Function.update ρ₆ .c [] .x).length = 2 ^ ℓ * w - w * s := by
    simp [hρ₆, twDblSt, hX0, ← hs]
  have hhd₆ : Function.update ρ₆ .c [] .hd = [] := by
    simp [hρ₆, twDblSt, hρ₅, hρ₄, hρ₃, hρ₁, hhd]
  rw [hx₆, hhd₆, List.append_nil, hx₆l] at h8
  set ρ₈ := Function.update (Function.update (Function.update ρ₆ .c []) .x []) .hd
    (cstream A w (rec.take (2 ^ ℓ - s))) with hρ₈
  -- 5. the sign step
  have h9 := twRuns_sign (body := body) htg hA hw ρ₈ (rec.drop (2 ^ ℓ - s)) (rec.take (2 ^ ℓ - s))
    (e.testBit ℓ)
    (by
      simp only [hρ₈, hρ₆, twDblSt, Function.update_apply, reduceCtorEq, ↓reduceIte]
      rw [List.take_reverse, List.reverse_reverse, hX0, hsw, tw_cstream_drop])
    (by simp [hρ₈])
    (by simp [hρ₈, hρ₆, twDblSt, hρ₅, hρ₄, hρ₃, hρ₁, hsg])
    (by simp [hρ₈, hρ₆, twDblSt, hρ₅, hρ₄, hρ₃, hρ₁, hwn])
    (by simp [hρ₈, hρ₆, twDblSt, hρ₅, hρ₄, hρ₃, hρ₁, ht2])
  have hlen : (rec.drop (2 ^ ℓ - s)).length + (rec.take (2 ^ ℓ - s)).length = 2 ^ ℓ := by
    simp [hrec]
  rw [hlen] at h9
  set ρ₉ := Function.update (Function.update (Function.update ρ₈ .tl []) .hd []) .acc
    ((cstream A w (if e.testBit ℓ = true then rec.drop (2 ^ ℓ - s) ++
      (rec.take (2 ^ ℓ - s)).map (fun z => -z)
      else (rec.drop (2 ^ ℓ - s)).map (fun z => -z) ++ rec.take (2 ^ ℓ - s))).reverse ++ ρ₈ .acc)
    with hρ₉
  -- 6. clear the exponent and the sign
  have h10 := twRuns_uclear (body := body) htg .f ρ₉
  have hf₉ : (ρ₉ .f).length = ℓ := by simp [hρ₉, hρ₈, hρ₆]
  rw [hf₉] at h10
  have h11 := twRuns_uclear (body := body) htg .sg (Function.update ρ₉ .f [])
  have hsg₉ : (Function.update ρ₉ .f [] .sg).length = 1 := by
    simp [hρ₉, hρ₈, hρ₆, twDblSt, hρ₅, hρ₄, hρ₃, hρ₁, hsg]
  rw [hsg₉] at h11
  -- assembly
  have hall := twRuns_seq h1 (twRuns_seq h2 (twRuns_seq h3 (twRuns_seq h4 (twRuns_seq h5
    (twRuns_seq h6' (twRuns_seq h7 (twRuns_seq h8 (twRuns_seq h9 (twRuns_seq h10 h11)))))))))
  refine twRuns_mono (twRuns_congr hall ?_) ?_
  · have hacc : ρ₈ .acc = ρ .acc := by simp [hρ₈, hρ₆, twDblSt, hρ₅, hρ₄, hρ₃, hρ₁]
    funext r
    cases r <;> simp [hρ₉, hρ₈, hρ₆, twDblSt, hρ₅, hρ₄, hρ₃, hρ₁, 
      twShiftL, ← hs, hx, htl, hhd, hc, hsg, ht1]
  · have := tw_sum_pow_two w ℓ
    have h2w : 2 ^ ℓ ≤ 2 ^ ℓ * w := Nat.le_mul_of_pos_right _ hw
    have hw2 : w ≤ 2 ^ ℓ * w := Nat.le_mul_of_pos_left _ (by positivity)
    have e1 : 2 ^ ℓ * (5 * w + 6) = 5 * (2 ^ ℓ * w) + 6 * 2 ^ ℓ := by ring
    have hsub : 2 ^ ℓ * w - w * s ≤ 2 ^ ℓ * w := Nat.sub_le _ _
    unfold twRecCost
    rw [show 33 * 2 ^ ℓ * w = 33 * (2 ^ ℓ * w) by ring, e1]
    omega

/-- Negating the exponent: `f := (2^L - e) mod 2^L`, `L = |u|`. -/
theorem twRuns_negE {u : TwReg} (hu : [u, TwReg.z, TwReg.f, TwReg.g, TwReg.t1, TwReg.t3, TwReg.t4,
      TwReg.t5].Nodup) {L e : ℕ} (ρ : TwReg → List (Fin (A + 4))) (hL : (ρ u).length = L)
    (hf : ρ .f = binSyms L e) (hz : ρ .z = []) (hg : ρ .g = []) (ht1 : ρ .t1 = [])
    (ht3 : ρ .t3 = []) (ht4 : ρ .t4 = []) (ht5 : ρ .t5 = []) :
    TwRuns body tg (twNegE tg u) ρ
      (Function.update ρ .f (binSyms L ((0 + 2 ^ L - e % 2 ^ L) % 2 ^ L))) (twNegECost L) := by
  have hu' := hu
  regs_ne hu'
  have h1 := twRuns_zeroBits (body := body) htg (len := u) (z := .z) (t := .t1) ‹u ≠ TwReg.z›
    ‹u ≠ TwReg.t1› (by decide) ρ ht1
  rw [hL, hz, List.append_nil] at h1
  have h2 := twRuns_bsub (body := body) htg (a := .z) (b := .f) (c := .g) (tx := .t3) (ty := .t4)
    (tz := .t5) (by decide) (cy := tg .cy) (htg.ne (by decide)) (htg.ne (by decide))
    (L := L) (x := 0) (y := e % 2 ^ L) (by positivity) (Nat.mod_lt _ (by positivity))
    (Function.update ρ .z (binSyms L 0)) (by simp) (by simp [hf, binSyms_mod]) (by simp [ht3])
    (by simp [ht4]) (by simp [ht5])
  have h3 := twRuns_uclear (body := body) htg .z
    (Function.update (Function.update ρ .z (binSyms L 0)) .g
      (binSyms L ((0 + 2 ^ L - e % 2 ^ L) % 2 ^ L) ++ Function.update ρ .z (binSyms L 0) .g))
  have h4 := twRuns_uclear (body := body) htg .f
    (Function.update (Function.update (Function.update ρ .z (binSyms L 0)) .g
      (binSyms L ((0 + 2 ^ L - e % 2 ^ L) % 2 ^ L) ++ Function.update ρ .z (binSyms L 0) .g)) .z [])
  have h5 := twRuns_moveR (body := body) htg (a := .g) (b := .t1) (by decide)
    (Function.update (Function.update (Function.update (Function.update ρ .z (binSyms L 0)) .g
      (binSyms L ((0 + 2 ^ L - e % 2 ^ L) % 2 ^ L) ++ Function.update ρ .z (binSyms L 0) .g)) .z [])
      .f [])
  have h6 := twRuns_moveR (body := body) htg (a := .t1) (b := .f) (by decide)
    (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update ρ .z (binSyms L 0)) .g
      (binSyms L ((0 + 2 ^ L - e % 2 ^ L) % 2 ^ L) ++ Function.update ρ .z (binSyms L 0) .g)) .z [])
      .f []) .g [])
      .t1 ((Function.update (Function.update (Function.update (Function.update ρ .z
      (binSyms L 0)) .g (binSyms L ((0 + 2 ^ L - e % 2 ^ L) % 2 ^ L) ++
      Function.update ρ .z (binSyms L 0) .g)) .z []) .f [] .g).reverse ++
      Function.update (Function.update (Function.update (Function.update ρ .z (binSyms L 0)) .g
      (binSyms L ((0 + 2 ^ L - e % 2 ^ L) % 2 ^ L) ++ Function.update ρ .z (binSyms L 0) .g)) .z [])
      .f [] .t1))
  refine twRuns_mono (twRuns_congr (twRuns_seq h1 (twRuns_seq h2 (twRuns_seq h3 (twRuns_seq h4
    (twRuns_seq h5 h6))))) ?_) ?_
  · funext r
    cases r <;> simp [hz, hg, ht1, Function.update_of_ne]
  · simp [hf, hg, ht1]
    unfold twNegECost
    omega

/-- **One record times `y^(-e)`**, `e` on `f` in `ℓ + 1` bits, `ℓ + 1` symbols on `hn`. -/
theorem twRecInv_runs (hA : 5 ≤ A) {ℓ w e : ℕ} (hw : 1 ≤ w) (ρ : TwReg → List (Fin (A + 4)))
    (rec : List GaussianInt) (rest : List (Fin (A + 4))) (hrec : rec.length = 2 ^ ℓ)
    (hsrc : ρ .src = cstream A w rec ++ rest) (hf : ρ .f = binSyms (ℓ + 1) e)
    (hhn : (ρ .hn).length = ℓ + 1) (hwn : (ρ .wn).length = w) (hrwn : (ρ .rwn).length = 2 ^ ℓ * w)
    (hx : ρ .x = []) (htl : ρ .tl = []) (hhd : ρ .hd = []) (hc : ρ .c = []) (hsg : ρ .sg = [])
    (hz : ρ .z = []) (hg : ρ .g = []) (ht1 : ρ .t1 = []) (ht2 : ρ .t2 = []) (ht3 : ρ .t3 = [])
    (ht4 : ρ .t4 = []) (ht5 : ρ .t5 = []) :
    TwRuns body tg (twRecInvP tg) ρ
      (Function.update (Function.update (Function.update ρ .src rest) .acc
        ((cstream A w (twShiftL ℓ ((2 * 2 ^ ℓ - e % (2 * 2 ^ ℓ)) % (2 * 2 ^ ℓ)) rec)).reverse ++
          ρ .acc)) .f [])
      (twNegECost (ℓ + 1) + twRecCost ℓ w) := by
  have h1 := twRuns_negE (body := body) htg (u := .hn) (by decide) ρ hhn hf hz hg ht1 ht3 ht4 ht5
  have h2 := twRec_runs (body := body) htg hA hw
    (e := (0 + 2 ^ (ℓ + 1) - e % 2 ^ (ℓ + 1)) % 2 ^ (ℓ + 1))
    (Function.update ρ .f (binSyms (ℓ + 1) ((0 + 2 ^ (ℓ + 1) - e % 2 ^ (ℓ + 1)) % 2 ^ (ℓ + 1))))
    rec rest hrec (by simp [hsrc]) (by simp) (by simp [hwn]) (by simp [hrwn]) (by simp [hx])
    (by simp [htl]) (by simp [hhd]) (by simp [hc]) (by simp [hsg]) (by simp [ht1]) (by simp [ht2])
    (by simp [ht3])
  refine twRuns_congr (twRuns_seq h1 h2) ?_
  rw [show 2 * 2 ^ ℓ = 2 ^ (ℓ + 1) by ring, Nat.zero_add]
  funext r
  cases r <;> simp

/-! ### Records given by their coefficient functions -/

/-- `y^e` on a record `Z : Fin (2^ℓ) → GaussianInt`. The new numerators `twShiftZ e Z` are those
of `shiftNegZ e` (`twShiftZ_toComplex`). -/
theorem twRec_runs_ofFn (hA : 5 ≤ A) {ℓ w e : ℕ} (hw : 1 ≤ w) (ρ : TwReg → List (Fin (A + 4)))
    (Z : Fin (2 ^ ℓ) → GaussianInt) (rest : List (Fin (A + 4)))
    (hsrc : ρ .src = cstream A w (List.ofFn Z) ++ rest) (hf : ρ .f = binSyms (ℓ + 1) e)
    (hwn : (ρ .wn).length = w) (hrwn : (ρ .rwn).length = 2 ^ ℓ * w)
    (hx : ρ .x = []) (htl : ρ .tl = []) (hhd : ρ .hd = []) (hc : ρ .c = []) (hsg : ρ .sg = [])
    (ht1 : ρ .t1 = []) (ht2 : ρ .t2 = []) (ht3 : ρ .t3 = []) :
    TwRuns body tg (twRecP tg) ρ
      (Function.update (Function.update (Function.update ρ .src rest) .acc
        ((cstream A w (List.ofFn (twShiftZ e Z))).reverse ++ ρ .acc)) .f [])
      (twRecCost ℓ w) := by
  have h := twRec_runs (body := body) htg hA hw ρ (List.ofFn Z) rest (by simp) hsrc hf hwn hrwn hx
    htl hhd hc hsg ht1 ht2 ht3
  rwa [twShiftL_ofFn] at h

end Runs

/-- `twShiftZ` at the negated exponent computes `shiftInv` on grid records. -/
theorem twShiftZ_shiftInv {r : ℕ} [NeZero r] (p e : ℕ) (Z : Fin r → GaussianInt) (i : Fin r) :
    GaussianInt.toComplex (twShiftZ ((2 * r - e % (2 * r)) % (2 * r)) Z i) / 2 ^ p =
      shiftInv e (fun c => GaussianInt.toComplex (Z c) / 2 ^ p) i := by
  rw [twShiftZ_toComplex]; rfl

section RunsInv

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {tg : TwReg → Fin T}
  (htg : Function.Injective tg)
include htg

/-- `y^(-e)` on a record `Z : Fin (2^ℓ) → GaussianInt`; the new numerators are those of
`shiftInv e` (`twShiftZ_shiftInv`). -/
theorem twRecInv_runs_ofFn (hA : 5 ≤ A) {ℓ w e : ℕ} (hw : 1 ≤ w) (ρ : TwReg → List (Fin (A + 4)))
    (Z : Fin (2 ^ ℓ) → GaussianInt) (rest : List (Fin (A + 4)))
    (hsrc : ρ .src = cstream A w (List.ofFn Z) ++ rest) (hf : ρ .f = binSyms (ℓ + 1) e)
    (hhn : (ρ .hn).length = ℓ + 1) (hwn : (ρ .wn).length = w) (hrwn : (ρ .rwn).length = 2 ^ ℓ * w)
    (hx : ρ .x = []) (htl : ρ .tl = []) (hhd : ρ .hd = []) (hc : ρ .c = []) (hsg : ρ .sg = [])
    (hz : ρ .z = []) (hg : ρ .g = []) (ht1 : ρ .t1 = []) (ht2 : ρ .t2 = []) (ht3 : ρ .t3 = [])
    (ht4 : ρ .t4 = []) (ht5 : ρ .t5 = []) :
    TwRuns body tg (twRecInvP tg) ρ
      (Function.update (Function.update (Function.update ρ .src rest) .acc
        ((cstream A w (List.ofFn (twShiftZ ((2 * 2 ^ ℓ - e % (2 * 2 ^ ℓ)) % (2 * 2 ^ ℓ)) Z))).reverse
          ++ ρ .acc)) .f [])
      (twNegECost (ℓ + 1) + twRecCost ℓ w) := by
  have h := twRecInv_runs (body := body) htg hA hw ρ (List.ofFn Z) rest (by simp) hsrc hf hhn hwn
    hrwn hx htl hhd hc hsg hz hg ht1 ht2 ht3 ht4 ht5
  rwa [twShiftL_ofFn] at h

end RunsInv

end IntegerMultBounds.MathlibTM2.Fast
