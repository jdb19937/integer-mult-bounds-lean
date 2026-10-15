module

public import IntegerMultBounds.MathlibTM2.Fast.TwiddleRec

/-!
# The twiddle exponent of a record address

`twExpP neg` computes on the empty register `f`, in `ℓ + 1` bits, the exponent of the record at
the address `n` held on `ad` (`binSyms N n`, `N = es.sum`, least significant bit on top) in the
round at named position `h` of the transform with axis exponents `es` and `r = 2^ℓ`:
`E = twE es r h (parts es h) n mod 2r` (`neg = false`, the opposite twiddle `y^E`), or
`(2r - E mod 2r) mod 2r` (`neg = true`, the forward twiddle `y^(-E)`, `shiftInv`).

**Parameters.** `rl` holds the roles of the address bits in round `h`, `twRoles A es h`
(`Fast/TwiddleMath`: per axis from the least significant, `h` symbols `bitSymbol true` for the
low bits, one `separator` for bit `h` and `bitSymbol false` for the other bits of a participating
axis, `bitSymbol false` for every bit of the others); `hn` holds `h + 1` symbols, `lh` holds
`ℓ - h` symbols (`h ≤ ℓ`). All three are restored, and so is `ad`.

**Algorithm.**
1. `f := binSyms (h + 1) 0` (`zeroBits` against `hn`).
2. Scan the roles (`scanP` over `rl`, `twRoleBody`): each step moves one address bit from `ad`
   onto `as`; a `low` bit is also pushed onto `v`; at a `sel` bit with value `1`, `vp` receives a
   `0` and then `v` (so `vp = binSyms (h + 1) (xᵢ mod 2^h)`), `f := (f + vp) mod 2^(h+1)`
   (`baddTo`) and `vp` is cleared; at a `sel` bit with value `0`, `v` is cleared. This is the
   scan `twStep h` of `Fast/TwiddleMath`, so `f` ends with `F = twF h es n mod 2^(h+1)`
   (`twFold_roles`); `twGood_roles` provides the `h` low bits at every `sel`.
3. `ad := as` reversed (the address is restored).
4. (`neg`) `f := (2^(h+1) - F) mod 2^(h+1)` (`twNegE`).
5. Push `ℓ - h` zero bits onto `f`: `f = binSyms (ℓ + 1) (2^(ℓ-h) F)`, which is the exponent
   modulo `2r` (`twE_mod`, `twE_neg_mod`).

**Result** (`twExp_runs`): `f` gains `binSyms (ℓ + 1) (twEx neg es ℓ h n)` and every other
register ends as it started. Scratch (empty before and after): `f`, `v`, `vp`, `as`, `t1`, `t3`,
`t4`, `t5`, and for `neg` also `z`, `g`. Scan slot `tg .cy` serves as the carry.

**Cost** (`twExpCost N h ℓ = N (12 h + 33) + 24 h + 4 ℓ + 70`): `O(N h + ℓ)`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Mult.Rounds

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

section Programs

variable {T Q A : ℕ} {U P : Type} (tg : TwReg → Fin T)

/-- At a `sel` bit `1`: `vp := 0 :: …` and the low bits of `v`, then `f := f + vp`. -/
def twSelAdd : Pr P T Q A U :=
  .seq (.act (.push (.rt (tg .vp)) (fun _ => bitSymbol false) .done)) <|
  .seq (moveR (tg .v) (tg .vp) id) <|
  .seq (baddTo (tg .f) (tg .vp) (tg .t3) (tg .t4) (tg .t5) (tg .cy)) (uclear (tg .vp))

/-- One step of the role scan, the role in `sym`. -/
def twRoleBody : Pr P T Q A U :=
  .cond (fun v => decide (v.sym.getD blank = separator))
    (.seq (.act (twMvTop (tg .ad) (tg .as) .done))
      (.cond (fun v => symBit (v.sym.getD blank)) (twSelAdd tg) (uclear (tg .v))))
    (.cond (fun v => decide (v.sym.getD blank = bitSymbol true))
      (.act (twMvTop2 (tg .ad) (tg .as) (tg .v)))
      (.act (twMvTop (tg .ad) (tg .as) .done)))

/-- **The exponent of the record at the address on `ad`**, onto `f` in `ℓ + 1` bits; negated
modulo `2r` when `neg`. -/
def twExpP (neg : Bool) : Pr P T Q A U :=
  .seq (zeroBits (tg .hn) (tg .f) (tg .t1)) <|
  .seq (scanP (tg .rl) (tg .t1) (twRoleBody tg)) <|
  .seq (moveR (tg .as) (tg .ad) id) <|
  if neg then .seq (twNegE tg .hn) (zeroBits (tg .lh) (tg .f) (tg .t1))
  else zeroBits (tg .lh) (tg .f) (tg .t1)

end Programs

/-- The exponent computed by `twExpP neg`: `E mod 2r`, or `(2r - E mod 2r) mod 2r` for `neg`. -/
def twEx (neg : Bool) (es : List ℕ) (ℓ h n : ℕ) : ℕ :=
  if neg then (2 * 2 ^ ℓ - twE es (2 ^ ℓ) h (parts es h) n % (2 * 2 ^ ℓ)) % (2 * 2 ^ ℓ)
  else twE es (2 ^ ℓ) h (parts es h) n % (2 * 2 ^ ℓ)

lemma twEx_false (es : List ℕ) (ℓ h n : ℕ) :
    twEx false es ℓ h n = twE es (2 ^ ℓ) h (parts es h) n % (2 * 2 ^ ℓ) := rfl

lemma twEx_true (es : List ℕ) (ℓ h n : ℕ) :
    twEx true es ℓ h n =
      (2 * 2 ^ ℓ - twE es (2 ^ ℓ) h (parts es h) n % (2 * 2 ^ ℓ)) % (2 * 2 ^ ℓ) := rfl

/-- The step bound of `twExpP` for `N` address bits. -/
def twExpCost (N h ℓ : ℕ) : ℕ := N * (12 * h + 33) + 24 * h + 4 * ℓ + 70

lemma tw_binSyms_shift {A : ℕ} (k L y : ℕ) :
    (binSyms k 0 ++ binSyms L y : List (Fin (A + 4))) = binSyms (k + L) (2 ^ k * y) := by
  induction k with
  | zero => simp [binSyms]
  | succ k ih =>
      rw [binSyms_succ, List.cons_append, Nat.zero_div, ih,
        show k + 1 + L = (k + L) + 1 by ring, binSyms_succ]
      congr 2
      · simp [pow_succ, Nat.testBit_zero, Nat.mul_assoc, Nat.mul_mod_right,
          Nat.mul_left_comm _ 2]
      · rw [pow_succ, show 2 ^ k * 2 * y = 2 * (2 ^ k * y) by ring,
          Nat.mul_div_cancel_left _ two_pos]

section Runs

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {tg : TwReg → Fin T}
  (htg : Function.Injective tg)
include htg

/-- The file after one scan step on the role `x` and the address bit `b`. -/
def twRoleSt (h : ℕ) (R : TwReg → List (Fin (A + 4))) (rest : List (Fin (A + 4)))
    (s : List Bool × ℕ) (x : Fin (A + 4)) (b : Bool) : TwReg → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update R .ad rest) .as
    (bitSymbol b :: R .as)) .v ((twStep h s (x, b)).1.map bitSymbol)) .f
    (binSyms (h + 1) (twStep h s (x, b)).2)

/-- One step of the role scan. -/
theorem twRuns_roleStep {h : ℕ} (R : TwReg → List (Fin (A + 4))) (rest : List (Fin (A + 4)))
    (V : List Bool) (F : ℕ) (x : Fin (A + 4)) (b : Bool) (hpre : twPre h (x, b) (V, F))
    (had : R .ad = bitSymbol b :: rest) (hv : R .v = V.map bitSymbol)
    (hf : R .f = binSyms (h + 1) F) (hvp : R .vp = []) (ht3 : R .t3 = []) (ht4 : R .t4 = [])
    (ht5 : R .t5 = []) :
    TwRunsS body tg (twRoleBody tg) x R (twRoleSt h R rest (V, F) x b) (12 * h + 26) := by
  by_cases hx : x = separator
  · subst hx
    obtain ⟨hVl, hF⟩ := hpre rfl
    set R₁ := Function.update (Function.update R .ad rest) .as (bitSymbol b :: R .as) with hR₁
    have hq : TwRunsS body tg (.cond (fun v => symBit (v.sym.getD blank)) (twSelAdd tg)
        (uclear (tg .v))) (bitSymbol b) R₁ (twRoleSt h R rest (V, F) separator b) (12 * h + 24) := by
      cases b with
      | false =>
          have hcl : TwRuns body tg (uclear (tg .v)) R₁ (twRoleSt h R rest (V, F) separator false)
              (12 * h + 23) := by
            refine twRuns_mono (twRuns_congr (twRuns_uclear (body := body) htg .v R₁) ?_) ?_
            · funext r
              cases r <;> simp [twRoleSt, twStep, Function.update_apply, hR₁, hf]
            · simp [hR₁, hv, hVl]; omega
          exact twRunsS_cond_false (fun v hv => by simp [hv]) (twRunsS_of hcl)
      | true =>
          have hlt : twVal V.reverse < 2 ^ (h + 1) := by
            have h1 := twVal_lt V.reverse
            rw [List.length_reverse, hVl] at h1
            exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by omega))
          have h1 := twRuns_push (body := body) htg .vp (bitSymbol false) R₁
          have h2 := twRuns_moveR (body := body) htg (a := .v) (b := .vp) (by decide)
            (Function.update R₁ .vp (bitSymbol false :: R₁ .vp))
          have hvp' : (Function.update R₁ .vp (bitSymbol false :: R₁ .vp) .v).reverse ++
              Function.update R₁ .vp (bitSymbol false :: R₁ .vp) .vp =
              binSyms (h + 1) (twVal V.reverse) := by
            simp only [Function.update_apply, hR₁, reduceCtorEq, ↓reduceIte, hv, hvp]
            rw [← List.map_reverse, show [bitSymbol false] = ([false] : List Bool).map
              (bitSymbol (a := A)) from rfl, ← List.map_append, tw_map_bitSymbol,
              List.length_append, List.length_reverse, hVl, twVal_append_false]
            rfl
          rw [hvp'] at h2
          have h3 := twRuns_baddTo (body := body) htg (a := .f) (b := .vp) (tx := .t3) (ty := .t4)
            (tz := .t5) (by decide) (cy := tg .cy) (htg.ne (by decide)) (htg.ne (by decide))
            (L := h + 1) (x := F) (y := twVal V.reverse) hF hlt
            (Function.update (Function.update (Function.update R₁ .vp (bitSymbol false :: R₁ .vp))
              .v []) .vp (binSyms (h + 1) (twVal V.reverse)))
            (by simp [hR₁, hf]) (by simp) (by simp [hR₁, ht3]) (by simp [hR₁, ht4])
            (by simp [hR₁, ht5])
          have h4 := twRuns_uclear (body := body) htg .vp
            (Function.update (Function.update (Function.update (Function.update R₁ .vp
              (bitSymbol false :: R₁ .vp)) .v []) .vp (binSyms (h + 1) (twVal V.reverse))) .f
              (binSyms (h + 1) ((F + twVal V.reverse) % 2 ^ (h + 1))))
          have hsel : TwRuns body tg (twSelAdd tg) R₁ (twRoleSt h R rest (V, F) separator true)
              (12 * h + 23) := by
            refine twRuns_mono (twRuns_congr (twRuns_seq h1 (twRuns_seq h2 (twRuns_seq h3 h4)))
              ?_) ?_
            · funext r
              cases r <;> simp [twRoleSt, twStep, Function.update_apply, hR₁, hvp]
            · simp [hR₁, hv, hVl]; omega
          exact twRunsS_cond_true (fun v hv => by simp [hv]) (twRunsS_of hsel)
    have hin := twRuns_mvTop_seqS (body := body) htg (src := .ad) (dst := .as) (by decide) had hq
    exact twRunsS_mono (twRunsS_cond_true (fun v hv => by simp [hv]) (twRunsS_of hin)) (by omega)
  · by_cases hl : x = bitSymbol true
    · subst hl
      have hin : TwRuns body tg (.act (twMvTop2 (tg .ad) (tg .as) (tg .v))) R
          (twRoleSt h R rest (V, F) (bitSymbol true) b) 1 := by
        refine twRuns_congr (twRuns_mvTop2 (body := body) htg (src := .ad) (d₁ := .as) (d₂ := .v)
          (by decide) (by decide) (by decide) had) ?_
        funext r
        cases r <;> simp [twRoleSt, twStep, hx, Function.update_apply, hv, hf]
      exact twRunsS_mono (twRunsS_cond_false (fun v hv => by simp [hv, tw_sep_ne_true.symm])
        (twRunsS_cond_true (fun v hv => by simp [hv]) (twRunsS_of hin))) (by omega)
    · have hin : TwRuns body tg (.act (twMvTop (tg .ad) (tg .as) .done)) R
          (twRoleSt h R rest (V, F) x b) 1 := by
        refine twRuns_congr (twRuns_mvTop (body := body) htg (src := .ad) (dst := .as) (by decide)
          had) ?_
        funext r
        cases r <;> simp [twRoleSt, twStep, hx, hl, Function.update_apply, hv, hf]
      exact twRunsS_mono (twRunsS_cond_false (fun v hv => by simp [hv, hx])
        (twRunsS_cond_false (fun v hv => by simp [hv, hl]) (twRunsS_of hin))) (by omega)

/-- The file of the role scan after `j` address bits. -/
def twScanSt (h : ℕ) (ρ : TwReg → List (Fin (A + 4))) (L : List (Fin (A + 4) × Bool))
    (bits : List Bool) (j : ℕ) : TwReg → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update ρ .ad
    ((bits.drop j).map bitSymbol)) .as ((bits.take j).reverse.map bitSymbol)) .v
    ((twSt h L ([], 0) j).1.map bitSymbol)) .f (binSyms (h + 1) (twSt h L ([], 0) j).2)

/-- **The role scan.** -/
theorem twRuns_roleScan {es : List ℕ} {h n : ℕ} (ρ : TwReg → List (Fin (A + 4)))
    (hrl : ρ .rl = twRoles A es h) (had : ρ .ad = binSyms es.sum n)
    (hf : ρ .f = binSyms (h + 1) 0) (hv : ρ .v = []) (hvp : ρ .vp = []) (has : ρ .as = [])
    (ht1 : ρ .t1 = []) (ht3 : ρ .t3 = []) (ht4 : ρ .t4 = []) (ht5 : ρ .t5 = []) :
    TwRuns body tg (scanP (tg .rl) (tg .t1) (twRoleBody tg)) ρ
      (Function.update (Function.update (Function.update ρ .ad []) .as
        ((binBits es.sum n).reverse.map bitSymbol)) .f
        (binSyms (h + 1) (twF h es n % 2 ^ (h + 1))))
      (es.sum * (12 * h + 29) + 2 * es.sum + 4) := by
  set l := twRoles A es h with hl
  set bits := binBits es.sum n with hbits
  set L := l.zip bits with hL
  have hll : l.length = es.sum := twRoles_length es h
  have hbl : bits.length = es.sum := length_binBits _ _
  have hLl : L.length = es.sum := by simp [hL, hll, hbl]
  have hgood := twGood_roles (A := A) h es n 0 (by positivity)
  rw [← hl, ← hbits, ← hL] at hgood
  have hsc := twRuns_scanP (body := body) htg (a := .rl) (t := .t1) (by decide)
    (p := twRoleBody tg) l (twScanSt h ρ L bits) (fun _ => 12 * h + 26) ?_
  · refine twRuns_mono (twRuns_congr (twRuns_congr_left hsc ?_) ?_) ?_
    · funext r
      cases r <;> simp [Function.update_apply, twAT, twScanSt, twSt, hrl, had, hf, hv, has, ht1,
        binSyms_eq, ← hl, ← hbits]
    · have hfin : twSt h L ([], 0) l.length = ([], twF h es n % 2 ^ (h + 1)) := by
        unfold twSt
        rw [hll, ← hLl, List.take_length, hL, hl, hbits, twFold_roles h es n 0 (by positivity),
          Nat.zero_add]
      simp only [twScanSt, hfin]
      rw [hll, ← hbl]
      funext r
      cases r <;> simp [Function.update_apply, hrl, hv, ht1]
    · simp [Finset.sum_const, hll]
  · intro j hj
    have hjb : j < bits.length := by omega
    have hjL : j < L.length := by omega
    have hpre := hgood j hjL
    rw [List.getElem_zip] at hpre
    have had' : twATin .rl .t1 l (twScanSt h ρ L bits) j .ad =
        bitSymbol bits[j] :: (bits.drop (j + 1)).map bitSymbol := by
      simp only [twATin, twScanSt, Function.update_apply, reduceCtorEq, ↓reduceIte]
      rw [List.drop_eq_getElem_cons hjb, List.map_cons]
    have hstep := twRuns_roleStep (body := body) htg (h := h)
      (twATin .rl .t1 l (twScanSt h ρ L bits) j) ((bits.drop (j + 1)).map bitSymbol)
      (twSt h L ([], 0) j).1 (twSt h L ([], 0) j).2 l[j] bits[j] hpre had'
      (by simp [twATin, twScanSt]) (by simp [twATin, twScanSt])
      (by simp [twATin, twScanSt, hvp]) (by simp [twATin, twScanSt, ht3])
      (by simp [twATin, twScanSt, ht4]) (by simp [twATin, twScanSt, ht5])
    refine twRunsS_congr hstep ?_
    have hsucc := twSt_succ h L ([], 0) hjL
    rw [List.getElem_zip] at hsucc
    have htk : (bits.take (j + 1)).reverse.map bitSymbol =
        (bitSymbol bits[j] : Fin (A + 4)) :: (bits.take j).reverse.map bitSymbol := by
      rw [List.take_add_one, List.getElem?_eq_getElem hjb, Option.toList_some]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.map_append, List.map_cons, List.map_nil, List.singleton_append]
    funext r
    cases r <;> simp [Function.update_apply, twRoleSt, twAT, twATin, twScanSt, hsucc, htk]

/-- **The exponent of the record at the address on `ad`.** -/
theorem twExp_runs (neg : Bool) {es : List ℕ} {ℓ h n : ℕ} (hh : h ≤ ℓ)
    (ρ : TwReg → List (Fin (A + 4))) (hrl : ρ .rl = twRoles A es h)
    (had : ρ .ad = binSyms es.sum n) (hhn : (ρ .hn).length = h + 1)
    (hlh : (ρ .lh).length = ℓ - h) (hf : ρ .f = []) (hv : ρ .v = []) (hvp : ρ .vp = [])
    (has : ρ .as = []) (ht1 : ρ .t1 = []) (ht3 : ρ .t3 = []) (ht4 : ρ .t4 = []) (ht5 : ρ .t5 = [])
    (hz : ρ .z = []) (hg : ρ .g = []) :
    TwRuns body tg (twExpP tg neg) ρ (Function.update ρ .f (binSyms (ℓ + 1) (twEx neg es ℓ h n)))
      (twExpCost es.sum h ℓ) := by
  set Fm := twF h es n % 2 ^ (h + 1) with hFm
  have h1 := twRuns_zeroBits (body := body) htg (len := .hn) (z := .f) (t := .t1) (by decide)
    (by decide) (by decide) ρ ht1
  rw [hhn, hf, List.append_nil] at h1
  have h2 := twRuns_roleScan (body := body) htg (es := es) (h := h) (n := n)
    (Function.update ρ .f (binSyms (h + 1) 0)) (by simp [hrl]) (by simp [had]) (by simp)
    (by simp [hv]) (by simp [hvp]) (by simp [has]) (by simp [ht1]) (by simp [ht3])
    (by simp [ht4]) (by simp [ht5])
  have h3 := twRuns_moveR (body := body) htg (a := .as) (b := .ad) (by decide)
    (Function.update (Function.update (Function.update (Function.update ρ .f (binSyms (h + 1) 0))
      .ad []) .as ((binBits es.sum n).reverse.map bitSymbol)) .f (binSyms (h + 1) Fm))
  have hρ₃ : Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update ρ .f (binSyms (h + 1) 0)) .ad []) .as
      ((binBits es.sum n).reverse.map bitSymbol)) .f (binSyms (h + 1) Fm)) .as []) .ad
      ((Function.update (Function.update (Function.update (Function.update ρ .f
        (binSyms (h + 1) 0)) .ad []) .as ((binBits es.sum n).reverse.map bitSymbol)) .f
        (binSyms (h + 1) Fm) .as).reverse ++
      Function.update (Function.update (Function.update (Function.update ρ .f
        (binSyms (h + 1) 0)) .ad []) .as ((binBits es.sum n).reverse.map bitSymbol)) .f
        (binSyms (h + 1) Fm) .ad) = Function.update ρ .f (binSyms (h + 1) Fm) := by
    funext r
    cases r <;> simp [Function.update_apply, had, has, binSyms_eq, ← List.map_reverse]
  rw [hρ₃] at h3
  have hc23 : (Function.update (Function.update (Function.update (Function.update ρ .f
      (binSyms (h + 1) 0)) .ad []) .as ((binBits es.sum n).reverse.map bitSymbol)) .f
      (binSyms (h + 1) Fm) .as).length = es.sum := by simp
  rw [hc23] at h3
  have hpow : 2 ^ (ℓ - h) * Fm < 2 ^ (ℓ + 1) := by
    have : Fm < 2 ^ (h + 1) := Nat.mod_lt _ (by positivity)
    calc 2 ^ (ℓ - h) * Fm < 2 ^ (ℓ - h) * 2 ^ (h + 1) := by
          exact Nat.mul_lt_mul_of_pos_left this (by positivity)
      _ = 2 ^ (ℓ + 1) := by rw [← pow_add]; congr 1; omega
  cases neg with
  | false =>
      have h4 := twRuns_zeroBits (body := body) htg (len := .lh) (z := .f) (t := .t1) (by decide)
        (by decide) (by decide) (Function.update ρ .f (binSyms (h + 1) Fm)) (by simp [ht1])
      have hf4 : binSyms ((Function.update ρ .f (binSyms (h + 1) Fm) .lh).length) 0 ++
          Function.update ρ .f (binSyms (h + 1) Fm) .f =
          (binSyms (ℓ + 1) (twEx false es ℓ h n) : List (Fin (A + 4))) := by
        simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hlh]
        rw [tw_binSyms_shift, show ℓ - h + (h + 1) = ℓ + 1 by omega, twEx_false, twE_mod hh]
      rw [hf4] at h4
      refine twRuns_mono (twRuns_congr (twRuns_seq h1 (twRuns_seq h2 (twRuns_seq h3 h4))) ?_) ?_
      · funext r; cases r <;> simp [Function.update_apply]
      · simp [hlh]
        unfold twExpCost
        rw [show es.sum * (12 * h + 33) = es.sum * (12 * h + 29) + 4 * es.sum by ring]
        generalize es.sum * (12 * h + 29) = K
        omega
  | true =>
      have h4 := twRuns_negE (body := body) htg (u := .hn) (by decide) (L := h + 1) (e := Fm)
        (Function.update ρ .f (binSyms (h + 1) Fm)) (by simp [hhn]) (by simp) (by simp [hz])
        (by simp [hg]) (by simp [ht1]) (by simp [ht3]) (by simp [ht4]) (by simp [ht5])
      have h5 := twRuns_zeroBits (body := body) htg (len := .lh) (z := .f) (t := .t1) (by decide)
        (by decide) (by decide) (Function.update (Function.update ρ .f (binSyms (h + 1) Fm)) .f
          (binSyms (h + 1) ((0 + 2 ^ (h + 1) - Fm % 2 ^ (h + 1)) % 2 ^ (h + 1)))) (by simp [ht1])
      have hf5 : binSyms ((Function.update (Function.update ρ .f (binSyms (h + 1) Fm)) .f
            (binSyms (h + 1) ((0 + 2 ^ (h + 1) - Fm % 2 ^ (h + 1)) % 2 ^ (h + 1))) .lh).length) 0 ++
          Function.update (Function.update ρ .f (binSyms (h + 1) Fm)) .f
            (binSyms (h + 1) ((0 + 2 ^ (h + 1) - Fm % 2 ^ (h + 1)) % 2 ^ (h + 1))) .f =
          (binSyms (ℓ + 1) (twEx true es ℓ h n) : List (Fin (A + 4))) := by
        simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hlh]
        rw [tw_binSyms_shift, show ℓ - h + (h + 1) = ℓ + 1 by omega, twEx_true,
          twE_neg_mod hh, hFm, Nat.mod_mod]
      rw [hf5] at h5
      refine twRuns_mono (twRuns_congr (twRuns_seq h1 (twRuns_seq h2 (twRuns_seq h3
        (twRuns_seq h4 h5)))) ?_) ?_
      · funext r; cases r <;> simp [Function.update_apply]
      · simp [hlh]
        unfold twExpCost twNegECost
        rw [show es.sum * (12 * h + 33) = es.sum * (12 * h + 29) + 4 * es.sum by ring]
        generalize es.sum * (12 * h + 29) = K
        omega

end Runs

end IntegerMultBounds.MathlibTM2.Fast
