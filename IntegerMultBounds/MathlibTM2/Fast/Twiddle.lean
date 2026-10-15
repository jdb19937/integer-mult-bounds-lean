module

public import IntegerMultBounds.MathlibTM2.Fast.TwiddleExp

/-!
# The twiddle pass

`twPassP tg fwd` multiplies every record of a stream by the twiddle monomial of the round at
named position `h` of the synthetic transforms with axis exponents `es`: the record at address `n`
by `y^(-E_h(n))` (`fwd = true`, the twiddle of `fwdRound`, `mulYInv`, `twFwdFlat`) or by
`y^(E_h(n))` (`fwd = false`, the twiddle of `oppRound`, `mulY`, `twOppFlat`), modulo `y^r + 1`,
`r = 2^ℓ`, `E_h = twE es r h (parts es h)` (`Mult/RoundsBasic`).

**Formats.** A record is `r` coefficients, each `w` pair symbols (`cstream A w`); the stream of
the records at the addresses `ns` with numerators `Z n : Fin r → GaussianInt` is
`twStream A w ns Z`. The address of a record is `n` in binary, bit `h` of axis `i` being bit
`off es i + h` of `n` (`Mult/RoundsBasic`).

**Registers** (`TwReg`, layout `tg` injective):
* `src`: the stream `twStream A w (List.range' n₀ M) Z` (consumed); `dst`: gains the output
  stream on top;
* `ad`: the address counter, `binSyms N n₀` with `N = es.sum` (ends at `binSyms N (n₀ + M)`);
* parameters, restored: `rl` the roles of the address bits in round `h` (`twRoles A es h`),
  `hn` (`h + 1` symbols), `lh` (`ℓ - h` symbols), `wn` (`w` symbols), `rwn` (`r w` symbols);
* scratch, empty before and after: `acc`, `x`, `tl`, `hd`, `c`, `v`, `vp`, `f`, `g`, `z`, `sg`,
  `as`, `t1` … `t5`; scan slots `tg .cy`, `tg .st`.

**Algorithm.** While `src` is nonempty (`twWhile`): compute the exponent `e` of the address on
`ad` modulo `2r` onto `f` (`twExpP`, negated for `fwd`), multiply the record on top of `src` by
`y^e` onto `acc` (`twRecP`), and increment `ad` (`countIter`). Finally `acc` moves onto `dst`.

**Results.**
* `twPass_runs`: `dst` gains `twStream A w (List.range' n₀ M) (fun n => twShiftZ (twEx fwd es ℓ h n)
  (Z n))`, `src` ends empty, `ad` holds `binSyms N (n₀ + M)`, every other register ends as it
  started, within `twPassCost N h ℓ w M` steps.
* `twEnc_twShiftZ`: on grid values (`TwEnc p Z u`: `u n c = Z n c / 2^p`), the output numerators
  encode `mulYInv (twE es r h (parts es h)) u` (`fwd`) or `mulY (twE es r h (parts es h)) u`;
  `twPass_recs` combines both. `twFwdFlat_flat`, `twOppFlat_flat`: on the flattened arrays these
  are `twFwdFlat es h (flat N u)` and `twOppFlat es h (flat N u)`.
* `twPassCost_le`: `twPassCost N h ℓ w M ≤ M (35 r w + 50 (N + 1)(ℓ + 3)) + 4`, and
  `twPassCost_le_sq`: `≤ M (485 r w + 50 (N + 1)^2) + 4`, for `h ≤ ℓ`, `1 ≤ w`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.NLogN IntegerMultBounds.Spec.SignedRingProduct IntegerMultBounds.MathlibTM2.Mult.Rounds

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

section Programs

variable {T Q A : ℕ} {U P : Type} (tg : TwReg → Fin T)

/-- One record: its exponent, the product, the next address. -/
def twStepP (fwd : Bool) : Pr P T Q A U :=
  .seq (twExpP tg fwd) (.seq (twRecP tg) (countIter (tg .ad) (tg .t1) (tg .cy)))

/-- **The twiddle pass**: `y^(-E_h)` (`fwd`) or `y^(E_h)` on every record of `src`, onto `dst`. -/
def twPassP (fwd : Bool) : Pr P T Q A U :=
  .seq (twWhile (tg .src) (twStepP tg fwd)) (moveR (tg .acc) (tg .dst) id)

end Programs

/-- The stream of the records at the addresses `ns` with numerators `Z`. -/
def twStream (A w : ℕ) {r : ℕ} (ns : List ℕ) (Z : ℕ → Fin r → GaussianInt) :
    List (Fin (A + 4)) :=
  ns.flatMap fun n => cstream A w (List.ofFn (Z n))

/-- The step bound of `twPassP` on `M` records with `N` address bits. -/
def twPassCost (N h ℓ w M : ℕ) : ℕ :=
  M * (twExpCost N h ℓ + twRecCost ℓ w + 4 * N + 5 + 2) + 2 + (2 * (M * (2 ^ ℓ * w)) + 2)

lemma twStream_length (A w : ℕ) {ℓ : ℕ} (ns : List ℕ) (Z : ℕ → Fin (2 ^ ℓ) → GaussianInt) :
    (twStream A w ns Z).length = ns.length * (2 ^ ℓ * w) := by
  induction ns with
  | nil => simp [twStream]
  | cons n ns ih =>
      rw [show twStream A w (n :: ns) Z = cstream A w (List.ofFn (Z n)) ++ twStream A w ns Z from
        List.flatMap_cons, List.length_append, ih, length_cstream, List.length_ofFn,
        List.length_cons]
      ring

@[simp] lemma twStream_nil (A w : ℕ) {r : ℕ} (Z : ℕ → Fin r → GaussianInt) :
    twStream A w [] Z = [] := rfl

section Runs

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {tg : TwReg → Fin T}
  (htg : Function.Injective tg)
include htg

/-- The register file of the pass after `j` records. -/
def twPassSt (ρ : TwReg → List (Fin (A + 4))) (w N n₀ M : ℕ) {r : ℕ}
    (Z Z' : ℕ → Fin r → GaussianInt) (j : ℕ) : TwReg → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update ρ .src
    (twStream A w (List.range' (n₀ + j) (M - j)) Z)) .acc
    ((twStream A w (List.range' n₀ j) Z').reverse ++ ρ .acc)) .ad (binSyms N (n₀ + j))

/-- **The twiddle pass.** -/
theorem twPass_runs (fwd : Bool) (hA : 5 ≤ A) {es : List ℕ} {ℓ h w n₀ M : ℕ} (hw : 1 ≤ w)
    (hh : h ≤ ℓ) (Z : ℕ → Fin (2 ^ ℓ) → GaussianInt) (ρ : TwReg → List (Fin (A + 4)))
    (hsrc : ρ .src = twStream A w (List.range' n₀ M) Z) (had : ρ .ad = binSyms es.sum n₀)
    (hrl : ρ .rl = twRoles A es h) (hwn : (ρ .wn).length = w)
    (hrwn : (ρ .rwn).length = 2 ^ ℓ * w) (hhn : (ρ .hn).length = h + 1)
    (hlh : (ρ .lh).length = ℓ - h) (hacc : ρ .acc = []) (hx : ρ .x = []) (htl : ρ .tl = [])
    (hhd : ρ .hd = []) (hc : ρ .c = []) (hv : ρ .v = []) (hvp : ρ .vp = []) (hf : ρ .f = [])
    (hg : ρ .g = []) (hz : ρ .z = []) (hsg : ρ .sg = []) (has : ρ .as = []) (ht1 : ρ .t1 = [])
    (ht2 : ρ .t2 = []) (ht3 : ρ .t3 = []) (ht4 : ρ .t4 = []) (ht5 : ρ .t5 = []) :
    TwRuns body tg (twPassP tg fwd) ρ
      (Function.update (Function.update (Function.update ρ .src []) .ad
        (binSyms es.sum (n₀ + M))) .dst
        (twStream A w (List.range' n₀ M) (fun n => twShiftZ (twEx fwd es ℓ h n) (Z n)) ++ ρ .dst))
      (twPassCost es.sum h ℓ w M) := by
  set Z' : ℕ → Fin (2 ^ ℓ) → GaussianInt := fun n => twShiftZ (twEx fwd es ℓ h n) (Z n) with hZ'
  set st := twPassSt ρ w es.sum n₀ M Z Z' with hst
  have hstep : ∀ j < M, TwRuns body tg (twStepP tg fwd) (st j) (st (j + 1))
      (twExpCost es.sum h ℓ + twRecCost ℓ w + (4 * es.sum + 5)) := by
    intro j hj
    have h1 := twExp_runs (body := body) htg fwd (es := es) (ℓ := ℓ) (h := h) (n := n₀ + j) hh
      (st j) (by simp [hst, twPassSt, hrl]) (by simp [hst, twPassSt])
      (by simp [hst, twPassSt, hhn]) (by simp [hst, twPassSt, hlh]) (by simp [hst, twPassSt, hf])
      (by simp [hst, twPassSt, hv]) (by simp [hst, twPassSt, hvp])
      (by simp [hst, twPassSt, has]) (by simp [hst, twPassSt, ht1])
      (by simp [hst, twPassSt, ht3]) (by simp [hst, twPassSt, ht4])
      (by simp [hst, twPassSt, ht5]) (by simp [hst, twPassSt, hz]) (by simp [hst, twPassSt, hg])
    have hsrcj : (Function.update (st j) .f (binSyms (ℓ + 1) (twEx fwd es ℓ h (n₀ + j)))) .src =
        cstream A w (List.ofFn (Z (n₀ + j))) ++
          twStream A w (List.range' (n₀ + (j + 1)) (M - (j + 1))) Z := by
      simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hst, twPassSt]
      rw [show M - j = (M - (j + 1)) + 1 by omega, List.range'_succ]
      simp [twStream, Nat.add_assoc]
    have h2 := twRec_runs_ofFn (body := body) htg hA hw (e := twEx fwd es ℓ h (n₀ + j))
      (Function.update (st j) .f (binSyms (ℓ + 1) (twEx fwd es ℓ h (n₀ + j))))
      (Z (n₀ + j)) _ hsrcj (by simp) (by simp [hst, twPassSt, hwn])
      (by simp [hst, twPassSt, hrwn]) (by simp [hst, twPassSt, hx]) (by simp [hst, twPassSt, htl])
      (by simp [hst, twPassSt, hhd]) (by simp [hst, twPassSt, hc]) (by simp [hst, twPassSt, hsg])
      (by simp [hst, twPassSt, ht1]) (by simp [hst, twPassSt, ht2]) (by simp [hst, twPassSt, ht3])
    have h3 := twRuns_countIter (body := body) htg (c := .ad) (tmp := .t1) (by decide) (tg .cy)
      (W := es.sum) (j := n₀ + j)
      (Function.update (Function.update (Function.update (Function.update (st j) .f
        (binSyms (ℓ + 1) (twEx fwd es ℓ h (n₀ + j)))) .src
        (twStream A w (List.range' (n₀ + (j + 1)) (M - (j + 1))) Z)) .acc
        ((cstream A w (List.ofFn (twShiftZ (twEx fwd es ℓ h (n₀ + j)) (Z (n₀ + j))))).reverse ++
          Function.update (st j) .f (binSyms (ℓ + 1) (twEx fwd es ℓ h (n₀ + j))) .acc)) .f [])
      (by simp [hst, twPassSt]) (by simp [hst, twPassSt, ht1])
    have h23 := twRuns_seq h2 h3
    refine twRuns_mono (twRuns_congr (twRuns_seq h1 h23) ?_) (by omega)
    have hacc' : (twStream A w (List.range' n₀ (j + 1)) Z').reverse =
        (cstream A w (List.ofFn (twShiftZ (twEx fwd es ℓ h (n₀ + j)) (Z (n₀ + j))))).reverse ++
          (twStream A w (List.range' n₀ j) Z').reverse := by
      rw [List.range'_concat]
      simp [twStream, hZ']
    funext r
    cases r <;> simp [Function.update_apply, hst, twPassSt, hacc', hf, Nat.add_assoc]
  have hne : ∀ j < M, st j .src ≠ [] := by
    intro j hj hnil
    have hl := congrArg List.length hnil
    simp only [hst, twPassSt, Function.update_apply, reduceCtorEq, ↓reduceIte,
      Function.update_self] at hl
    rw [twStream_length, List.length_range'] at hl
    have : 0 < (M - j) * (2 ^ ℓ * w) :=
      Nat.mul_pos (by omega) (Nat.mul_pos (by positivity) hw)
    simp at hl
    omega
  have hend : st M .src = [] := by simp [hst, twPassSt, twStream]
  have hwh := twRuns_while (body := body) (tg := tg) .src (twStepP tg fwd) st M _ hstep hne hend
  have hmv := twRuns_moveR (body := body) htg (a := .acc) (b := .dst) (by decide) (st M)
  have hacc_len : (st M .acc).length = M * (2 ^ ℓ * w) := by
    simp [hst, twPassSt, twStream_length, hacc]
  rw [hacc_len] at hmv
  have h0 : st 0 = ρ := by
    funext r
    cases r <;> simp [hst, twPassSt, Function.update_apply, hsrc, hacc, had, twStream]
  rw [h0] at hwh
  refine twRuns_mono (twRuns_congr (twRuns_seq hwh hmv) ?_) ?_
  · funext r
    cases r <;> simp [Function.update_apply, hst, twPassSt, hacc, hZ']
  · unfold twPassCost
    apply le_of_eq
    ring

end Runs

/-! ### Grid records -/

/-- `Z` holds the numerators of the grid values `u` at scale `2^p`. -/
def TwEnc {r : ℕ} (p : ℕ) (Z : ℕ → Fin r → GaussianInt) (u : Recs r) : Prop :=
  ∀ n c, u n c = GaussianInt.toComplex (Z n c) / 2 ^ p

/-- The output numerators of the pass encode `mulYInv (twE …) u` (`fwd`) or `mulY (twE …) u`. -/
theorem twEnc_twShiftZ (fwd : Bool) {ℓ p : ℕ} (es : List ℕ) (h : ℕ)
    {Z : ℕ → Fin (2 ^ ℓ) → GaussianInt} {u : Recs (2 ^ ℓ)} (hZ : TwEnc p Z u) :
    TwEnc p (fun n => twShiftZ (twEx fwd es ℓ h n) (Z n))
      (if fwd then mulYInv (twE es (2 ^ ℓ) h (parts es h)) u
        else mulY (twE es (2 ^ ℓ) h (parts es h)) u) := by
  intro n c
  have hu : u n = fun c => GaussianInt.toComplex (Z n c) / 2 ^ p := funext (hZ n)
  rw [twShiftZ_toComplex, ← hu]
  cases fwd with
  | true => rfl
  | false =>
      show shiftNegZ _ (u n) c = shiftNegZ _ (u n) c
      rw [twEx_false, ← shiftNegZ_mod]

/-- The forward twiddle on the flattened array of `u` is the flattened `mulYInv`. -/
theorem twFwdFlat_flat {r : ℕ} [NeZero r] (es : List ℕ) (h : ℕ) (u : Recs r) :
    twFwdFlat es h (flat es.sum u) = flat es.sum (mulYInv (twE es r h (parts es h)) u) := rfl

/-- The opposite twiddle on the flattened array of `u` is the flattened `mulY`. -/
theorem twOppFlat_flat {r : ℕ} [NeZero r] (es : List ℕ) (h : ℕ) (u : Recs r) :
    twOppFlat es h (flat es.sum u) = flat es.sum (mulY (twE es r h (parts es h)) u) := rfl

section Recs

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {tg : TwReg → Fin T}
  (htg : Function.Injective tg)
include htg

/-- **The twiddle pass on grid records.** The stream of the numerators `Z` of `u : Recs r`
(`r = 2^ℓ`) at the addresses `n₀, …, n₀ + M - 1` becomes the stream of numerators `Z'` of
`mulYInv (twE es r h (parts es h)) u` (`fwd`, the twiddle of `fwdRound` and of `twFwdFlat`) or
`mulY (twE es r h (parts es h)) u` (the twiddle of `oppRound` and of `twOppFlat`). -/
theorem twPass_recs (fwd : Bool) (hA : 5 ≤ A) {es : List ℕ} {ℓ h w p n₀ M : ℕ} (hw : 1 ≤ w)
    (hh : h ≤ ℓ) (Z : ℕ → Fin (2 ^ ℓ) → GaussianInt) (u : Recs (2 ^ ℓ)) (hZ : TwEnc p Z u)
    (ρ : TwReg → List (Fin (A + 4)))
    (hsrc : ρ .src = twStream A w (List.range' n₀ M) Z) (had : ρ .ad = binSyms es.sum n₀)
    (hrl : ρ .rl = twRoles A es h) (hwn : (ρ .wn).length = w)
    (hrwn : (ρ .rwn).length = 2 ^ ℓ * w) (hhn : (ρ .hn).length = h + 1)
    (hlh : (ρ .lh).length = ℓ - h) (hacc : ρ .acc = []) (hx : ρ .x = []) (htl : ρ .tl = [])
    (hhd : ρ .hd = []) (hc : ρ .c = []) (hv : ρ .v = []) (hvp : ρ .vp = []) (hf : ρ .f = [])
    (hg : ρ .g = []) (hz : ρ .z = []) (hsg : ρ .sg = []) (has : ρ .as = []) (ht1 : ρ .t1 = [])
    (ht2 : ρ .t2 = []) (ht3 : ρ .t3 = []) (ht4 : ρ .t4 = []) (ht5 : ρ .t5 = []) :
    ∃ Z' : ℕ → Fin (2 ^ ℓ) → GaussianInt,
      TwEnc p Z' (if fwd then mulYInv (twE es (2 ^ ℓ) h (parts es h)) u
        else mulY (twE es (2 ^ ℓ) h (parts es h)) u) ∧
      TwRuns body tg (twPassP tg fwd) ρ
        (Function.update (Function.update (Function.update ρ .src []) .ad
          (binSyms es.sum (n₀ + M))) .dst (twStream A w (List.range' n₀ M) Z' ++ ρ .dst))
        (twPassCost es.sum h ℓ w M) :=
  ⟨_, twEnc_twShiftZ fwd es h hZ, twPass_runs htg fwd hA hw hh Z ρ hsrc had hrl hwn hrwn hhn
    hlh hacc hx htl hhd hc hv hvp hf hg hz hsg has ht1 ht2 ht3 ht4 ht5⟩

end Recs

/-! ### Cost -/

lemma tw_sq_le_pow (ℓ : ℕ) : (ℓ + 3) ^ 2 ≤ 9 * 2 ^ ℓ := by
  induction ℓ with
  | zero => norm_num
  | succ ℓ ih =>
      have e1 : (ℓ + 1 + 3) ^ 2 = (ℓ + 3) ^ 2 + (2 * ℓ + 7) := by ring
      have e2 : 2 * ℓ + 7 ≤ (ℓ + 3) ^ 2 := by nlinarith
      calc (ℓ + 1 + 3) ^ 2 ≤ 2 * (ℓ + 3) ^ 2 := by rw [e1]; omega
        _ ≤ 2 * (9 * 2 ^ ℓ) := by omega
        _ = 9 * 2 ^ (ℓ + 1) := by ring

/-- The pass costs `O(r w + (N + 1)(ℓ + 1))` per record. -/
theorem twPassCost_le {N h ℓ w M : ℕ} (hh : h ≤ ℓ) :
    twPassCost N h ℓ w M ≤ M * (35 * 2 ^ ℓ * w + 50 * (N + 1) * (ℓ + 3)) + 4 := by
  unfold twPassCost twExpCost twRecCost
  have h1 : N * h ≤ N * ℓ := Nat.mul_le_mul_left _ hh
  have hper : N * (12 * h + 33) + 24 * h + 4 * ℓ + 70 + (33 * 2 ^ ℓ * w + 20 * ℓ + 40) +
      4 * N + 5 + 2 + 2 * (2 ^ ℓ * w) ≤ 35 * 2 ^ ℓ * w + 50 * (N + 1) * (ℓ + 3) := by
    have e1 : N * (12 * h + 33) = 12 * (N * h) + 33 * N := by ring
    have e2 : 50 * (N + 1) * (ℓ + 3) = 50 * (N * ℓ) + 150 * N + 50 * ℓ + 150 := by ring
    have e3 : 33 * 2 ^ ℓ * w = 33 * (2 ^ ℓ * w) := by ring
    have e4 : 35 * 2 ^ ℓ * w = 35 * (2 ^ ℓ * w) := by ring
    rw [e1, e2, e3, e4]
    omega
  calc M * (N * (12 * h + 33) + 24 * h + 4 * ℓ + 70 + (33 * 2 ^ ℓ * w + 20 * ℓ + 40) + 4 * N + 5 +
        2) + 2 + (2 * (M * (2 ^ ℓ * w)) + 2)
      = M * (N * (12 * h + 33) + 24 * h + 4 * ℓ + 70 + (33 * 2 ^ ℓ * w + 20 * ℓ + 40) + 4 * N +
        5 + 2 + 2 * (2 ^ ℓ * w)) + 4 := by ring
    _ ≤ M * (35 * 2 ^ ℓ * w + 50 * (N + 1) * (ℓ + 3)) + 4 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left M hper) 4

/-- The pass costs `M (c₁ r w + c₂ (N + 1)^2) + 4` with `c₁ = 485`, `c₂ = 50`. -/
theorem twPassCost_le_sq {N h ℓ w M : ℕ} (hh : h ≤ ℓ) (hw : 1 ≤ w) :
    twPassCost N h ℓ w M ≤ M * (485 * 2 ^ ℓ * w + 50 * (N + 1) ^ 2) + 4 := by
  refine le_trans (twPassCost_le hh) ?_
  have h1 : 50 * (N + 1) * (ℓ + 3) ≤ 25 * (N + 1) ^ 2 + 25 * (ℓ + 3) ^ 2 := by
    nlinarith [sq_nonneg ((N + 1 : ℤ) - (ℓ + 3))]
  have h2 := tw_sq_le_pow ℓ
  have h3 : 2 ^ ℓ ≤ 2 ^ ℓ * w := Nat.le_mul_of_pos_right _ hw
  have h4 : 35 * 2 ^ ℓ * w + 50 * (N + 1) * (ℓ + 3) ≤ 485 * 2 ^ ℓ * w + 50 * (N + 1) ^ 2 := by
    nlinarith
  exact Nat.add_le_add_right (Nat.mul_le_mul_left M h4) 4

end IntegerMultBounds.MathlibTM2.Fast
