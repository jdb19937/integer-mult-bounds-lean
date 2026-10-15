module

public import IntegerMultBounds.MathlibTM2.Fast.CMulPass

/-!
# The complex fixed-point product with truncation

A grid coefficient `u = N / 2^p` (`N : GaussianInt`, `|re N|, |im N| < 2^(w-1)`, `Fits w N`) is
stored as `coeffSyms A w (red w N)`: `w` pair symbols, least significant first, two's complement.
`cmulOne` multiplies two stored coefficients with truncation: from `N₁`, `N₂` it produces
`red w (tdivN p (N₁ N₂))`, the numerator of `rhoC p (u₁ u₂)` (`rhoC_mul_grid`). The result is
exact modulo `2^w`; no bound on the product is needed.

**Algorithm** (one coefficient pair).
1. `cmulPre`: split each operand (`splitP`) into the residues of `re`, `-re`, `im`, `-im`, and
   select (`selectP`) the magnitudes `|a|, |b|, |c|, |d|` (`binSyms w`) and their signs, where
   `N₁ = a + b i`, `N₂ = c + d i`.
2. `cmulProds`: four Schönhage–Strassen products `|a||c|, |b||d|, |a||d|, |b||c|` (`ssMul` at
   `m = w`), each `binSyms (topN w + 1)`. (`rmulProds`, for `d = 0`: two products and two zero
   numerals.)
3. `cmulPost`: the signed combinations `re = ac - bd`, `im = ad + bc` modulo `2^N`, `N = topN w`,
   together with their negations (`combP`); since `|re|, |im| < 2^(N-1)`, a selection gives sign
   and magnitude; dropping `p` bits (`usub`) gives `|re| / 2^p`; the final pass (`finP`) applies
   the sign modulo `2^w` (`re.tdiv 2^p = bsgn (re < 0) · (|re| / 2^p)`, `tdiv_eq_bsgn`) and
   writes pair symbols onto `acc`, most significant pair on top. Scratch registers are cleared.

**Register interface** (`CR`, `cr` injective; `ι` the 64 multiplier registers, disjoint from `cr`,
empty on both stacks; `Ready ρ w p`): `wn`, `pn`, `nn` hold `w`, `p`, `topN w` symbols (restored);
`tmp` and all scratch registers are empty (and end empty). `cmulOne` consumes one coefficient from
the top of `xs` and of `ys`, pushes their symbols (reversed) onto `xsv`, `ysv`, and pushes the
result coefficient (reversed) onto `acc`. Hypotheses: `96 ≤ A`, `1 ≤ w`, `p ≤ w`, `Fits w N₁`,
`Fits w N₂`, `64 ≤ T`, `SS.states ≤ Q`.

**Cost** (`cmulOne_runs`): at most `4 S + 128 w + 128` steps, `S = ssMulConst (T + 1) mLogLog w` the
bound of one `ssMul` (`ssMul_exec_log`). `rmulOne_runs`: `2 S + 160 w + 128`.

**Streams** (`CMulStream`). `cmulBlock` repeats `cmulOne` while `ys` is nonempty and then moves `ysv` back onto
`ys`: it multiplies the first `L = |ys|` coefficients of `xs` by the coefficients of `ys`, which
it restores. `cmulStream` (`xs`, `ys` of equal length `n`) and `cmulTable` (`xs` of `B L`
coefficients, the table `ys` of `L` coefficients reused for every block of `L` consecutive
coefficients of `xs`) end by moving the results from `acc` onto `out` (first coefficient on top)
and restoring `xs` from `xsv`; both operand registers end as they started. `cmulPair_runs` is
the case of one coefficient pair: `out` gains `coeffSyms A w (red w (tdivN p (N₁ N₂)))` on top.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Schoenhage.Schedule (topN topN_facts)

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

noncomputable section

/-! ### Register files -/

/-- Both parts of `N` lie strictly between `-2^(w-1)` and `2^(w-1)`. -/
def Fits (w : ℕ) (N : GaussianInt) : Prop := |N.re| < 2 ^ (w - 1) ∧ |N.im| < 2 ^ (w - 1)

/-- The unary registers hold `w`, `p`, `topN w`; the spare and all scratch registers are
empty. -/
structure Ready {A : ℕ} (ρ : CR → List (Fin (A + 4))) (w p : ℕ) : Prop where
  wn : (ρ .wn).length = w
  pn : (ρ .pn).length = p
  nn : (ρ .nn).length = topN w
  tmp : ρ .tmp = []
  u0 : ρ .u0 = []
  u1 : ρ .u1 = []
  u2 : ρ .u2 = []
  u3 : ρ .u3 = []
  ma : ρ .ma = []
  mb : ρ .mb = []
  mc : ρ .mc = []
  md : ρ .md = []
  sa : ρ .sa = []
  sb : ρ .sb = []
  sc : ρ .sc = []
  sd : ρ .sd = []
  p1 : ρ .p1 = []
  p2 : ρ .p2 = []
  p3 : ρ .p3 = []
  p4 : ρ .p4 = []
  qr : ρ .qr = []
  qi : ρ .qi = []
  sr : ρ .sr = []
  si : ρ .si = []

/-- `Ready` is kept by updates of the operand, save, result and output registers. -/
lemma Ready.update {A : ℕ} {ρ : CR → List (Fin (A + 4))} {w p : ℕ} (hr : Ready ρ w p) (r : CR)
    (hr' : r = .xs ∨ r = .ys ∨ r = .xsv ∨ r = .ysv ∨ r = .acc ∨ r = .out)
    (l : List (Fin (A + 4))) : Ready (Function.update ρ r l) w p := by
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl <;>
  exact ⟨by simp [hr.wn], by simp [hr.pn], by simp [hr.nn], by simp [hr.tmp], by simp [hr.u0],
    by simp [hr.u1], by simp [hr.u2], by simp [hr.u3], by simp [hr.ma], by simp [hr.mb],
    by simp [hr.mc], by simp [hr.md], by simp [hr.sa], by simp [hr.sb], by simp [hr.sc],
    by simp [hr.sd], by simp [hr.p1], by simp [hr.p2], by simp [hr.p3], by simp [hr.p4],
    by simp [hr.qr], by simp [hr.qi], by simp [hr.sr], by simp [hr.si]⟩

/-- Operands consumed: the rests `rx`, `ry` on `xs`, `ys`, the coefficients' symbols on the save
registers. -/
def opSt {A : ℕ} (ρ : CR → List (Fin (A + 4))) (w : ℕ) (N₁ N₂ : GaussianInt)
    (rx ry : List (Fin (A + 4))) : CR → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update ρ .xs rx) .ys ry)
    .xsv ((csyms A w N₁).reverse ++ ρ .xsv)) .ysv ((csyms A w N₂).reverse ++ ρ .ysv)

lemma Ready.opSt {A : ℕ} {ρ : CR → List (Fin (A + 4))} {w p : ℕ} (hr : Ready ρ w p)
    (N₁ N₂ : GaussianInt) (rx ry : List (Fin (A + 4))) : Ready (opSt ρ w N₁ N₂ rx ry) w p :=
  (((hr.update .xs (by simp) _).update .ys (by simp) _).update .xsv (by simp) _).update .ysv
    (by simp) _

/-- Magnitudes and signs of the operand parts. -/
def magSt {A : ℕ} (ρ : CR → List (Fin (A + 4))) (w : ℕ) (N₁ N₂ : GaussianInt) :
    CR → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update ρ
      .ma (binSyms w N₁.re.natAbs)) .mb (binSyms w N₁.im.natAbs))
      .mc (binSyms w N₂.re.natAbs)) .md (binSyms w N₂.im.natAbs))
      .sa [bitSymbol (decide (N₁.re < 0))]) .sb [bitSymbol (decide (N₁.im < 0))])
      .sc [bitSymbol (decide (N₂.re < 0))]) .sd [bitSymbol (decide (N₂.im < 0))]

/-- The four product registers. -/
def prodSt {A : ℕ} (ρ : CR → List (Fin (A + 4))) (X₁ X₂ X₃ X₄ : List (Fin (A + 4))) :
    CR → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update ρ .p1 X₁) .p2 X₂) .p3 X₃)
    .p4 X₄

section Body

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U} {cr : CR → Fin T}
  {ι : Fin 64 → Fin T}

/-! ### Splitting the operands -/

/-- Split both operands into magnitudes (`ma … md`) and signs (`sa … sd`). -/
def cmulPre (cr : CR → Fin T) : Pr P T Q A U :=
  .seq (splitP cr .xs .xsv .u0 .u1 .u2 .u3 .wn .tmp)
  (.seq (selectP (cr .u0) (cr .u1) (cr .ma) (cr .sa))
  (.seq (selectP (cr .u2) (cr .u3) (cr .mb) (cr .sb))
  (.seq (splitP cr .ys .ysv .u0 .u1 .u2 .u3 .wn .tmp)
  (.seq (selectP (cr .u0) (cr .u1) (cr .mc) (cr .sc))
    (selectP (cr .u2) (cr .u3) (cr .md) (cr .sd))))))

theorem pre_runs (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j) (hA : 96 ≤ A)
    {ρ : CR → List (Fin (A + 4))} {w p : ℕ} (hr : Ready ρ w p) (hw : 1 ≤ w)
    {N₁ N₂ : GaussianInt} (h₁ : Fits w N₁) (h₂ : Fits w N₂) {rx ry : List (Fin (A + 4))}
    (hx : ρ .xs = csyms A w N₁ ++ rx) (hy : ρ .ys = csyms A w N₂ ++ ry) :
    CRuns body cr ι (cmulPre cr) ρ (magSt (opSt ρ w N₁ N₂ rx ry) w N₁ N₂) (26 * w + 32) := by
  have H := CRuns.seq hdisj (split_runs (body := body) hcr hA (I := .xs) (Sv := .xsv) (O₀ := .u0)
      (O₁ := .u1) (O₂ := .u2) (O₃ := .u3) (C := .wn) (Tm := .tmp) (by decide) N₁ rx hx hr.wn
      hr.tmp)
    (CRuns.seq hdisj (select_runs hcr (X := .u0) (Y := .u1) (M := .ma) (Sg := .sa) (by decide) hw
      (x := N₁.re) h₁.1 (by simp [rbits, hr.u0]) (by simp [rbits, hr.u1]))
    (CRuns.seq hdisj (select_runs hcr (X := .u2) (Y := .u3) (M := .mb) (Sg := .sb) (by decide) hw
      (x := N₁.im) h₁.2 (by simp [rbits, hr.u2]) (by simp [rbits, hr.u3]))
    (CRuns.seq hdisj (split_runs hcr hA (I := .ys) (Sv := .ysv) (O₀ := .u0) (O₁ := .u1)
      (O₂ := .u2) (O₃ := .u3) (C := .wn) (Tm := .tmp) (w := w) (by decide) N₂ ry (by simp [hy])
      (by simp [hr.wn]) (by simp [hr.tmp]))
    (CRuns.seq hdisj (select_runs hcr (X := .u0) (Y := .u1) (M := .mc) (Sg := .sc) (by decide) hw
      (x := N₂.re) h₂.1 (by simp [rbits, hr.u0]) (by simp [rbits, hr.u1]))
      (select_runs hcr (X := .u2) (Y := .u3) (M := .md) (Sg := .sd) (by decide) hw
      (x := N₂.im) h₂.2 (by simp [rbits, hr.u2]) (by simp [rbits, hr.u3]))))))
  refine (H.congr ?_).mono (by omega)
  funext r
  cases r <;> simp [magSt, opSt, Function.update_apply, hr.u0, hr.u1, hr.u2, hr.u3, hr.ma, hr.mb,
    hr.mc, hr.md, hr.sa, hr.sb, hr.sc, hr.sd]

/-! ### Products -/

lemma natAbs_lt_of_fits {w : ℕ} {x : ℤ} (h : |x| < 2 ^ (w - 1)) : x.natAbs < 2 ^ w := by
  have h2 : (2 : ℤ) ^ (w - 1) ≤ 2 ^ w := pow_le_pow_right₀ (by norm_num) (by omega)
  have : (x.natAbs : ℤ) < ((2 ^ w : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]; push_cast; linarith
  exact_mod_cast this

/-- A product numeral of `N + 1` bits as `N` bits and the top bit. -/
lemma binSyms_succ_split {A : ℕ} (N x : ℕ) :
    (binSyms (N + 1) x : List (Fin (A + 4))) ++ [] = binSyms N x ++ binSyms 1 (x / 2 ^ N) := by
  rw [List.append_nil, binSyms_add]

variable (ι) in
/-- The four Schönhage–Strassen products `|a||c|`, `|b||d|`, `|a||d|`, `|b||c|`. -/
def cmulProds (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (cr : CR → Fin T) :
    Pr P T Q A U :=
  .seq (ssMul ι hι hT hQ (cr .ma) (cr .mc) (cr .nn) (cr .p1))
  (.seq (ssMul ι hι hT hQ (cr .mb) (cr .md) (cr .nn) (cr .p2))
  (.seq (ssMul ι hι hT hQ (cr .ma) (cr .md) (cr .nn) (cr .p3))
    (ssMul ι hι hT hQ (cr .mb) (cr .mc) (cr .nn) (cr .p4))))

/-- The product numerals: `N` low bits and the top bit. -/
abbrev pnum (A N P : ℕ) : List (Fin (A + 4)) := binSyms N P ++ binSyms 1 (P / 2 ^ N)

theorem prods_runs (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    {ρ : CR → List (Fin (A + 4))} {w p : ℕ} (hr : Ready ρ w p) (hw : 1 ≤ w)
    {N₁ N₂ : GaussianInt} (h₁ : Fits w N₁) (h₂ : Fits w N₂) :
    CRuns body cr ι (cmulProds ι hι hT hQ cr) (magSt ρ w N₁ N₂)
      (prodSt (magSt ρ w N₁ N₂) (pnum A (topN w) (N₁.re.natAbs * N₂.re.natAbs))
        (pnum A (topN w) (N₁.im.natAbs * N₂.im.natAbs))
        (pnum A (topN w) (N₁.re.natAbs * N₂.im.natAbs))
        (pnum A (topN w) (N₁.im.natAbs * N₂.re.natAbs)))
      (4 * (ssMulConst * (T + 1) * mLogLog w)) := by
  have H := CRuns.seq hdisj (ssMul_runs (body := body) hcr hdisj hι hT hQ (xa := .ma) (xb := .mc)
      (xn := .nn) (xc := .p1) (ρ := magSt ρ w N₁ N₂) (by decide) (by decide) hw (natAbs_lt_of_fits h₁.1)
      (natAbs_lt_of_fits h₂.1) (by simp [magSt]) (by simp [magSt]) (by simp [magSt, hr.nn]))
    (CRuns.seq hdisj (ssMul_runs hcr hdisj hι hT hQ (xa := .mb) (xb := .md)
      (xn := .nn) (xc := .p2) (by decide) (by decide) hw (natAbs_lt_of_fits h₁.2)
      (natAbs_lt_of_fits h₂.2) (by simp [magSt]) (by simp [magSt]) (by simp [magSt, hr.nn]))
    (CRuns.seq hdisj (ssMul_runs hcr hdisj hι hT hQ (xa := .ma) (xb := .md)
      (xn := .nn) (xc := .p3) (by decide) (by decide) hw (natAbs_lt_of_fits h₁.1)
      (natAbs_lt_of_fits h₂.2) (by simp [magSt]) (by simp [magSt]) (by simp [magSt, hr.nn]))
      (ssMul_runs hcr hdisj hι hT hQ (xa := .mb) (xb := .mc)
      (xn := .nn) (xc := .p4) (by decide) (by decide) hw (natAbs_lt_of_fits h₁.2)
      (natAbs_lt_of_fits h₂.1) (by simp [magSt]) (by simp [magSt]) (by simp [magSt, hr.nn]))))
  refine (H.congr ?_).mono (by omega)
  funext r
  cases r <;> simp [prodSt, magSt, Function.update_apply, hr.p1, hr.p2, hr.p3, hr.p4,
    binSyms_add]

variable (ι) in
/-- The two products `|a||c|`, `|b||c|` of a real second factor, and two zero numerals. -/
def rmulProds (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (cr : CR → Fin T) :
    Pr P T Q A U :=
  .seq (ssMul ι hι hT hQ (cr .ma) (cr .mc) (cr .nn) (cr .p1))
  (.seq (zeroBits (cr .nn) (cr .p2) (cr .tmp))
  (.seq (zeroBits (cr .nn) (cr .p3) (cr .tmp))
    (ssMul ι hι hT hQ (cr .mb) (cr .mc) (cr .nn) (cr .p4))))

theorem rprods_runs (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    {ρ : CR → List (Fin (A + 4))} {w p : ℕ} (hr : Ready ρ w p) (hw : 1 ≤ w)
    {N₁ N₂ : GaussianInt} (h₁ : Fits w N₁) (h₂ : Fits w N₂) :
    CRuns body cr ι (rmulProds ι hι hT hQ cr) (magSt ρ w N₁ N₂)
      (prodSt (magSt ρ w N₁ N₂) (pnum A (topN w) (N₁.re.natAbs * N₂.re.natAbs))
        (binSyms (topN w) 0 ++ []) (binSyms (topN w) 0 ++ [])
        (pnum A (topN w) (N₁.im.natAbs * N₂.re.natAbs)))
      (2 * (ssMulConst * (T + 1) * mLogLog w) + 2 * (4 * topN w + 4)) := by
  have H := CRuns.seq hdisj (ssMul_runs (body := body) hcr hdisj hι hT hQ (xa := .ma) (xb := .mc)
      (xn := .nn) (xc := .p1) (ρ := magSt ρ w N₁ N₂) (by decide) (by decide) hw (natAbs_lt_of_fits h₁.1)
      (natAbs_lt_of_fits h₂.1) (by simp [magSt]) (by simp [magSt]) (by simp [magSt, hr.nn]))
    (CRuns.seq hdisj (zeroBits_runs hcr (len := .nn) (z := .p2) (t := .tmp) (by decide)
      (by decide) (by decide) (n := topN w) (by simp [magSt, hr.nn]) (by simp [magSt, hr.tmp]))
    (CRuns.seq hdisj (zeroBits_runs hcr (len := .nn) (z := .p3) (t := .tmp) (by decide)
      (by decide) (by decide) (n := topN w) (by simp [magSt, hr.nn]) (by simp [magSt, hr.tmp]))
      (ssMul_runs hcr hdisj hι hT hQ (xa := .mb) (xb := .mc)
      (xn := .nn) (xc := .p4) (by decide) (by decide) hw (natAbs_lt_of_fits h₁.2)
      (natAbs_lt_of_fits h₂.1) (by simp [magSt]) (by simp [magSt]) (by simp [magSt, hr.nn]))))
  refine (H.congr ?_).mono (by omega)
  funext r
  cases r <;> simp [prodSt, magSt, Function.update_apply, hr.p1, hr.p2, hr.p3, hr.p4,
    binSyms_add]

/-! ### Combination, truncation and output -/

/-- Mode bits of the real part: `re = bsgn (sa ⊕ sc) |a||c| + bsgn ¬(sb ⊕ sd) |b||d|`. -/
def fRe (a b c d : Bool) : Bool × Bool := (a ^^ c, !(b ^^ d))

/-- Mode bits of the imaginary part: `im = bsgn (sa ⊕ sd) |a||d| + bsgn (sb ⊕ sc) |b||c|`. -/
def fIm (a b c d : Bool) : Bool × Bool := (a ^^ d, b ^^ c)

/-- The real part from the signs of the operand parts and the products `P₁`, `P₂`. -/
def reOf (N₁ N₂ : GaussianInt) (P₁ P₂ : ℕ) : ℤ :=
  bsgn (decide (N₁.re < 0) ^^ decide (N₂.re < 0)) * P₁ +
    bsgn (!(decide (N₁.im < 0) ^^ decide (N₂.im < 0))) * P₂

/-- The imaginary part from the signs of the operand parts and the products `P₃`, `P₄`. -/
def imOf (N₁ N₂ : GaussianInt) (P₃ P₄ : ℕ) : ℤ :=
  bsgn (decide (N₁.re < 0) ^^ decide (N₂.im < 0)) * P₃ +
    bsgn (decide (N₁.im < 0) ^^ decide (N₂.re < 0)) * P₄

/-- The truncated quotient in sign-magnitude form (`tq_eq`: it is `x.tdiv 2^p`). -/
def tq (p : ℕ) (x : ℤ) : ℤ := bsgn (decide (x < 0)) * ((x.natAbs / 2 ^ p : ℕ) : ℤ)

lemma tq_eq (p : ℕ) (x : ℤ) : tq p x = x.tdiv (2 ^ p) := (tdiv_eq_bsgn x p).symm

/-- The low bits after dropping `p` bits, split at `w`. -/
lemma drop_split {A N p w : ℕ} (h : p + w ≤ N) (x : ℕ) :
    (binSyms N x : List (Fin (A + 4))).drop p =
      binSyms w (x / 2 ^ p) ++ binSyms (N - p - w) (x / 2 ^ p / 2 ^ w) := by
  rw [drop_binSyms (by omega)]
  conv_lhs => rw [show N - p = w + (N - p - w) by omega]
  rw [binSyms_add]

/-- Combine, select, truncate, write the result coefficient, and clear the scratch registers. -/
def cmulPost (cr : CR → Fin T) : Pr P T Q A U :=
  .seq (uclear (cr .ma))
  (.seq (uclear (cr .mb))
  (.seq (uclear (cr .mc))
  (.seq (uclear (cr .md))
  (.seq (combP cr fRe .sa .sb .sc .sd .p1 .p2 .u0 .u1 .nn .tmp)
  (.seq (combP cr fIm .sa .sb .sc .sd .p3 .p4 .u2 .u3 .nn .tmp)
  (.seq (uclear (cr .p1))
  (.seq (uclear (cr .p2))
  (.seq (uclear (cr .p3))
  (.seq (uclear (cr .p4))
  (.seq (uclear (cr .sa))
  (.seq (uclear (cr .sb))
  (.seq (uclear (cr .sc))
  (.seq (uclear (cr .sd))
  (.seq (selectP (cr .u0) (cr .u1) (cr .qr) (cr .sr))
  (.seq (selectP (cr .u2) (cr .u3) (cr .qi) (cr .si))
  (.seq (usub (cr .pn) (cr .qr) (cr .tmp))
  (.seq (usub (cr .pn) (cr .qi) (cr .tmp))
  (.seq (finP cr .sr .si .qr .qi .acc .wn .tmp)
  (.seq (uclear (cr .qr))
  (.seq (uclear (cr .qi))
  (.seq (uclear (cr .sr))
  (uclear (cr .si)))))))))))))))))))))))

theorem post_runs (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j) (hA : 96 ≤ A)
    {ρ : CR → List (Fin (A + 4))} {w p : ℕ} (hr : Ready ρ w p) (hw : 1 ≤ w) (hp : p ≤ w)
    (N₁ N₂ : GaussianInt) {P₁ P₂ P₃ P₄ : ℕ} {e₁ e₂ e₃ e₄ : List (Fin (A + 4))}
    (hl₁ : e₁.length ≤ 1) (hl₂ : e₂.length ≤ 1) (hl₃ : e₃.length ≤ 1) (hl₄ : e₄.length ≤ 1)
    (hR : |reOf N₁ N₂ P₁ P₂| < 2 ^ (topN w - 1)) (hI : |imOf N₁ N₂ P₃ P₄| < 2 ^ (topN w - 1)) :
    CRuns body cr ι (cmulPost cr)
      (prodSt (magSt ρ w N₁ N₂) (binSyms (topN w) P₁ ++ e₁) (binSyms (topN w) P₂ ++ e₂)
        (binSyms (topN w) P₃ ++ e₃) (binSyms (topN w) P₄ ++ e₄))
      (Function.update ρ .acc ((coeffSyms A w (((tq p (reOf N₁ N₂ P₁ P₂) : ℤ) : ZMod (2 ^ w)),
        ((tq p (imOf N₁ N₂ P₃ P₄) : ℤ) : ZMod (2 ^ w)))).reverse ++ ρ .acc))
      (22 * topN w + 9 * w + 4 * p + 84) := by
  obtain ⟨hNlt, hNle, -⟩ := topN_facts hw
  have hN1 : 1 ≤ topN w := by omega
  have hpw : p + w ≤ topN w := by omega
  set R := reOf N₁ N₂ P₁ P₂ with hRdef
  set I := imOf N₁ N₂ P₃ P₄ with hIdef
  have H := CRuns.seq hdisj (uclear_runs (body := body) (ι := ι) hcr .ma
      (ρ := prodSt (magSt ρ w N₁ N₂) (binSyms (topN w) P₁ ++ e₁) (binSyms (topN w) P₂ ++ e₂)
        (binSyms (topN w) P₃ ++ e₃) (binSyms (topN w) P₄ ++ e₄)) (n := w) (by simp [prodSt, magSt]))
    (CRuns.seq hdisj (uclear_runs hcr .mb (n := w) (by simp [prodSt, magSt]))
    (CRuns.seq hdisj (uclear_runs hcr .mc (n := w) (by simp [prodSt, magSt]))
    (CRuns.seq hdisj (uclear_runs hcr .md (n := w) (by simp [prodSt, magSt]))
    (CRuns.seq hdisj (comb_runs hcr hA fRe .sa .sb .sc .sd (I₁ := .p1) (I₂ := .p2) (O₁ := .u0)
      (O₂ := .u1) (C := .nn) (Tm := .tmp) (by decide) (K := topN w) (X₁ := P₁) (X₂ := P₂) (e₁ := e₁)
      (e₂ := e₂) (by simp [prodSt, magSt]) (by simp [prodSt, magSt]) (by simp [prodSt, magSt, hr.nn])
      (by simp [prodSt, magSt, hr.tmp]) (m := fRe (decide (N₁.re < 0)) (decide (N₁.im < 0))
        (decide (N₂.re < 0)) (decide (N₂.im < 0))) (by simp [prodSt, magSt, topB]))
    (CRuns.seq hdisj (comb_runs hcr hA fIm .sa .sb .sc .sd (I₁ := .p3) (I₂ := .p4) (O₁ := .u2)
      (O₂ := .u3) (C := .nn) (Tm := .tmp) (by decide) (K := topN w) (X₁ := P₃) (X₂ := P₄) (e₁ := e₃)
      (e₂ := e₄) (by simp [prodSt, magSt]) (by simp [prodSt, magSt]) (by simp [prodSt, magSt, hr.nn])
      (by simp [prodSt, magSt, hr.tmp]) (m := fIm (decide (N₁.re < 0)) (decide (N₁.im < 0))
        (decide (N₂.re < 0)) (decide (N₂.im < 0))) (by simp [prodSt, magSt, topB]))
    (CRuns.seq hdisj (uclear_runs hcr .p1 (n := e₁.length) (by simp [prodSt, magSt]))
    (CRuns.seq hdisj (uclear_runs hcr .p2 (n := e₂.length) (by simp [prodSt, magSt]))
    (CRuns.seq hdisj (uclear_runs hcr .p3 (n := e₃.length) (by simp [prodSt, magSt]))
    (CRuns.seq hdisj (uclear_runs hcr .p4 (n := e₄.length) (by simp [prodSt, magSt]))
    (CRuns.seq hdisj (uclear_runs hcr .sa (n := 1) (by simp [prodSt, magSt]))
    (CRuns.seq hdisj (uclear_runs hcr .sb (n := 1) (by simp [prodSt, magSt]))
    (CRuns.seq hdisj (uclear_runs hcr .sc (n := 1) (by simp [prodSt, magSt]))
    (CRuns.seq hdisj (uclear_runs hcr .sd (n := 1) (by simp [prodSt, magSt]))
    (CRuns.seq hdisj (select_runs hcr (X := .u0) (Y := .u1) (M := .qr) (Sg := .sr) (by decide)
      hN1 (x := R) hR (by simp [prodSt, magSt, rbits, hRdef, reOf, fRe, hr.u0])
      (by simp [prodSt, magSt, rbits, hRdef, reOf, fRe, hr.u1]))
    (CRuns.seq hdisj (select_runs hcr (X := .u2) (Y := .u3) (M := .qi) (Sg := .si) (by decide)
      hN1 (x := I) hI (by simp [prodSt, magSt, rbits, hIdef, imOf, fIm, hr.u2])
      (by simp [prodSt, magSt, rbits, hIdef, imOf, fIm, hr.u3]))
    (CRuns.seq hdisj (usub_runs hcr (a := .pn) (b := .qr) (t := .tmp) (by decide) (by decide)
      (by decide) (n := p) (by simp [prodSt, magSt, hr.pn]) (by simp [prodSt, magSt, hr.tmp]))
    (CRuns.seq hdisj (usub_runs hcr (a := .pn) (b := .qi) (t := .tmp) (by decide) (by decide)
      (by decide) (n := p) (by simp [prodSt, magSt, hr.pn]) (by simp [prodSt, magSt, hr.tmp]))
    (CRuns.seq hdisj (fin_runs hcr hA .sr .si (I₁ := .qr) (I₂ := .qi) (O := .acc) (C := .wn)
      (Tm := .tmp) (by decide) (w := w) (X₁ := R.natAbs / 2 ^ p) (X₂ := I.natAbs / 2 ^ p)
      (e₁ := binSyms (topN w - p - w) (R.natAbs / 2 ^ p / 2 ^ w))
      (e₂ := binSyms (topN w - p - w) (I.natAbs / 2 ^ p / 2 ^ w))
      (by simp [prodSt, magSt, hr.qr, drop_split hpw]) (by simp [prodSt, magSt, hr.qi, drop_split hpw])
      (by simp [prodSt, magSt, hr.wn]) (by simp [prodSt, magSt, hr.tmp])
      (s₁ := decide (R < 0)) (s₂ := decide (I < 0)) (by simp [prodSt, magSt, topB, hr.sr])
      (by simp [prodSt, magSt, topB, hr.si]))
    (CRuns.seq hdisj (uclear_runs hcr .qr (n := topN w - p - w) (by simp [prodSt, magSt]))
    (CRuns.seq hdisj (uclear_runs hcr .qi (n := topN w - p - w) (by simp [prodSt, magSt]))
    (CRuns.seq hdisj (uclear_runs hcr .sr (n := 1) (by simp [prodSt, magSt, hr.sr]))
      (uclear_runs hcr .si (n := 1) (by simp [prodSt, magSt, hr.si])))))))))))))))))))))))
  refine (H.congr ?_).mono ?_
  swap
  · clear H hR hI hRdef hIdef R I hr
    generalize topN w = N at *
    obtain ⟨k, rfl⟩ : ∃ k, N = p + w + k := ⟨N - p - w, by omega⟩
    rw [show p + w + k - p - w = k by omega]
    linarith
  funext r
  cases r <;> simp [prodSt, magSt, tq, Function.update_apply, hr.u0, hr.u1, hr.u2, hr.u3,
    hr.ma, hr.mb, hr.mc, hr.md, hr.sa, hr.sb, hr.sc, hr.sd, hr.p1, hr.p2, hr.p3, hr.p4, hr.qr,
    hr.qi, hr.sr, hr.si]

/-! ### One coefficient pair -/

lemma reOf_eq (N₁ N₂ : GaussianInt) :
    reOf N₁ N₂ (N₁.re.natAbs * N₂.re.natAbs) (N₁.im.natAbs * N₂.im.natAbs) = (N₁ * N₂).re := by
  have key : ∀ (sa sb sc sd : Bool) (a b c d : ℤ), bsgn (sa ^^ sc) * (a * c) +
      bsgn (!(sb ^^ sd)) * (b * d) = (bsgn sa * a) * (bsgn sc * c) - (bsgn sb * b) * (bsgn sd * d) := by
    intros; rw [bsgn_xor, bsgn_not, bsgn_xor]; ring
  rw [reOf, Nat.cast_mul, Nat.cast_mul, key, bsgn_natAbs, bsgn_natAbs, bsgn_natAbs, bsgn_natAbs,
    Zsqrtd.re_mul]
  ring

lemma imOf_eq (N₁ N₂ : GaussianInt) :
    imOf N₁ N₂ (N₁.re.natAbs * N₂.im.natAbs) (N₁.im.natAbs * N₂.re.natAbs) = (N₁ * N₂).im := by
  have key : ∀ (sa sb sc sd : Bool) (a b c d : ℤ), bsgn (sa ^^ sd) * (a * d) +
      bsgn (sb ^^ sc) * (b * c) = (bsgn sa * a) * (bsgn sd * d) + (bsgn sb * b) * (bsgn sc * c) := by
    intros; rw [bsgn_xor, bsgn_xor]; ring
  rw [imOf, Nat.cast_mul, Nat.cast_mul, key, bsgn_natAbs, bsgn_natAbs, bsgn_natAbs, bsgn_natAbs,
    Zsqrtd.im_mul]

/-- The parts of the product fit the combination width. -/
lemma prod_bound {w : ℕ} (hw : 1 ≤ w) {N₁ N₂ : GaussianInt} (h₁ : Fits w N₁) (h₂ : Fits w N₂) :
    |(N₁ * N₂).re| < 2 ^ (topN w - 1) ∧ |(N₁ * N₂).im| < 2 ^ (topN w - 1) := by
  obtain ⟨hlt, -, -⟩ := topN_facts hw
  have hM : (2 : ℤ) * 2 ^ (w - 1) * 2 ^ (w - 1) ≤ 2 ^ (topN w - 1) := by
    have : (2 : ℤ) * 2 ^ (w - 1) * 2 ^ (w - 1) = 2 ^ (1 + (w - 1) + (w - 1)) := by
      rw [pow_add, pow_add]; ring
    rw [this]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have key : ∀ x y u v : ℤ, |x| < 2 ^ (w - 1) → |y| < 2 ^ (w - 1) → |u| < 2 ^ (w - 1) →
      |v| < 2 ^ (w - 1) → |x * y| + |u * v| < 2 * 2 ^ (w - 1) * 2 ^ (w - 1) := by
    intro x y u v hx hy hu hv
    rw [abs_mul, abs_mul]
    have := mul_lt_mul'' hx hy (abs_nonneg _) (abs_nonneg _)
    have := mul_lt_mul'' hu hv (abs_nonneg _) (abs_nonneg _)
    linarith
  rw [Zsqrtd.re_mul, Zsqrtd.im_mul]
  constructor
  · calc |N₁.re * N₂.re + -1 * N₁.im * N₂.im| ≤ |N₁.re * N₂.re| + |-1 * N₁.im * N₂.im| :=
          abs_add_le _ _
      _ = |N₁.re * N₂.re| + |N₁.im * N₂.im| := by rw [mul_assoc, neg_one_mul, abs_neg]
      _ < 2 * 2 ^ (w - 1) * 2 ^ (w - 1) := key _ _ _ _ h₁.1 h₂.1 h₁.2 h₂.2
      _ ≤ _ := hM
  · calc |N₁.re * N₂.im + N₁.im * N₂.re| ≤ |N₁.re * N₂.im| + |N₁.im * N₂.re| := abs_add_le _ _
      _ < 2 * 2 ^ (w - 1) * 2 ^ (w - 1) := key _ _ _ _ h₁.1 h₂.2 h₁.2 h₂.1
      _ ≤ _ := hM

/-- The register file after one product: operands consumed and saved, the result coefficient
`z` (reversed) on top of `acc`. -/
def oneSt {A : ℕ} (ρ : CR → List (Fin (A + 4))) (w : ℕ) (N₁ N₂ : GaussianInt)
    (rx ry : List (Fin (A + 4))) (z : GaussianInt) : CR → List (Fin (A + 4)) :=
  Function.update (opSt ρ w N₁ N₂ rx ry) .acc ((csyms A w z).reverse ++ ρ .acc)

variable (ι) in
/-- The complex fixed-point product of the coefficients on top of `xs` and `ys`. -/
def cmulOne (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (cr : CR → Fin T) :
    Pr P T Q A U :=
  .seq (cmulPre cr) (.seq (cmulProds ι hι hT hQ cr) (cmulPost cr))

variable (ι) in
/-- The product by a real coefficient (`im N₂ = 0`): two Schönhage–Strassen products. -/
def rmulOne (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (cr : CR → Fin T) :
    Pr P T Q A U :=
  .seq (cmulPre cr) (.seq (rmulProds ι hι hT hQ cr) (cmulPost cr))

/-- The step bound of `cmulOne`. -/
def cmulCost (T w : ℕ) : ℕ := 4 * (ssMulConst * (T + 1) * mLogLog w) + 128 * w + 128

/-- The step bound of `rmulOne`. -/
def rmulCost (T w : ℕ) : ℕ := 2 * (ssMulConst * (T + 1) * mLogLog w) + 160 * w + 128

/-- **The complex fixed-point product of one coefficient pair.** From a ready register file with
`coeffSyms A w (red w N₁)` on top of `xs` and `coeffSyms A w (red w N₂)` on top of `ys`, `cmulOne`
pops both coefficients, pushes their symbols (reversed) onto `xsv` and `ysv`, and pushes
`coeffSyms A w (red w (tdivN p (N₁ N₂)))` (reversed) onto `acc`, within `cmulCost T w` steps. -/
theorem cmulOne_runs (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {ρ : CR → List (Fin (A + 4))} {w p : ℕ} (hr : Ready ρ w p) (hw : 1 ≤ w) (hp : p ≤ w)
    {N₁ N₂ : GaussianInt} (h₁ : Fits w N₁) (h₂ : Fits w N₂) {rx ry : List (Fin (A + 4))}
    (hx : ρ .xs = csyms A w N₁ ++ rx) (hy : ρ .ys = csyms A w N₂ ++ ry) :
    CRuns body cr ι (cmulOne ι hι hT hQ cr) ρ (oneSt ρ w N₁ N₂ rx ry (tdivN p (N₁ * N₂)))
      (cmulCost T w) := by
  obtain ⟨-, hNle, -⟩ := topN_facts hw
  have hr' := hr.opSt N₁ N₂ rx ry
  have hb := prod_bound hw h₁ h₂
  have H := CRuns.seq hdisj (pre_runs (body := body) hcr hdisj hA hr hw h₁ h₂ hx hy)
    (CRuns.seq hdisj (prods_runs hcr hdisj hι hT hQ hr' hw h₁ h₂)
      (post_runs hcr hdisj hA hr' hw hp N₁ N₂ (by simp) (by simp) (by simp) (by simp)
        (by rw [reOf_eq]; exact hb.1) (by rw [imOf_eq]; exact hb.2)))
  refine (H.congr ?_).mono ?_
  · rw [tq_eq, tq_eq, reOf_eq, imOf_eq]
    simp [oneSt, opSt, csyms, red, tdivN]
  · unfold cmulCost
    generalize ssMulConst * (T + 1) * mLogLog w = S
    generalize topN w = N at *
    omega

/-- **The product by a real coefficient.** As `cmulOne_runs` when `im N₂ = 0`, with two
Schönhage–Strassen products, within `rmulCost T w` steps. -/
theorem rmulOne_runs (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {ρ : CR → List (Fin (A + 4))} {w p : ℕ} (hr : Ready ρ w p) (hw : 1 ≤ w) (hp : p ≤ w)
    {N₁ N₂ : GaussianInt} (h₁ : Fits w N₁) (h₂ : Fits w N₂) (hre : N₂.im = 0)
    {rx ry : List (Fin (A + 4))}
    (hx : ρ .xs = csyms A w N₁ ++ rx) (hy : ρ .ys = csyms A w N₂ ++ ry) :
    CRuns body cr ι (rmulOne ι hι hT hQ cr) ρ (oneSt ρ w N₁ N₂ rx ry (tdivN p (N₁ * N₂)))
      (rmulCost T w) := by
  obtain ⟨-, hNle, -⟩ := topN_facts hw
  have hr' := hr.opSt N₁ N₂ rx ry
  have hb := prod_bound hw h₁ h₂
  have hd : N₂.im.natAbs = 0 := by simp [hre]
  have e₁ : reOf N₁ N₂ (N₁.re.natAbs * N₂.re.natAbs) 0 = (N₁ * N₂).re := by
    have := reOf_eq N₁ N₂; simp only [hd, mul_zero] at this; exact this
  have e₂ : imOf N₁ N₂ 0 (N₁.im.natAbs * N₂.re.natAbs) = (N₁ * N₂).im := by
    have := imOf_eq N₁ N₂; simp only [hd, mul_zero] at this; exact this
  have H := CRuns.seq hdisj (pre_runs (body := body) hcr hdisj hA hr hw h₁ h₂ hx hy)
    (CRuns.seq hdisj (rprods_runs hcr hdisj hι hT hQ hr' hw h₁ h₂)
      (post_runs hcr hdisj hA hr' hw hp N₁ N₂ (by simp) (by simp) (by simp) (by simp)
        (by rw [e₁]; exact hb.1) (by rw [e₂]; exact hb.2)))
  refine (H.congr ?_).mono ?_
  · rw [tq_eq, tq_eq, e₁, e₂]
    simp [oneSt, opSt, csyms, red, tdivN]
  · unfold rmulCost
    generalize ssMulConst * (T + 1) * mLogLog w = S
    generalize topN w = N at *
    omega

end Body

end

end IntegerMultBounds.MathlibTM2.Fast
