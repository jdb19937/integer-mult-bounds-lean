module

public import IntegerMultBounds.MathlibTM2.Fast.ResampARegs
public import IntegerMultBounds.MathlibTM2.Fast.ResampASem

/-!
# The numeric `Ã` on one line

The line machine `rsaLineP` turns one padded line of the box into the `t` outputs of the
numeric `Ã` (`Fast/ResampASem`): from the numerators `N` of the `s` grid values of the line at
scale `2^q` and the integer table weights `wt k i` (`2^p` times the weights) it computes
`rsaOut q s t (2m + 1) (rsaExt m N) wt`, whose entry `k` is
`Σ_{i ≤ 2m} tdivN q (E_{⌊s k / t⌋ + i} · wt k i)` on the cyclic extension
`E = N.drop (s - m) ++ N ++ N.take m` (`rsaOut_resampANum`: the numerators at scale `2^(p+1)`
of `resampANum s t m (termW p (WA / 2^p))`). All sums are exact modulo `2^w`; every product is
exact (`rmulOne_runs`).

**Registers** (`RsaR X`, one record `RsaV X A` of contents, `V.get` the register file): the
complex-product registers `c x`, `x : CR` (`Fast/CMulRegs`); the box register `ln`; the output
register `ob`; the running sum `sm` with `pz`, `sm2`; the extension temporaries `ea`, `eb`, `er`;
the unary counters `cS`, `cM`, `cP`, `cW`, `cT` (holding `s w`, `m w`, `(t - s) w`, `2m + 1`,
`t` symbols, any symbols) with their spares `ka`, `kW`, `kT`, and the spares `kx`, `kb`, `atm`;
the binary residue `rr` and source length `bS` (`L` bits, `t = 2^L`) with the adder spares
`bxa`, `bya`, `bza`; and an extra family `x j`, `j : X`, untouched here. `RsaV.upd_*` and
`RsaV.extend_c` turn register updates into record updates.

**Algorithm.**
1. Move the `s w` symbols of the line from `ln` to `ea`; build `E` on `c .xs` by copies and two
   counted transfers of `m w` symbols; drop the `(t - s) w` padding symbols from `ln`.
2. For each output `k < t` (`rsaRowP`, counter `cT`): zero the sum; for each of the `2m + 1`
   terms (`rsaTermP`, counter `cW`) multiply the record on top of `xs` (the window) by the real
   table entry on top of `ys` (`rmulOne`, shift `q = |pn|`) and add it to `sm`
   (`rsaAddAuto`, the Gaussian automaton of `[[1, 1]]`); move the window back from `xsv` onto
   `xs` and the sum onto `ob`; `rr := (rr + s) mod 2^L` (`baddTo`), and when it carries drop one
   record from `xs`: the window start `⌊s k / t⌋` advances by that carry (`rsaCen_succ`).
3. Move the table back from `ysv` onto `ys` and clear `xs`.

**Contract** (`rsa_line`): from a register file with `ln = cstream (N ++ Z) ++ rest`
(`|N| = s`, `|Z| = t - s`), the table `cstream (rsaTabL t (2m + 1) wt)` on `ys`, the counters,
`rr = 0`, `bS = s`, a ready product register file and empty scratch registers, the machine ends
with `ln = rest` and `cstream (rsaOut …)` reversed on top of `ob`; every other register is
restored. Conditions: `m ≤ s < t = 2^L`, the records of `N` and of the table fit `w` bits, the
table is real, `q ≤ w`, `96 ≤ A`.

**Cost** (`rsaLineCost`): `t` outputs of `2m + 1` terms of `rmulCost T w + 9 w + 12` steps,
plus `O(w + L)` per output and `O((s + m + t) w)` per line (`rsaLineCost_le` in
`Fast/ResampAAxis`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.ResampA

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! ### Registers -/

/-- The registers of the resampling machines: the complex-product registers `c x`, the stage
registers, and an extra family `x j`. -/
inductive RsaR (X : Type) where
  | c (x : CR)
  | ln | ob | sm | pz | sm2 | ea | eb | er | cS | cM | cP | cW | cT | kW | kT | kx | ka | kb | atm | rr | bS | bxa | bya | bza
  | x (j : X)
  deriving DecidableEq

/-- A register file of the resampling machines, one field per register role. -/
@[ext]
structure RsaV (X : Type) (A : ℕ) where
  cr : CR → List (Fin (A + 4))
  ln : List (Fin (A + 4))
  ob : List (Fin (A + 4))
  sm : List (Fin (A + 4))
  pz : List (Fin (A + 4))
  sm2 : List (Fin (A + 4))
  ea : List (Fin (A + 4))
  eb : List (Fin (A + 4))
  er : List (Fin (A + 4))
  cS : List (Fin (A + 4))
  cM : List (Fin (A + 4))
  cP : List (Fin (A + 4))
  cW : List (Fin (A + 4))
  cT : List (Fin (A + 4))
  kW : List (Fin (A + 4))
  kT : List (Fin (A + 4))
  kx : List (Fin (A + 4))
  ka : List (Fin (A + 4))
  kb : List (Fin (A + 4))
  atm : List (Fin (A + 4))
  rr : List (Fin (A + 4))
  bS : List (Fin (A + 4))
  bxa : List (Fin (A + 4))
  bya : List (Fin (A + 4))
  bza : List (Fin (A + 4))
  xr : X → List (Fin (A + 4))

variable {X : Type} {A : ℕ}

/-- The register file as a function. -/
def RsaV.get (V : RsaV X A) : RsaR X → List (Fin (A + 4))
  | .c x => V.cr x
  | .ln => V.ln
  | .ob => V.ob
  | .sm => V.sm
  | .pz => V.pz
  | .sm2 => V.sm2
  | .ea => V.ea
  | .eb => V.eb
  | .er => V.er
  | .cS => V.cS
  | .cM => V.cM
  | .cP => V.cP
  | .cW => V.cW
  | .cT => V.cT
  | .kW => V.kW
  | .kT => V.kT
  | .kx => V.kx
  | .ka => V.ka
  | .kb => V.kb
  | .atm => V.atm
  | .rr => V.rr
  | .bS => V.bS
  | .bxa => V.bxa
  | .bya => V.bya
  | .bza => V.bza
  | .x j => V.xr j

@[simp] lemma RsaV.get_c (V : RsaV X A) (x : CR) : V.get (.c x) = V.cr x := rfl
@[simp] lemma RsaV.get_x (V : RsaV X A) (j : X) : V.get (.x j) = V.xr j := rfl
@[simp] lemma RsaV.get_ln (V : RsaV X A) : V.get .ln = V.ln := rfl
@[simp] lemma RsaV.get_ob (V : RsaV X A) : V.get .ob = V.ob := rfl
@[simp] lemma RsaV.get_sm (V : RsaV X A) : V.get .sm = V.sm := rfl
@[simp] lemma RsaV.get_pz (V : RsaV X A) : V.get .pz = V.pz := rfl
@[simp] lemma RsaV.get_sm2 (V : RsaV X A) : V.get .sm2 = V.sm2 := rfl
@[simp] lemma RsaV.get_ea (V : RsaV X A) : V.get .ea = V.ea := rfl
@[simp] lemma RsaV.get_eb (V : RsaV X A) : V.get .eb = V.eb := rfl
@[simp] lemma RsaV.get_er (V : RsaV X A) : V.get .er = V.er := rfl
@[simp] lemma RsaV.get_cS (V : RsaV X A) : V.get .cS = V.cS := rfl
@[simp] lemma RsaV.get_cM (V : RsaV X A) : V.get .cM = V.cM := rfl
@[simp] lemma RsaV.get_cP (V : RsaV X A) : V.get .cP = V.cP := rfl
@[simp] lemma RsaV.get_cW (V : RsaV X A) : V.get .cW = V.cW := rfl
@[simp] lemma RsaV.get_cT (V : RsaV X A) : V.get .cT = V.cT := rfl
@[simp] lemma RsaV.get_kW (V : RsaV X A) : V.get .kW = V.kW := rfl
@[simp] lemma RsaV.get_kT (V : RsaV X A) : V.get .kT = V.kT := rfl
@[simp] lemma RsaV.get_kx (V : RsaV X A) : V.get .kx = V.kx := rfl
@[simp] lemma RsaV.get_ka (V : RsaV X A) : V.get .ka = V.ka := rfl
@[simp] lemma RsaV.get_kb (V : RsaV X A) : V.get .kb = V.kb := rfl
@[simp] lemma RsaV.get_atm (V : RsaV X A) : V.get .atm = V.atm := rfl
@[simp] lemma RsaV.get_rr (V : RsaV X A) : V.get .rr = V.rr := rfl
@[simp] lemma RsaV.get_bS (V : RsaV X A) : V.get .bS = V.bS := rfl
@[simp] lemma RsaV.get_bxa (V : RsaV X A) : V.get .bxa = V.bxa := rfl
@[simp] lemma RsaV.get_bya (V : RsaV X A) : V.get .bya = V.bya := rfl
@[simp] lemma RsaV.get_bza (V : RsaV X A) : V.get .bza = V.bza := rfl

lemma RsaR.c_injective : Function.Injective (RsaR.c : CR → RsaR X) := fun _ _ h => RsaR.c.inj h

lemma RsaV.upd_c [DecidableEq X] (V : RsaV X A) (x : CR) (l : List (Fin (A + 4))) :
    Function.update V.get (.c x) l = { V with cr := Function.update V.cr x l }.get := by
  funext r
  cases r <;> simp [RsaV.get, Function.update_apply]

lemma RsaV.upd_x [DecidableEq X] (V : RsaV X A) (j : X) (l : List (Fin (A + 4))) :
    Function.update V.get (.x j) l = { V with xr := Function.update V.xr j l }.get := by
  funext r
  cases r <;> simp [RsaV.get, Function.update_apply]

lemma RsaV.extend_c [DecidableEq X] (V : RsaV X A) (ρ : CR → List (Fin (A + 4))) :
    Function.extend RsaR.c ρ V.get = { V with cr := ρ }.get := by
  funext r
  cases r with
  | c x => exact RsaR.c_injective.extend_apply _ _ x
  | _ => exact Function.extend_apply' _ _ _ (by rintro ⟨_, h⟩; cases h)

lemma RsaV.upd_ln [DecidableEq X] (V : RsaV X A) (l : List (Fin (A + 4))) :
    Function.update V.get .ln l = { V with ln := l }.get := by
  funext r
  cases r <;> simp [RsaV.get]

lemma RsaV.upd_ob [DecidableEq X] (V : RsaV X A) (l : List (Fin (A + 4))) :
    Function.update V.get .ob l = { V with ob := l }.get := by
  funext r
  cases r <;> simp [RsaV.get]

lemma RsaV.upd_sm [DecidableEq X] (V : RsaV X A) (l : List (Fin (A + 4))) :
    Function.update V.get .sm l = { V with sm := l }.get := by
  funext r
  cases r <;> simp [RsaV.get]

lemma RsaV.upd_pz [DecidableEq X] (V : RsaV X A) (l : List (Fin (A + 4))) :
    Function.update V.get .pz l = { V with pz := l }.get := by
  funext r
  cases r <;> simp [RsaV.get]

lemma RsaV.upd_sm2 [DecidableEq X] (V : RsaV X A) (l : List (Fin (A + 4))) :
    Function.update V.get .sm2 l = { V with sm2 := l }.get := by
  funext r
  cases r <;> simp [RsaV.get]

lemma RsaV.upd_ea [DecidableEq X] (V : RsaV X A) (l : List (Fin (A + 4))) :
    Function.update V.get .ea l = { V with ea := l }.get := by
  funext r
  cases r <;> simp [RsaV.get]

lemma RsaV.upd_eb [DecidableEq X] (V : RsaV X A) (l : List (Fin (A + 4))) :
    Function.update V.get .eb l = { V with eb := l }.get := by
  funext r
  cases r <;> simp [RsaV.get]

lemma RsaV.upd_er [DecidableEq X] (V : RsaV X A) (l : List (Fin (A + 4))) :
    Function.update V.get .er l = { V with er := l }.get := by
  funext r
  cases r <;> simp [RsaV.get]

lemma RsaV.upd_cS [DecidableEq X] (V : RsaV X A) (l : List (Fin (A + 4))) :
    Function.update V.get .cS l = { V with cS := l }.get := by
  funext r
  cases r <;> simp [RsaV.get]

lemma RsaV.upd_cM [DecidableEq X] (V : RsaV X A) (l : List (Fin (A + 4))) :
    Function.update V.get .cM l = { V with cM := l }.get := by
  funext r
  cases r <;> simp [RsaV.get]

lemma RsaV.upd_cP [DecidableEq X] (V : RsaV X A) (l : List (Fin (A + 4))) :
    Function.update V.get .cP l = { V with cP := l }.get := by
  funext r
  cases r <;> simp [RsaV.get]

lemma RsaV.upd_cW [DecidableEq X] (V : RsaV X A) (l : List (Fin (A + 4))) :
    Function.update V.get .cW l = { V with cW := l }.get := by
  funext r
  cases r <;> simp [RsaV.get]

lemma RsaV.upd_cT [DecidableEq X] (V : RsaV X A) (l : List (Fin (A + 4))) :
    Function.update V.get .cT l = { V with cT := l }.get := by
  funext r
  cases r <;> simp [RsaV.get]

lemma RsaV.upd_kW [DecidableEq X] (V : RsaV X A) (l : List (Fin (A + 4))) :
    Function.update V.get .kW l = { V with kW := l }.get := by
  funext r
  cases r <;> simp [RsaV.get]

lemma RsaV.upd_kT [DecidableEq X] (V : RsaV X A) (l : List (Fin (A + 4))) :
    Function.update V.get .kT l = { V with kT := l }.get := by
  funext r
  cases r <;> simp [RsaV.get]

lemma RsaV.upd_kx [DecidableEq X] (V : RsaV X A) (l : List (Fin (A + 4))) :
    Function.update V.get .kx l = { V with kx := l }.get := by
  funext r
  cases r <;> simp [RsaV.get]

lemma RsaV.upd_ka [DecidableEq X] (V : RsaV X A) (l : List (Fin (A + 4))) :
    Function.update V.get .ka l = { V with ka := l }.get := by
  funext r
  cases r <;> simp [RsaV.get]

lemma RsaV.upd_kb [DecidableEq X] (V : RsaV X A) (l : List (Fin (A + 4))) :
    Function.update V.get .kb l = { V with kb := l }.get := by
  funext r
  cases r <;> simp [RsaV.get]

lemma RsaV.upd_atm [DecidableEq X] (V : RsaV X A) (l : List (Fin (A + 4))) :
    Function.update V.get .atm l = { V with atm := l }.get := by
  funext r
  cases r <;> simp [RsaV.get]

lemma RsaV.upd_rr [DecidableEq X] (V : RsaV X A) (l : List (Fin (A + 4))) :
    Function.update V.get .rr l = { V with rr := l }.get := by
  funext r
  cases r <;> simp [RsaV.get]

lemma RsaV.upd_bS [DecidableEq X] (V : RsaV X A) (l : List (Fin (A + 4))) :
    Function.update V.get .bS l = { V with bS := l }.get := by
  funext r
  cases r <;> simp [RsaV.get]

lemma RsaV.upd_bxa [DecidableEq X] (V : RsaV X A) (l : List (Fin (A + 4))) :
    Function.update V.get .bxa l = { V with bxa := l }.get := by
  funext r
  cases r <;> simp [RsaV.get]

lemma RsaV.upd_bya [DecidableEq X] (V : RsaV X A) (l : List (Fin (A + 4))) :
    Function.update V.get .bya l = { V with bya := l }.get := by
  funext r
  cases r <;> simp [RsaV.get]

lemma RsaV.upd_bza [DecidableEq X] (V : RsaV X A) (l : List (Fin (A + 4))) :
    Function.update V.get .bza l = { V with bza := l }.get := by
  funext r
  cases r <;> simp [RsaV.get]

/-! ### Programs -/

noncomputable section

section Programs

variable {T Q A : ℕ} {U P X : Type} (rg : RsaR X → Fin T) (ι : Fin 64 → Fin T)
  (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)

/-- One term of a window: the product of the records on top of `xs` (extended line) and `ys`
(table) onto `acc`, moved to `pz` and added to the running sum `sm` (through `sm2`). -/
def rsaTermP : Pr P T Q A U :=
  .seq (rmulOne ι hι hT hQ (fun x => rg (.c x)))
  (.seq (moveR (rg (.c .acc)) (rg .pz) id)
  (.seq (autoWords ![rg .sm, rg .pz] ![rg .sm2] (rg .sm2) (rg (.c .wn)) (rg .atm) (rsaAddAuto A))
    (moveR (rg .sm2) (rg .sm) id)))

/-- One output of a line: a zero sum, the `2m + 1` terms of the window (counter `cW`), the
window moved back from `xsv` onto `xs`, the sum onto `ob`, and the window advanced by one
record (`w` symbols off `xs`) when `rr := (rr + bS) mod 2^L` carries. -/
def rsaRowP : Pr P T Q A U :=
  .seq (umulSym 1 (pairSym A false false) (rg (.c .wn)) (rg .sm) (rg .kx))
  (.seq (scanP (rg .cW) (rg .kW) (rsaTermP rg ι hι hT hQ))
  (.seq (moveR (rg (.c .xsv)) (rg (.c .xs)) id)
  (.seq (moveR (rg .sm) (rg .ob) id)
  (.seq (baddTo (rg .rr) (rg .bS) (rg .bxa) (rg .bya) (rg .bza) (rg .bza))
    (.cond (fun v => symBit (v.scan (rg .bza))) (usub (rg (.c .wn)) (rg (.c .xs)) (rg .kx))
      (.act .done))))))

/-- A counted transfer: move `|cnt|` symbols from `src` to `dst` (reversing them). -/
def rsaXferP (cnt sp src dst : RsaR X) : Pr P T Q A U :=
  scanP (rg cnt) (rg sp) (.act (popPush (rg src) (rg dst)))

/-- **One line.** The `s` records of the line move from `ln` to `ea`; the cyclic extension
`E = N.drop (s - m) ++ N ++ N.take m` is built on `xs` (counters `cS = s w`, `cM = m w`); the
padding (`cP = (t - s) w` symbols) is dropped from `ln`; the `t` outputs (counter `cT`) go onto
`ob`; the table is restored and `xs` cleared. -/
def rsaLineP : Pr P T Q A U :=
  .seq (rsaXferP rg .cS .ka .ln .er)
  (.seq (moveR (rg .er) (rg .ea) id)
  (.seq (bcopy (rg .ea) (rg .eb) (rg .ka) (rg .kb))
  (.seq (rsaXferP rg .cM .ka .eb .er)
  (.seq (uclear (rg .eb))
  (.seq (moveR (rg .er) (rg (.c .xs)) id)
  (.seq (bcopy (rg .ea) (rg (.c .xs)) (rg .ka) (rg .kb))
  (.seq (moveR (rg .ea) (rg .er) id)
  (.seq (rsaXferP rg .cM .ka .er (.c .xs))
  (.seq (uclear (rg .er))
  (.seq (usub (rg .cP) (rg .ln) (rg .kx))
  (.seq (scanP (rg .cT) (rg .kT) (rsaRowP rg ι hι hT hQ))
  (.seq (moveR (rg (.c .ysv)) (rg (.c .ys)) id)
    (uclear (rg (.c .xs)))))))))))))))

end Programs

/-! ### One term -/

section Term

variable {T Q A : ℕ} {U P X : Type} [DecidableEq X] {body : P → Pr P T Q A U}
  {rg : RsaR X → Fin T} {ι : Fin 64 → Fin T}

/-- The complex-product registers inside a window: `xs` holds the rest `xr` of the extended
line, `xsv` the window records `xd` taken so far (reversed), `ys` the rest `tr` of the table and
`ysv` the table entries `td` taken so far (reversed). -/
def rsaCr (ρ : CR → List (Fin (A + 4))) (w : ℕ) (xr xd tr td : List GaussianInt) :
    CR → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update ρ .xs (cstream A w xr))
    .xsv (cstream A w xd).reverse) .ys (cstream A w tr)) .ysv (cstream A w td).reverse

lemma rsa_ready_cr {ρ : CR → List (Fin (A + 4))} {w q : ℕ} (hr : Ready ρ w q)
    (xr xd tr td : List GaussianInt) : Ready (rsaCr ρ w xr xd tr td) w q :=
  (((hr.update .xs (by simp) _).update .xsv (by simp) _).update .ys (by simp) _).update .ysv
    (by simp) _

lemma rsaCr_one (ρ : CR → List (Fin (A + 4))) (w : ℕ) (a b : GaussianInt)
    (xr xd tr td : List GaussianInt) (z : GaussianInt) (hacc : ρ .acc = []) :
    Function.update (oneSt (rsaCr ρ w (a :: xr) xd (b :: tr) td) w a b (cstream A w xr)
      (cstream A w tr) z) .acc [] = rsaCr ρ w xr (xd ++ [a]) tr (td ++ [b]) := by
  funext x
  cases x <;> simp [oneSt, opSt, rsaCr, hacc]

lemma rsa_csyms_add (A w : ℕ) (P z : GaussianInt) :
    coeffSyms A w (red w P + red w z) = csyms A w (P + z) := by
  rw [csyms, red_add]

/-- The step bound of one term. -/
def rsaTermCost (T w : ℕ) : ℕ := rmulCost T w + 9 * w + 12

variable (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
include hrg hdisj

/-- **One term.** With `a` on top of `xs` and the real `b` on top of `ys`, the running sum `sm`
goes from `P` to `P + tdivN q (a b)`; `a`, `b` move to the save registers. -/
theorem rsa_term (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w q : ℕ} (hw : 1 ≤ w) (hq : q ≤ w) (V : RsaV X A) (hr : Ready V.cr w q)
    (hacc : V.cr .acc = []) (hatm : V.atm = []) {a b : GaussianInt} (ha : Fits w a)
    (hb : Fits w b) (hbi : b.im = 0) (xr xd tr td : List GaussianInt) (P : GaussianInt) :
    RsaRuns body rg ι (rsaTermP rg ι hι hT hQ)
      { V with
        cr := rsaCr V.cr w (a :: xr) xd (b :: tr) td, sm := csyms A w P, pz := [], sm2 := [] }.get
      { V with
        cr := rsaCr V.cr w xr (xd ++ [a]) tr (td ++ [b]), sm := csyms A w (P + tdivN q (a * b)),
        pz := [], sm2 := [] }.get
      (rsaTermCost T w) := by
  have hcr : Function.Injective (fun x => rg (RsaR.c x : RsaR X)) :=
    hrg.comp RsaR.c_injective
  have hdisj' : ∀ x j, rg (RsaR.c x : RsaR X) ≠ ι j := fun x j => hdisj _ j
  set z := tdivN q (a * b) with hz
  set V₁ : RsaV X A := { V with
    cr := rsaCr V.cr w (a :: xr) xd (b :: tr) td, sm := csyms A w P, pz := [], sm2 := [] }
    with hV₁
  set V₂ : RsaV X A := { V₁ with cr := oneSt V₁.cr w a b (cstream A w xr) (cstream A w tr) z }
    with hV₂
  set V₃ : RsaV X A := { V₂ with cr := Function.update V₂.cr .acc [], pz := csyms A w z }
    with hV₃
  set V₄ : RsaV X A := { V₃ with
    sm := [], pz := [], sm2 := (coeffSyms A w (red w P + red w z)).reverse } with hV₄
  set V₅ : RsaV X A := { V₄ with sm := csyms A w (P + z), sm2 := [] } with hV₅
  have h1 : RsaRuns body rg ι (rmulOne ι hι hT hQ (fun x => rg (.c x))) V₁.get V₂.get
      (rmulCost T w) :=
    (RsaRuns.of_c (c := RsaR.c) hrg RsaR.c_injective
      (rmulOne_runs (body := body) hcr hdisj' hι hT hQ hA (rsa_ready_cr hr _ _ _ _) hw hq ha hb hbi
        (rx := cstream A w xr) (ry := cstream A w tr) (by simp [hV₁, rsaCr])
        (by simp [hV₁, rsaCr])) V₁.get (fun _ => rfl)).congr (RsaV.extend_c _ _)
  have h2 : RsaRuns body rg ι (moveR (rg (.c .acc)) (rg .pz) id) V₂.get V₃.get (2 * w + 2) :=
    ((rsa_moveR (body := body) (ι := ι) hrg (a := .c .acc) (b := .pz) (by simp) V₂.get).congr
      (by rw [RsaV.upd_c, RsaV.upd_pz]; simp [hV₃, hV₂, hV₁, oneSt, rsaCr, hacc])).mono
      (by simp [hV₂, hV₁, oneSt, rsaCr, hacc])
  have h3 : RsaRuns body rg ι
      (autoWords ![rg .sm, rg .pz] ![rg .sm2] (rg .sm2) (rg (.c .wn)) (rg .atm) (rsaAddAuto A))
      V₃.get V₄.get (5 * w + 8) :=
    (rsa_add (body := body) (ι := ι) hrg (x := .sm) (y := .pz) (o := .sm2)
      (ctr := .c .wn) (tmp := .atm) (st := .sm2) (by simp) (by simp) (by simp) hA hw V₃.get
      (by simp [hV₃, hV₂, hV₁, oneSt, opSt, rsaCr, hr.wn]) (by simp [hV₃, hV₂, hV₁, hatm])
      (red w P) (red w z) (by simp [hV₃, hV₂, hV₁, csyms]) (by simp [hV₃, csyms])).congr
      (by rw [RsaV.upd_sm, RsaV.upd_pz, RsaV.upd_sm2]; simp [hV₄, hV₃, hV₂, hV₁])
  have h4 : RsaRuns body rg ι (moveR (rg .sm2) (rg .sm) id) V₄.get V₅.get (2 * w + 2) :=
    ((rsa_moveR (body := body) (ι := ι) hrg (a := .sm2) (b := .sm) (by simp) V₄.get).congr
      (by rw [RsaV.upd_sm2, RsaV.upd_sm]; simp [hV₅, hV₄, rsa_csyms_add])).mono (by simp [hV₄])
  refine ((h1.seq hdisj (h2.seq hdisj (h3.seq hdisj h4))).congr ?_).mono ?_
  · congr 1
    ext1
    · simp [hV₅, hV₄, hV₃, hV₂, hV₁, rsaCr_one _ _ _ _ _ _ _ _ _ hacc]
    all_goals simp [hV₅, hV₄, hV₃, hV₂, hV₁]
  · unfold rsaTermCost; omega


/-! ### The window of one output -/

/-- The step bound of the terms of one window. -/
def rsaTermsCost (T w n : ℕ) : ℕ := n * (rsaTermCost T w + 3) + 2 * n + 4

/-- The register file inside a window, before term `i`. -/
def rsaTV (V : RsaV X A) (q w : ℕ) (E tab : List GaussianInt) (e j i : ℕ) : RsaV X A :=
  { V with
    cr := rsaCr V.cr w (E.drop (e + i)) ((E.drop e).take i) (tab.drop (j + i)) (tab.take (j + i))
    sm := csyms A w (rsaPart q E e (fun i => tab.getD (j + i) 0) i)
    pz := []
    sm2 := [] }

/-- **The terms of one window.** The counter `cW` holds `n` symbols; `xs` holds the extended line
from `e` on and `ys` the table from `j` on. Afterwards `sm` holds the window sum
`rsaPart q E e (tab_{j + ·}) n`, the window is on `xsv` and the `n` table entries on `ysv`. -/
theorem rsa_terms (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w q : ℕ} (hw : 1 ≤ w) (hq : q ≤ w) (V : RsaV X A) (hr : Ready V.cr w q)
    (hacc : V.cr .acc = []) (hatm : V.atm = []) (hkW : V.kW = []) {n : ℕ}
    (hcW : V.cW.length = n) (E tab : List GaussianInt) (e j : ℕ) (hE : e + n ≤ E.length)
    (htab : j + n ≤ tab.length) (hFE : ∀ x ∈ E, Fits w x)
    (hFT : ∀ y ∈ tab, Fits w y ∧ y.im = 0) :
    RsaRuns body rg ι (scanP (rg .cW) (rg .kW) (rsaTermP rg ι hι hT hQ))
      (rsaTV V q w E tab e j 0).get (rsaTV V q w E tab e j n).get (rsaTermsCost T w n) := by
  have H := rsa_scanP_runs (body := body) (ι := ι) hrg hdisj (a := .cW) (t := .kW) (by simp)
    (fun i => (rsaTV V q w E tab e j i).get) (b := rsaTermCost T w) V.cW (fun i hi => by
      have hiE : e + i < E.length := by omega
      have hiT : j + i < tab.length := by omega
      have h := rsa_term (body := body) hrg hdisj hι hT hQ hA hw hq
        { V with cW := V.cW.drop (i + 1), kW := (V.cW.take (i + 1)).reverse } hr hacc hatm
        (a := E.getD (e + i) 0) (b := tab.getD (j + i) 0)
        (hFE _ (rsa_getD_mem E 0 hiE)) (hFT _ (rsa_getD_mem tab 0 hiT)).1
        (hFT _ (rsa_getD_mem tab 0 hiT)).2
        (E.drop (e + i + 1)) ((E.drop e).take i) (tab.drop (j + i + 1)) (tab.take (j + i))
        (rsaPart q E e (fun i => tab.getD (j + i) 0) i)
      refine (h.congr_pre ?_).congr ?_
      · rw [RsaV.upd_cW, RsaV.upd_kW]
        simp only [rsaTV]
        rw [← rsa_drop_getD E 0 hiE, ← rsa_drop_getD tab 0 hiT]
      · rw [RsaV.upd_cW, RsaV.upd_kW]
        simp only [rsaTV]
        rw [← rsa_take_drop_succ E 0 hiE, ← rsa_take_succ tab 0 hiT, rsaPart_succ,
          Nat.add_assoc, Nat.add_assoc])
  rw [hcW] at H
  refine (H.congr_pre ?_).congr ?_
  · rw [RsaV.upd_cW, RsaV.upd_kW]
    congr 1
    ext1 <;> simp [rsaTV, hkW]
  · rw [RsaV.upd_cW, RsaV.upd_kW]
    congr 1
    ext1 <;> simp [rsaTV, hkW]

lemma rsaCr_rsaCr (ρ : CR → List (Fin (A + 4))) (w : ℕ) (a b c d a' b' c' d' : List GaussianInt) :
    rsaCr (rsaCr ρ w a b c d) w a' b' c' d' = rsaCr ρ w a' b' c' d' := by
  funext x
  cases x <;> simp [rsaCr]

/-- The register file before an output: the extended line from `e` on in `xs`, the table from
`j` on in `ys` (the entries before `j` reversed on `ysv`), the residue `r` in `rr` and the
output register `ob`. -/
def rsaRV (V : RsaV X A) (w L : ℕ) (E tab : List GaussianInt) (e j r : ℕ)
    (ob : List (Fin (A + 4))) : RsaV X A :=
  { V with
    cr := rsaCr V.cr w (E.drop e) [] (tab.drop j) (tab.take j)
    rr := binSyms L r
    ob := ob }

/-- The step bound of one output. -/
def rsaRowCost (T w n L : ℕ) : ℕ :=
  4 * w + 4 + rsaTermsCost T w n + (2 * (n * w) + 2) + (2 * w + 2) + (8 * L + 8 + (4 * w + 5))

/-- **One output.** The window sum of `E` from `e` against the table from `j` goes on top of
`ob`; the table advances by `n`; `rr` goes from `r` to `(r + s) mod 2^L` and the window start
advances by its carry. -/
theorem rsa_row (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w q : ℕ} (hw : 1 ≤ w) (hq : q ≤ w) (V : RsaV X A) (hr : Ready V.cr w q)
    (hacc : V.cr .acc = []) (hatm : V.atm = []) (hkW : V.kW = []) (hkx : V.kx = [])
    (hsm : V.sm = []) (hpz : V.pz = []) (hsm2 : V.sm2 = []) (hbx : V.bxa = [])
    (hby : V.bya = []) (hbz : V.bza = []) {n : ℕ} (hn : 1 ≤ n) (hcW : V.cW.length = n)
    {L s : ℕ} (hs : s < 2 ^ L) (hbS : V.bS = binSyms L s) (E tab : List GaussianInt)
    (e j r : ℕ) (hrL : r < 2 ^ L) (hE : e + n ≤ E.length) (htab : j + n ≤ tab.length)
    (hFE : ∀ x ∈ E, Fits w x) (hFT : ∀ y ∈ tab, Fits w y ∧ y.im = 0)
    (ob : List (Fin (A + 4))) :
    RsaRuns body rg ι (rsaRowP rg ι hι hT hQ) (rsaRV V w L E tab e j r ob).get
      (rsaRV V w L E tab (e + if 2 ^ L ≤ r + s then 1 else 0) (j + n) ((r + s) % 2 ^ L)
        ((csyms A w (rsaPart q E e (fun i => tab.getD (j + i) 0) n)).reverse ++ ob)).get
      (rsaRowCost T w n L) := by
  set V₁ : RsaV X A := { V with rr := binSyms L r, ob := ob } with hV₁
  have hwn : (V.cr .wn).length = w := hr.wn
  have h1 : RsaRuns body rg ι (umulSym 1 (pairSym A false false) (rg (.c .wn)) (rg .sm) (rg .kx))
      (rsaRV V w L E tab e j r ob).get (rsaTV V₁ q w E tab e j 0).get (4 * w + 4) :=
    ((rsa_umulSym (body := body) (ι := ι) hrg 1 (pairSym A false false) (a := .c .wn) (b := .sm)
      (t := .kx) (by simp) (by simp) (by simp) _ (by simp [rsaRV, hkx])).congr (by
        rw [RsaV.upd_sm]
        congr 1
        ext1
        · simp [rsaRV, rsaTV, hV₁, rsaCr]
        all_goals simp [rsaRV, rsaTV, hV₁, rsaCr, hsm, hpz, hsm2, rsa_csyms_zero, hwn, rsaPart])).mono
      (by simp [rsaRV, rsaCr, hwn])
  have h2 := rsa_terms (body := body) hrg hdisj hι hT hQ hA hw hq V₁ hr hacc hatm hkW hcW E tab e j
    hE htab hFE hFT
  set V₃ : RsaV X A := { V₁ with
    cr := rsaCr V.cr w (E.drop e) [] (tab.drop (j + n)) (tab.take (j + n))
    sm := csyms A w (rsaPart q E e (fun i => tab.getD (j + i) 0) n), pz := [], sm2 := [] }
    with hV₃
  have hxsv : ((cstream A w ((E.drop e).take n)).reverse).length = n * w := by
    simp; omega
  have h3 : RsaRuns body rg ι (moveR (rg (.c .xsv)) (rg (.c .xs)) id)
      (rsaTV V₁ q w E tab e j n).get V₃.get (2 * (n * w) + 2) :=
    ((rsa_moveR (body := body) (ι := ι) hrg (a := .c .xsv) (b := .c .xs) (by simp) _).congr (by
      rw [RsaV.upd_c, RsaV.upd_c]
      congr 1
      ext1
      · funext x
        have hd : (E.drop e).take n ++ E.drop (e + n) = E.drop e := by
          rw [← List.drop_drop, List.take_append_drop]
        cases x <;> simp [rsaTV, hV₃, hV₁, rsaCr, ← cstream_append, hd]
      all_goals simp [rsaTV, hV₃])).mono
      (by simp [rsaTV, rsaCr, Nat.min_eq_left (by omega : n ≤ E.length - e)])
  set V₄ : RsaV X A := { V₃ with
    sm := [], ob := (csyms A w (rsaPart q E e (fun i => tab.getD (j + i) 0) n)).reverse ++ ob }
    with hV₄
  have h4 : RsaRuns body rg ι (moveR (rg .sm) (rg .ob) id) V₃.get V₄.get (2 * w + 2) :=
    ((rsa_moveR (body := body) (ι := ι) hrg (a := .sm) (b := .ob) (by simp) _).congr (by
      rw [RsaV.upd_sm, RsaV.upd_ob]; rfl)).mono (by simp [hV₃, csyms])
  have hE1 : e < E.length := by omega
  have hp := (rsa_usub (body := body) (ι := ι) hrg (a := .c .wn) (b := .c .xs) (t := .kx)
    (by simp) (by simp) (by simp) (Function.update V₄.get .rr (binSyms L ((r + s) % 2 ^ L)))
    (by simp [hV₄, hV₃, hV₁, hkx]))
  have hq' := rsa_done (body := body) (ι := ι) hrg
    (Function.update V₄.get .rr (binSyms L ((r + s) % 2 ^ L)))
  have h5 := rsa_baddTo_cond (body := body) hrg hdisj (a := .rr) (b := .bS) (tx := .bxa)
    (ty := .bya) (tz := .bza) (cy := .bza) (by simp) (by simp) (by simp) hrL hs V₄.get
    (by simp [hV₄, hV₃, hV₁]) (by simp [hV₄, hV₃, hV₁, hbS]) (by simp [hV₄, hV₃, hV₁, hbx])
    (by simp [hV₄, hV₃, hV₁, hby]) (by simp [hV₄, hV₃, hV₁, hbz]) hp hq'
  refine ((h1.seq hdisj (h2.seq hdisj (h3.seq hdisj (h4.seq hdisj h5)))).congr ?_).mono ?_
  · rw [RsaV.upd_rr]
    have hdrop : (cstream A w (E.drop e)).drop w = cstream A w (E.drop (e + 1)) := by
      have := rsa_cstream_drop (A := A) (w := w) (E.drop e) 1
      rw [one_mul, List.drop_drop] at this
      rw [this]
    split_ifs with hc
    · rw [RsaV.upd_c]
      congr 1
      ext1
      · funext x
        cases x <;> simp [rsaRV, hV₄, hV₃, hV₁, rsaCr, hwn, hdrop]
      all_goals simp [rsaRV, hV₄, hV₃, hV₁, hsm, hpz, hsm2]
    · congr 1
      ext1
      · funext x
        cases x <;> simp [rsaRV, hV₄, hV₃, hV₁, rsaCr]
      all_goals simp [rsaRV, hV₄, hV₃, hV₁, hsm, hpz, hsm2]
  · simp only [rsaRowCost]
    have : max (4 * (Function.update V₄.get RsaR.rr (binSyms L ((r + s) % 2 ^ L)) (.c .wn)).length
      + 4) 1 = 4 * w + 4 := by simp [hV₄, hV₃, hV₁, rsaCr, hwn]
    rw [this]
    omega

/-- The step bound of the outputs of one line. -/
def rsaRowsCost (T w n L t : ℕ) : ℕ := t * (rsaRowCost T w n L + 3) + 2 * t + 4

/-- **The outputs of one line.** From the extended line `E` (`s + 2m` records) on `xs` and the
table `rsaTabL t n wt` on `ys` (`n = 2m + 1`, `t = 2^L`), the `t` outputs
`rsaOut q s t n E wt` go onto `ob` (reversed), the table moves to `ysv` and `xs` keeps the last
`2m` records of `E`. -/
theorem rsa_rows (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w q : ℕ} (hw : 1 ≤ w) (hq : q ≤ w) (V : RsaV X A) (hr : Ready V.cr w q)
    (hacc : V.cr .acc = []) (hatm : V.atm = []) (hkW : V.kW = []) (hkx : V.kx = [])
    (hsm : V.sm = []) (hpz : V.pz = []) (hsm2 : V.sm2 = []) (hbx : V.bxa = [])
    (hby : V.bya = []) (hbz : V.bza = []) (hkT : V.kT = []) {m : ℕ}
    (hcW : V.cW.length = 2 * m + 1) {L s t : ℕ} (ht : t = 2 ^ L) (hst : s < t) (hs0 : 0 < s)
    (hbS : V.bS = binSyms L s) (hcT : V.cT.length = t) (E : List GaussianInt)
    (hE : E.length = s + 2 * m) (wt : ℕ → ℕ → GaussianInt) (hFE : ∀ x ∈ E, Fits w x)
    (hFT : ∀ y ∈ rsaTabL t (2 * m + 1) wt, Fits w y ∧ y.im = 0) :
    RsaRuns body rg ι (scanP (rg .cT) (rg .kT) (rsaRowP rg ι hι hT hQ))
      (rsaRV V w L E (rsaTabL t (2 * m + 1) wt) 0 0 0 V.ob).get
      (rsaRV V w L E (rsaTabL t (2 * m + 1) wt) s (t * (2 * m + 1)) 0
        ((cstream A w (rsaOut q s t (2 * m + 1) E wt)).reverse ++ V.ob)).get
      (rsaRowsCost T w (2 * m + 1) L t) := by
  set n := 2 * m + 1 with hn
  set tab := rsaTabL t n wt with htab
  set outs := rsaOut q s t n E wt with houts
  have hsL : s < 2 ^ L := ht ▸ hst
  have htl : tab.length = t * n := length_rsaTabL t n wt
  have H := rsa_scanP_runs (body := body) (ι := ι) hrg hdisj (a := .cT) (t := .kT) (by simp)
    (fun k => (rsaRV V w L E tab (rsaCen s t k) (k * n) (s * k % t)
      ((cstream A w (outs.take k)).reverse ++ V.ob)).get) (b := rsaRowCost T w n L) V.cT
    (fun k hk => by
      rw [hcT] at hk
      have hc := rsaCen_lt hst.le hk hs0
      have h := rsa_row (body := body) hrg hdisj hι hT hQ hA hw hq
        { V with cT := V.cT.drop (k + 1), kT := (V.cT.take (k + 1)).reverse } hr hacc hatm hkW
        hkx hsm hpz hsm2 hbx hby hbz (by omega) hcW hsL hbS E tab (rsaCen s t k) (k * n)
        (s * k % t) (by rw [ht]; exact Nat.mod_lt _ (by positivity)) (by omega)
        (by rw [htl]; nlinarith) hFE hFT ((cstream A w (outs.take k)).reverse ++ V.ob)
      refine (h.congr_pre ?_).congr ?_
      · rw [RsaV.upd_cT, RsaV.upd_kT]; rfl
      · rw [RsaV.upd_cT, RsaV.upd_kT]
        have e1 : rsaCen s t k + (if 2 ^ L ≤ s * k % t + s then 1 else 0) = rsaCen s t (k + 1) := by
          rw [rsaCen_succ hst, ← ht]
        have e2 : (s * k % t + s) % 2 ^ L = s * (k + 1) % t := by
          rw [rsaCen_succ_mod, ← ht]
        have e3 : k * n + n = (k + 1) * n := by ring
        have e4 : (csyms A w (rsaPart q E (rsaCen s t k) (fun i => tab.getD (k * n + i) 0) n)).reverse
            ++ ((cstream A w (outs.take k)).reverse ++ V.ob) =
            (cstream A w (outs.take (k + 1))).reverse ++ V.ob := by
          rw [htab, rsaPart_tab q E _ t n wt hk, houts, rsaOut_take_succ q s t n E wt hk]
          simp
        rw [e1, e2, e3, e4]
        rfl)
  rw [hcT] at H
  refine (H.congr_pre ?_).congr ?_
  · rw [RsaV.upd_cT, RsaV.upd_kT]
    congr 1
    ext1 <;> simp [rsaRV, hkT, rsaCen_zero]
  · rw [RsaV.upd_cT, RsaV.upd_kT]
    have ht0 : 0 < t := by omega
    have e1 : outs.take t = outs := List.take_of_length_le (by simp [houts, rsaOut])
    congr 1
    ext1 <;> simp [rsaRV, hkT, rsaCen_self ht0, Nat.mul_mod_left, e1, Nat.mul_comm s t]

/-- The step bound of one line of `s` records, `t` outputs, window `2m + 1`, `t = 2^L`. -/
def rsaLineCost (T w s t m L : ℕ) : ℕ :=
  (6 * (s * w) + 4) + (2 * (s * w) + 2) + (6 * (s * w) + 6) + (6 * (m * w) + 4) +
    (2 * ((s - m) * w) + 2) + (2 * (m * w) + 2) + (6 * (s * w) + 6) + (2 * (s * w) + 2) +
    (6 * (m * w) + 4) + (2 * ((s - m) * w) + 2) + (4 * ((t - s) * w) + 4) +
    rsaRowsCost T w (2 * m + 1) L t + (2 * (t * (2 * m + 1) * w) + 2) + (2 * (2 * m * w) + 2)

/-- **One line of `Ã`.** The box register `ln` holds the line `N` (`s` records, numerators at
scale `q`), then `t - s` padding records `Z`, then `rest`; `ys` holds the table
`rsaTabL t (2m + 1) wt`. Afterwards `ln` holds `rest` and `ob` gains the outputs
`rsaOut q s t (2m + 1) (rsaExt m N) wt` (reversed) on top; every other register is restored.
Conditions: `m ≤ s < t = 2^L`, all records of `N` and of the table fit `w` bits, the table is
real, `q ≤ w`; the counters `cS`, `cM`, `cP`, `cW`, `cT` hold `s w`, `m w`, `(t - s) w`,
`2m + 1`, `t` symbols; `bS` holds `s` in `L` bits and `rr` holds `0`; the scratch registers
are empty. -/
theorem rsa_line (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w q : ℕ} (hw : 1 ≤ w) (hq : q ≤ w) (V : RsaV X A) (hr : Ready V.cr w q)
    {L s t m : ℕ} (ht : t = 2 ^ L) (hst : s < t) (hms : m ≤ s) (hs0 : 0 < s)
    (wt : ℕ → ℕ → GaussianInt) (N Z : List GaussianInt) (rest : List (Fin (A + 4)))
    (hN : N.length = s) (hZ : Z.length = t - s) (hFN : ∀ x ∈ N, Fits w x)
    (hFT : ∀ y ∈ rsaTabL t (2 * m + 1) wt, Fits w y ∧ y.im = 0)
    (hxs : V.cr .xs = []) (hxsv : V.cr .xsv = [])
    (hys : V.cr .ys = cstream A w (rsaTabL t (2 * m + 1) wt)) (hysv : V.cr .ysv = [])
    (hacc : V.cr .acc = []) (hln : V.ln = cstream A w (N ++ Z) ++ rest)
    (hea : V.ea = []) (heb : V.eb = []) (her : V.er = []) (hka : V.ka = []) (hkb : V.kb = [])
    (hkx : V.kx = []) (hkW : V.kW = []) (hkT : V.kT = []) (hatm : V.atm = [])
    (hsm : V.sm = []) (hpz : V.pz = []) (hsm2 : V.sm2 = []) (hbx : V.bxa = [])
    (hby : V.bya = []) (hbz : V.bza = []) (hcS : V.cS.length = s * w)
    (hcM : V.cM.length = m * w) (hcP : V.cP.length = (t - s) * w)
    (hcW : V.cW.length = 2 * m + 1) (hcT : V.cT.length = t) (hrr : V.rr = binSyms L 0)
    (hbS : V.bS = binSyms L s) :
    RsaRuns body rg ι (rsaLineP rg ι hι hT hQ) V.get
      { V with
        ln := rest
        ob := (cstream A w (rsaOut q s t (2 * m + 1) (rsaExt m N) wt)).reverse ++ V.ob }.get
      (rsaLineCost T w s t m L) := by
  set D := cstream A w N with hD
  set Z' := cstream A w Z with hZ'
  set E := rsaExt m N with hE
  set tab := rsaTabL t (2 * m + 1) wt with htab
  have hDl : D.length = s * w := by simp [hD, hN]
  have hZl : Z'.length = (t - s) * w := by simp [hZ', hZ]
  have hEl : E.length = s + 2 * m := by rw [hE, length_rsaExt (by omega), hN]
  have hmw : m * w ≤ s * w := Nat.mul_le_mul_right _ hms
  have hln' : V.ln = D ++ (Z' ++ rest) := by rw [hln, cstream_append, List.append_assoc]
  -- 1. the line onto `er`
  set S₁ : RsaV X A := { V with ln := Z' ++ rest, er := D.reverse } with hS₁
  have h1 : RsaRuns body rg ι (rsaXferP rg .cS .ka .ln .er) V.get S₁.get (6 * (s * w) + 4) :=
    ((rsa_xfer (body := body) (ι := ι) hrg hdisj (a := .cS) (sp := .ka) (src := .ln) (dst := .er)
      (by simp) V.get (by simp [hka]) (by simp [hln', hcS, hDl])).congr (by
        rw [RsaV.upd_ln, RsaV.upd_er]
        congr 1
        ext1 <;> simp [hS₁, hln', hcS, ← hDl, her])).mono (by simp [hcS])
  -- 2. `ea := D`
  set S₂ : RsaV X A := { V with ln := Z' ++ rest, ea := D } with hS₂
  have h2 : RsaRuns body rg ι (moveR (rg .er) (rg .ea) id) S₁.get S₂.get (2 * (s * w) + 2) :=
    ((rsa_moveR (body := body) (ι := ι) hrg (a := .er) (b := .ea) (by simp) _).congr (by
      rw [RsaV.upd_er, RsaV.upd_ea]
      congr 1
      ext1 <;> simp [hS₂, hS₁, hea, her])).mono (by simp [hS₁, hDl])
  -- 3. `eb := D`
  set S₃ : RsaV X A := { S₂ with eb := D } with hS₃
  have h3 : RsaRuns body rg ι (bcopy (rg .ea) (rg .eb) (rg .ka) (rg .kb)) S₂.get S₃.get
      (6 * (s * w) + 6) :=
    ((rsa_bcopy (body := body) (ι := ι) hrg (a := .ea) (c := .eb) (t₁ := .ka) (t₂ := .kb)
      (by simp) _ (by simp [hS₂, hka]) (by simp [hS₂, hkb])).congr (by
        rw [RsaV.upd_eb]
        congr 1
        ext1 <;> simp [hS₃, hS₂, heb])).mono (by simp [hS₂, hDl])
  -- 4. `er := (D.take (m w)).reverse`, `eb := D.drop (m w)`
  set S₄ : RsaV X A := { S₂ with eb := D.drop (m * w), er := (D.take (m * w)).reverse }
    with hS₄
  have h4 : RsaRuns body rg ι (rsaXferP rg .cM .ka .eb .er) S₃.get S₄.get (6 * (m * w) + 4) :=
    ((rsa_xfer (body := body) (ι := ι) hrg hdisj (a := .cM) (sp := .ka) (src := .eb) (dst := .er)
      (by simp) _ (by simp [hS₃, hS₂, hka]) (by simp [hS₃, hS₂, hcM, hDl, hmw])).congr (by
        rw [RsaV.upd_eb, RsaV.upd_er]
        congr 1
        ext1 <;> simp [hS₄, hS₃, hS₂, hcM, her])).mono (by simp [hS₃, hS₂, hcM])
  -- 5. clear `eb`
  set S₅ : RsaV X A := { S₂ with er := (D.take (m * w)).reverse } with hS₅
  have h5 : RsaRuns body rg ι (uclear (rg .eb)) S₄.get S₅.get (2 * ((s - m) * w) + 2) :=
    ((rsa_uclear (body := body) (ι := ι) hrg .eb _).congr (by
      rw [RsaV.upd_eb]
      congr 1
      ext1 <;> simp [hS₅, hS₄, hS₂, heb])).mono (by simp [hS₄, hDl, Nat.sub_mul])
  -- 6. `xs := D.take (m w)`
  set S₆ : RsaV X A := { S₂ with cr := Function.update V.cr .xs (D.take (m * w)) } with hS₆
  have h6 : RsaRuns body rg ι (moveR (rg .er) (rg (.c .xs)) id) S₅.get S₆.get
      (2 * (m * w) + 2) :=
    ((rsa_moveR (body := body) (ι := ι) hrg (a := .er) (b := .c .xs) (by simp) _).congr (by
      rw [RsaV.upd_er, RsaV.upd_c]
      congr 1
      ext1
      · funext x; cases x <;> simp [hS₆, hS₅, hS₂, hxs]
      all_goals simp [hS₆, hS₅, hS₂, her])).mono (by simp [hS₅, hDl, hmw])
  -- 7. `xs := D ++ D.take (m w)`
  set S₇ : RsaV X A := { S₂ with cr := Function.update V.cr .xs (D ++ D.take (m * w)) }
    with hS₇
  have h7 : RsaRuns body rg ι (bcopy (rg .ea) (rg (.c .xs)) (rg .ka) (rg .kb)) S₆.get S₇.get
      (6 * (s * w) + 6) :=
    ((rsa_bcopy (body := body) (ι := ι) hrg (a := .ea) (c := .c .xs) (t₁ := .ka) (t₂ := .kb)
      (by simp) _ (by simp [hS₆, hS₂, hka]) (by simp [hS₆, hS₂, hkb])).congr (by
        rw [RsaV.upd_c]
        congr 1
        ext1
        · funext x; cases x <;> simp [hS₇, hS₆, hS₂]
        all_goals simp [hS₇, hS₆, hS₂])).mono (by simp [hS₆, hS₂, hDl])
  -- 8. `er := D.reverse`
  set S₈ : RsaV X A := { V with
    ln := Z' ++ rest, cr := Function.update V.cr .xs (D ++ D.take (m * w)), er := D.reverse }
    with hS₈
  have h8 : RsaRuns body rg ι (moveR (rg .ea) (rg .er) id) S₇.get S₈.get (2 * (s * w) + 2) :=
    ((rsa_moveR (body := body) (ι := ι) hrg (a := .ea) (b := .er) (by simp) _).congr (by
      rw [RsaV.upd_ea, RsaV.upd_er]
      congr 1
      ext1 <;> simp [hS₈, hS₇, hS₂, hea, her])).mono (by simp [hS₇, hS₂, hDl])
  -- 9. `xs := E`
  have hEs : (D.reverse.take (m * w)).reverse ++ (D ++ D.take (m * w)) = cstream A w E := by
    rw [hD, rsa_cstream_reverse_take, hN, rsa_cstream_take, ← cstream_append, ← cstream_append, hE,
      rsaExt, hN, List.append_assoc]
  set S₉ : RsaV X A := { V with
    ln := Z' ++ rest, cr := Function.update V.cr .xs (cstream A w E),
    er := D.reverse.drop (m * w) } with hS₉
  have h9 : RsaRuns body rg ι (rsaXferP rg .cM .ka .er (.c .xs)) S₈.get S₉.get
      (6 * (m * w) + 4) :=
    ((rsa_xfer (body := body) (ι := ι) hrg hdisj (a := .cM) (sp := .ka) (src := .er)
      (dst := .c .xs) (by simp) _ (by simp [hS₈, hka]) (by simp [hS₈, hcM, hDl, hmw])).congr (by
        rw [RsaV.upd_er, RsaV.upd_c]
        congr 1
        ext1
        · funext x; cases x <;> simp [hS₉, hS₈, hcM, ← hEs]
        all_goals simp [hS₉, hS₈, hcM])).mono (by simp [hS₈, hcM])
  -- 10. clear `er`
  set S₁₀ : RsaV X A := { V with
    ln := Z' ++ rest, cr := Function.update V.cr .xs (cstream A w E) } with hS₁₀
  have h10 : RsaRuns body rg ι (uclear (rg .er)) S₉.get S₁₀.get (2 * ((s - m) * w) + 2) :=
    ((rsa_uclear (body := body) (ι := ι) hrg .er _).congr (by
      rw [RsaV.upd_er]
      congr 1
      ext1 <;> simp [hS₁₀, hS₉, her])).mono (by simp [hS₉, hDl, Nat.sub_mul])
  -- 11. drop the padding
  set V' : RsaV X A := { V with ln := rest } with hV'
  have h11 : RsaRuns body rg ι (usub (rg .cP) (rg .ln) (rg .kx)) S₁₀.get
      (rsaRV V' w L E tab 0 0 0 V.ob).get (4 * ((t - s) * w) + 4) :=
    ((rsa_usub (body := body) (ι := ι) hrg (a := .cP) (b := .ln) (t := .kx) (by simp) (by simp)
      (by simp) _ (by simp [hS₁₀, hkx])).congr (by
        rw [RsaV.upd_ln]
        congr 1
        ext1
        · funext x; cases x <;> simp [rsaRV, rsaCr, hS₁₀, hV', hxsv, hys, hysv, htab]
        all_goals simp [rsaRV, hS₁₀, hV', hcP, ← hZl, hrr])).mono (by simp [hS₁₀, hcP])
  -- 12. the outputs
  have h12 := rsa_rows (body := body) hrg hdisj hι hT hQ hA hw hq V' hr hacc hatm hkW hkx hsm hpz
    hsm2 hbx hby hbz hkT hcW ht hst hs0 hbS hcT E hEl wt
    (fun x hx => by
      rw [hE, rsaExt, List.mem_append, List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact hFN x (List.mem_of_mem_drop hx)
      · exact hFN x hx
      · exact hFN x (List.mem_of_mem_take hx)) hFT (q := q)
  -- 13. restore the table
  set S₁₃ : RsaV X A := { V' with
    cr := Function.update V.cr .xs (cstream A w (E.drop s))
    ob := (cstream A w (rsaOut q s t (2 * m + 1) E wt)).reverse ++ V.ob } with hS₁₃
  have htabl : tab.length = t * (2 * m + 1) := length_rsaTabL _ _ _
  have h13 : RsaRuns body rg ι (moveR (rg (.c .ysv)) (rg (.c .ys)) id)
      (rsaRV V' w L E tab s (t * (2 * m + 1)) 0
        ((cstream A w (rsaOut q s t (2 * m + 1) E wt)).reverse ++ V'.ob)).get S₁₃.get
      (2 * (t * (2 * m + 1) * w) + 2) :=
    ((rsa_moveR (body := body) (ι := ι) hrg (a := .c .ysv) (b := .c .ys) (by simp) _).congr (by
      rw [RsaV.upd_c, RsaV.upd_c]
      congr 1
      ext1
      · funext x
        cases x <;> simp [rsaRV, rsaCr, hS₁₃, hV', hys, hysv, hxsv, ← htabl]
      all_goals simp [rsaRV, hS₁₃, hV', hrr])).mono
      (by simp [rsaRV, rsaCr, hV', htabl])
  -- 14. clear `xs`
  have h14 : RsaRuns body rg ι (uclear (rg (.c .xs))) S₁₃.get
      { V with
        ln := rest
        ob := (cstream A w (rsaOut q s t (2 * m + 1) (rsaExt m N) wt)).reverse ++ V.ob }.get
      (2 * (2 * m * w) + 2) :=
    ((rsa_uclear (body := body) (ι := ι) hrg (.c .xs) _).congr (by
      rw [RsaV.upd_c]
      congr 1
      ext1
      · funext x; cases x <;> simp [hS₁₃, hV', hxs]
      all_goals simp [hS₁₃, hV', hE])).mono (by simp [hS₁₃, hEl])
  refine ((h1.seq hdisj (h2.seq hdisj (h3.seq hdisj (h4.seq hdisj (h5.seq hdisj (h6.seq hdisj
    (h7.seq hdisj (h8.seq hdisj (h9.seq hdisj (h10.seq hdisj (h11.seq hdisj (h12.seq hdisj
    (h13.seq hdisj h14))))))))))))).mono ?_)
  simp only [rsaLineCost]
  omega

end Term

end

end IntegerMultBounds.MathlibTM2.Fast.ResampA
