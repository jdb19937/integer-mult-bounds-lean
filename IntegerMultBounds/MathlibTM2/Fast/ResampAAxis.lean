module

public import IntegerMultBounds.MathlibTM2.Fast.ResampALine
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# The numeric `Ã` along the innermost axis of a padded box

The box register `ln` holds the box array as a coefficient stream whose lines along the
innermost axis are contiguous: `lines.flatten`, every line `t` records long, of which the first
`s` are the line of the array and the rest padding. `rsaAxisP` runs the line machine
`rsaLineP` (`Fast/ResampALine`) while `ln` is nonempty, collecting the outputs on `ob`, and moves
them back onto `ln`.

* `RsaIdle V w q L s t m wt`: the register file between lines (complex-product registers ready
  for `w` bits and shift `q`, the table `rsaTabL t (2m + 1) wt` on `ys`, the counters `cS`, `cM`,
  `cP`, `cW`, `cT` at `s w`, `m w`, `(t - s) w`, `2m + 1`, `t` symbols, `rr = 0`, `bS = s` in `L`
  bits, scratch registers empty). It does not constrain `ln`, `ob` or the extra registers.
* `rsaLineMap q s t m wt line = rsaOut q s t (2m + 1) (rsaExt m (line.take s)) wt`: the `t`
  outputs of one padded line.
* `rsa_axis`: `ln = cstream (lines.flatten)` becomes `cstream (lines.flatMap (rsaLineMap …))`,
  every other register restored (`ob` empty before and after), within
  `|lines| (rsaLineCost … + 2) + 2 |lines| t w + 4` steps.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.ResampA

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast


noncomputable section

/-- The `t` outputs of one padded line: the window sums of its first `s` records, extended
cyclically by `m` records. -/
def rsaLineMap (q s t m : ℕ) (wt : ℕ → ℕ → GaussianInt) (line : List GaussianInt) :
    List GaussianInt :=
  rsaOut q s t (2 * m + 1) (rsaExt m (line.take s)) wt

lemma length_rsaLineMap (q s t m : ℕ) (wt : ℕ → ℕ → GaussianInt) (line : List GaussianInt) :
    (rsaLineMap q s t m wt line).length = t := length_rsaOut _ _ _ _ _ _

/-- The register file between lines of `Ã` on an axis with `s` source and `t = 2^L` target
records, window `2m + 1`, table weights `wt`, product shift `q` and coefficient width `w`. -/
structure RsaIdle {X : Type} {A : ℕ} (V : RsaV X A) (w q L s t m : ℕ)
    (wt : ℕ → ℕ → GaussianInt) : Prop where
  ready : Ready V.cr w q
  xs : V.cr .xs = []
  xsv : V.cr .xsv = []
  ys : V.cr .ys = cstream A w (rsaTabL t (2 * m + 1) wt)
  ysv : V.cr .ysv = []
  acc : V.cr .acc = []
  ea : V.ea = []
  eb : V.eb = []
  er : V.er = []
  ka : V.ka = []
  kb : V.kb = []
  kx : V.kx = []
  kW : V.kW = []
  kT : V.kT = []
  atm : V.atm = []
  sm : V.sm = []
  pz : V.pz = []
  sm2 : V.sm2 = []
  bxa : V.bxa = []
  bya : V.bya = []
  bza : V.bza = []
  cS : V.cS.length = s * w
  cM : V.cM.length = m * w
  cP : V.cP.length = (t - s) * w
  cW : V.cW.length = 2 * m + 1
  cT : V.cT.length = t
  rr : V.rr = binSyms L 0
  bS : V.bS = binSyms L s

lemma RsaIdle.with_ln_ob {X : Type} {A : ℕ} {V : RsaV X A} {w q L s t m : ℕ}
    {wt : ℕ → ℕ → GaussianInt} (h : RsaIdle V w q L s t m wt) (l o : List (Fin (A + 4))) :
    RsaIdle { V with ln := l, ob := o } w q L s t m wt :=
  ⟨h.ready, h.xs, h.xsv, h.ys, h.ysv, h.acc, h.ea, h.eb, h.er, h.ka, h.kb, h.kx, h.kW, h.kT,
    h.atm, h.sm, h.pz, h.sm2, h.bxa, h.bya, h.bza, h.cS, h.cM, h.cP, h.cW, h.cT, h.rr, h.bS⟩

section Programs

variable {T Q A : ℕ} {U P X : Type} (rg : RsaR X → Fin T) (ι : Fin 64 → Fin T)
  (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)

/-- `Ã` along the innermost axis: one line per iteration while `ln` is nonempty, then the
outputs back onto `ln`. -/
def rsaAxisP : Pr P T Q A U :=
  .seq (cwhileP (rg .ln) (rsaLineP rg ι hι hT hQ)) (moveR (rg .ob) (rg .ln) id)

end Programs

section Axis

variable {T Q A : ℕ} {U P X : Type} [DecidableEq X] {body : P → Pr P T Q A U}
  {rg : RsaR X → Fin T} {ι : Fin 64 → Fin T}

variable (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
include hrg hdisj

/-- `rsa_line` for a register file between lines. -/
theorem rsa_line_idle (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (hA : 96 ≤ A) {w q L s t m : ℕ} (hw : 1 ≤ w) (hq : q ≤ w) {wt : ℕ → ℕ → GaussianInt}
    (V : RsaV X A) (hI : RsaIdle V w q L s t m wt) (ht : t = 2 ^ L) (hst : s < t) (hms : m ≤ s)
    (hs0 : 0 < s) (hFT : ∀ y ∈ rsaTabL t (2 * m + 1) wt, Fits w y ∧ y.im = 0)
    (N Z : List GaussianInt) (rest : List (Fin (A + 4))) (hN : N.length = s)
    (hZ : Z.length = t - s) (hFN : ∀ x ∈ N, Fits w x)
    (hln : V.ln = cstream A w (N ++ Z) ++ rest) :
    RsaRuns body rg ι (rsaLineP rg ι hι hT hQ) V.get
      { V with
        ln := rest
        ob := (cstream A w (rsaOut q s t (2 * m + 1) (rsaExt m N) wt)).reverse ++ V.ob }.get
      (rsaLineCost T w s t m L) :=
  rsa_line hrg hdisj hι hT hQ hA hw hq V hI.ready ht hst hms hs0 wt N Z rest hN hZ hFN hFT hI.xs
    hI.xsv hI.ys hI.ysv hI.acc hln hI.ea hI.eb hI.er hI.ka hI.kb hI.kx hI.kW hI.kT hI.atm hI.sm
    hI.pz hI.sm2 hI.bxa hI.bya hI.bza hI.cS hI.cM hI.cP hI.cW hI.cT hI.rr hI.bS

/-- The step bound of `Ã` along the innermost axis of a box of `B` lines. -/
def rsaAxisCost (T w s t m L B : ℕ) : ℕ :=
  B * (rsaLineCost T w s t m L + 2) + 2 + (2 * (B * t * w) + 2)

/-- **`Ã` along the innermost axis.** `ln` holds the box stream `lines.flatten` (every line `t`
records, the first `s` of which fit `w` bits) and `ob` is empty; afterwards `ln` holds
`lines.flatMap (rsaLineMap q s t m wt)` and every other register is as before. -/
theorem rsa_axis (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w q L s t m : ℕ} (hw : 1 ≤ w) (hq : q ≤ w) {wt : ℕ → ℕ → GaussianInt} (V : RsaV X A)
    (hI : RsaIdle V w q L s t m wt) (ht : t = 2 ^ L) (hst : s < t) (hms : m ≤ s) (hs0 : 0 < s)
    (hFT : ∀ y ∈ rsaTabL t (2 * m + 1) wt, Fits w y ∧ y.im = 0)
    (lines : List (List GaussianInt)) (hlen : ∀ l ∈ lines, l.length = t)
    (hF : ∀ l ∈ lines, ∀ x ∈ l.take s, Fits w x)
    (hln : V.ln = cstream A w lines.flatten) (hob : V.ob = []) :
    RsaRuns body rg ι (rsaAxisP rg ι hι hT hQ) V.get
      { V with ln := cstream A w (lines.flatMap (rsaLineMap q s t m wt)) }.get
      (rsaAxisCost T w s t m L lines.length) := by
  set f := rsaLineMap q s t m wt with hf
  set st : List (List GaussianInt) → List (List GaussianInt) → RsaR X → List (Fin (A + 4)) :=
    fun l done => { V with
      ln := cstream A w l.flatten
      ob := (cstream A w (done.flatMap f)).reverse }.get with hst'
  have ht0 : 0 < t := by omega
  have hloop := rsa_cwhileP_runs (body := body) hdisj (α := List GaussianInt) .ln
    (rsaLineP rg ι hι hT hQ) (fun a => a.length = t ∧ ∀ x ∈ a.take s, Fits w x) st
    (rsaLineCost T w s t m L)
    (fun a rest done ⟨ha, haF⟩ => by
      have h := rsa_line_idle (body := body) hrg hdisj hι hT hQ hA hw hq
        { V with
          ln := cstream A w (a :: rest).flatten
          ob := (cstream A w (done.flatMap f)).reverse }
        (hI.with_ln_ob _ _) ht hst hms hs0 hFT (a.take s) (a.drop s)
        (cstream A w rest.flatten) (by simp [ha]; omega) (by simp [ha]) haF
        (by simp [cstream_append])
      refine h.congr ?_
      simp only [hst', List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, cstream_append, List.reverse_append]
      rfl)
    (fun a rest done ⟨ha, _⟩ => by
      have hw' : 0 < w := hw
      simp only [hst', RsaV.get_ln, List.flatten_cons, cstream_append]
      intro h
      have := congrArg List.length h
      simp [ha] at this
      omega)
    (fun done => by simp [hst'])
  have hlines : ∀ a ∈ lines, a.length = t ∧ ∀ x ∈ a.take s, Fits w x :=
    fun a ha => ⟨hlen a ha, hF a ha⟩
  have h1 := hloop lines [] hlines
  have e0 : st lines [] = V.get := by
    simp only [hst', List.flatMap_nil, cstream_nil, List.reverse_nil]
    rw [← hln, ← hob]
  rw [e0] at h1
  have h2 := rsa_moveR (body := body) (ι := ι) hrg (a := .ob) (b := .ln) (by simp)
    (st [] ([] ++ lines))
  refine ((h1.seq hdisj h2).congr ?_).mono ?_
  · rw [RsaV.upd_ob, RsaV.upd_ln]
    simp only [hst', List.nil_append, List.flatten_nil, cstream_nil]
    congr 1
    ext1 <;> simp [hob]
  · have hlenf : (lines.flatMap f).length = lines.length * t := by
      rw [List.length_flatMap]
      have : ∀ a ∈ lines, (f a).length = t := fun a _ => length_rsaLineMap _ _ _ _ _ _
      rw [List.map_congr_left this]
      simp [Nat.mul_comm]
    simp [hst', rsaAxisCost, hlenf]

end Axis

/-! ### Cost bounds -/

/-- One line costs at most `t ((2m + 1)(rmulCost T w + 13 w + 17) + 58 w + 8 L + 78)` steps:
`2m + 1` real fixed-point products per output, plus `O(w + L)` per output. -/
theorem rsaLineCost_le (T w s t m L : ℕ) (hst : s ≤ t) (hms : m ≤ s) (ht : 1 ≤ t) :
    rsaLineCost T w s t m L ≤
      t * ((2 * m + 1) * (rmulCost T w + 13 * w + 17) + 58 * w + 8 * L + 78) := by
  unfold rsaLineCost rsaRowsCost rsaRowCost rsaTermsCost rsaTermCost
  generalize rmulCost T w = R
  have h1 : s * w ≤ t * w := Nat.mul_le_mul_right _ hst
  have h2 : m * w ≤ t * w := Nat.mul_le_mul_right _ (hms.trans hst)
  have h3 : (s - m) * w ≤ t * w := Nat.mul_le_mul_right _ (by omega)
  have h4 : (t - s) * w ≤ t * w := Nat.mul_le_mul_right _ (by omega)
  have h5 : 48 ≤ 48 * t := by omega
  have e : t * (2 * m + 1) * w = t * ((2 * m + 1) * w) := by ring
  rw [e]
  nlinarith [h1, h2, h3, h4, h5]

/-- `Ã` along the innermost axis of a box of `n = B t` records costs at most
`n ((2m + 1)(rmulCost T w + 13 w + 17) + 60 w + 8 L + 80) + 4` steps. -/
theorem rsaAxisCost_le (T w s t m L B : ℕ) (hst : s ≤ t) (hms : m ≤ s) (ht : 1 ≤ t) :
    rsaAxisCost T w s t m L B ≤
      B * t * ((2 * m + 1) * (rmulCost T w + 13 * w + 17) + 60 * w + 8 * L + 80) + 4 := by
  unfold rsaAxisCost
  have h := rsaLineCost_le T w s t m L hst hms ht
  generalize rmulCost T w = R at h ⊢
  have h2 : 2 ≤ 2 * t := by omega
  nlinarith [Nat.mul_le_mul_left B h, Nat.mul_le_mul_left B h2]

end

end IntegerMultBounds.MathlibTM2.Fast.ResampA
