module

public import IntegerMultBounds.MathlibTM2.Fast.ChirpBox
public import IntegerMultBounds.MathlibTM2.Fast.ResampARegs
public import IntegerMultBounds.MathlibTM2.Layer.Shift
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import IntegerMultBounds.MathlibTM2.Fast.CMulStream
public import IntegerMultBounds.MathlibTM2.Mult.SourceErr
public import IntegerMultBounds.ExactRecovery

/-!
# Entrywise stages on box streams

Box arrays are stored as in `Fast/ChirpStage`: the numerators at scale `2^q` of a function `f`
on `∏ ZMod (t i)`, in address order (`cstNumBox q t f`), each as `coeffSyms A w (red w N)`. The
stages below act entry by entry; each is a register-file contract `ResampA.RsaRuns` on a
register family `R` with an injective layout `rg : R → Fin T` disjoint from the 64
Schönhage–Strassen registers `ι j`.

**Pointwise product** (`cst_point_runs`). `cmulStream` through an injective map `c : CR → R` of
the complex-product registers: from `xs`, `ys` holding the numerator boxes of `f`, `h` (grid
values at scale `2^q`, numerators fitting `w` bits), `out` gains the numerator box of
`rdV q (f * h)` (`= rdV q fun k => f k * h k`, the argument of `G'` in
`ExactRecovery.computed`); `xs`, `ys` are restored. `(∏ t_i) (cmulCost T w + 6 w + 2) + 8`
steps.

**Chirp products** (`cst_chirpMul_runs`). The same program with the conjugate kernel on `xs`:
`out` gains the numerator box of `cstChirpProd t q a' x = k ↦ rhoC q (conj (a' k) · x k)`;
`cst_bluesteinApproxD_eq`: `bluesteinApproxD q a' M' u` is the chirp product of `M' a'`
applied to the chirp product of `u`. The conjugate kernel comes from `cst_conjKeep_runs`, run
once: `bcopy` of the kernel register, the conjugation automaton (`conj_exec`), and `moveR` back
to forward order; the kernel register is kept. `cstChirpMul` combines the conjugation onto
`xs`, the products and the clearing of `xs` (`cst_chirpMulKeep_runs`,
`(∏ t_i) (cmulCost T w + 21 w + 8) + 20` steps).

**Conjugation** (`cst_conj_runs`). The Gaussian automaton of `conj_exec` on one register: the
input stream of `l` is consumed and the output register gains the stream of `l.map star`
reversed; `|l| (5 w + 6) + 2` steps. On boxes `numer q (conj z) = star (numer q z)`
(`cstNumBox_conj`), for every `f`: the numerator box of `conj ∘ f`, as used by
`SourceErr.oppApprox` (`cst_conj_box`; `cst_conjKeep_box` with the source kept,
`|l| (13 w + 6) + 10` steps).

**Exact scale by `2^γ`** (`cst_scale_runs`). `shiftInto` (`Layer/Shift`): the stream of `l` on
`src` becomes the stream of `l.map (2^γ * ·)` on `out` (in place when `out = src`), in
`|l| (6 w + 4 γ + 14) + 4` steps; on boxes of grid values it is the numerator box of
`(2 : ℂ)^γ • v` (`cstNumBox_scale`, `cst_scale_box`), the last step of
`SourceErr.sourceApprox`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.ChirpSt

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ResampA


noncomputable section

/-! ### Box semantics -/

section Semantics

variable {d : ℕ} (t : Fin d → ℕ)

/-- The address cast `x ↦ (x_i : ZMod (t i))`. -/
abbrev cstCast (x : (i : Fin d) → Fin (t i)) : (i : Fin d) → ZMod (t i) :=
  fun i => ((x i : ℕ) : ZMod (t i))

theorem cstNumBox_eq (q : ℕ) (f : ((i : Fin d) → ZMod (t i)) → ℂ) :
    cstNumBox q t f = rsaBox d t fun x => numer q (f (cstCast t x)) := rfl

/-- The numerator box of a rounded pointwise product. -/
theorem cstNumBox_rdV [∀ i, NeZero (t i)] {q : ℕ} (f h : ((i : Fin d) → ZMod (t i)) → ℂ)
    (hf : ∀ x, IsFixed q (f (cstCast t x))) (hh : ∀ x, IsFixed q (h (cstCast t x))) :
    List.zipWith (fun x y => tdivN q (x * y)) (cstNumBox q t f) (cstNumBox q t h) =
      cstNumBox q t (rdV q (f * h)) := by
  rw [cstNumBox_eq, cstNumBox_eq, cstNumBox_eq, cst_zipWith_rsaBox]
  congr 1
  funext x
  simp only [rdV, Pi.mul_apply]
  rw [cst_numer_rhoC_mul (hf x) (hh x)]

/-- The numerator box of the conjugate. -/
theorem cstNumBox_conj (q : ℕ) (f : ((i : Fin d) → ZMod (t i)) → ℂ) :
    (cstNumBox q t f).map star = cstNumBox q t fun k => starRingEnd ℂ (f k) := by
  rw [cstNumBox_eq, cstNumBox_eq, ← rsaBox_map]
  congr 1
  funext x
  rw [cst_numer_conj]

/-- The numerator box of `2^γ • v` for grid values. -/
theorem cstNumBox_scale {q : ℕ} (γ : ℕ) (v : ((i : Fin d) → ZMod (t i)) → ℂ)
    (hv : ∀ x, IsFixed q (v (cstCast t x))) :
    (cstNumBox q t v).map (fun N => 2 ^ γ * N) = cstNumBox q t ((2 : ℂ) ^ γ • v) := by
  rw [cstNumBox_eq, cstNumBox_eq, ← rsaBox_map]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [cst_numer_two_pow_mul (hv x)]

theorem cst_isFixed_conj {q : ℕ} {z : ℂ} (hz : IsFixed q z) :
    IsFixed q (starRingEnd ℂ z) := by
  rw [← cst_grid_numer hz, cst_conj_grid]
  exact cst_isFixed_grid q _

/-- The chirp product `k ↦ Q_q (conj (a' k) · x k)` of `bluesteinApproxD`. -/
def cstChirpProd (q : ℕ) (a' x : ((i : Fin d) → ZMod (t i)) → ℂ) :
    ((i : Fin d) → ZMod (t i)) → ℂ :=
  fun k => rhoC q (starRingEnd ℂ (a' k) * x k)

/-- The computed chirp transform is the outer chirp product of `M'` applied to the inner one. -/
theorem cst_bluesteinApproxD_eq (q : ℕ) (a' : ((i : Fin d) → ZMod (t i)) → ℂ)
    (M' : (((i : Fin d) → ZMod (t i)) → ℂ) → (((i : Fin d) → ZMod (t i)) → ℂ) →
      (((i : Fin d) → ZMod (t i)) → ℂ)) (u : ((i : Fin d) → ZMod (t i)) → ℂ) :
    bluesteinApproxD q a' M' u = cstChirpProd t q a' (M' a' (cstChirpProd t q a' u)) := rfl

theorem cstChirpProd_eq_rdV [∀ i, NeZero (t i)] (q : ℕ)
    (a' x : ((i : Fin d) → ZMod (t i)) → ℂ) :
    cstChirpProd t q a' x = rdV q ((fun k => starRingEnd ℂ (a' k)) * x) := rfl

end Semantics

lemma cst_fits_star {w : ℕ} {N : GaussianInt} (h : Fits w N) : Fits w (star N) := by
  obtain ⟨a, b⟩ := N
  rw [Zsqrtd.star_mk]
  exact ⟨h.1, by simpa using h.2⟩

/-! ### Streams -/

lemma cst_cstream_eq_red (A w : ℕ) (l : List GaussianInt) :
    cstream A w l = (l.map (red w)).flatMap (coeffSyms A w) := by
  rw [cstream, List.flatMap_map]

lemma cst_two_pow_gauss (γ : ℕ) : ((2 : GaussianInt) ^ γ) = ⟨2 ^ γ, 0⟩ := by
  induction γ with
  | zero => rfl
  | succ γ ih =>
      rw [pow_succ, ih]
      ext <;> simp [pow_succ]

lemma cst_red_two_pow_mul (w γ : ℕ) (N : GaussianInt) :
    red w (2 ^ γ * N) =
      ((2 ^ γ : ZMod (2 ^ w)) * (red w N).1, (2 ^ γ : ZMod (2 ^ w)) * (red w N).2) := by
  rw [cst_two_pow_gauss, red_mulG]
  simp [GR.mulG]

lemma cst_red_star_map (w : ℕ) (l : List GaussianInt) :
    (l.map (red w)).map GR.conj = (l.map star).map (red w) := by
  simp only [List.map_map]
  congr 1
  funext N
  simp [red_star]

/-! ### Contracts -/

section Contracts

variable {T Q A : ℕ} {U P R : Type} [DecidableEq R] {body : P → Pr P T Q A U} {rg : R → Fin T}
  {ι : Fin 64 → Fin T}

variable (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
include hrg hdisj

/-- **The pointwise product of two box streams.** `xs` and `ys` (through `c`) hold the numerator
boxes at scale `2^q` of grid functions `f` and `h` whose numerators fit `w` bits; `out` gains the
numerator box of `rdV q (f * h)`, every other register as before, within
`(∏ t_i) (cmulCost T w + 6 w + 2) + 8` steps. -/
theorem cst_point_runs (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (hA : 96 ≤ A) {c : CR → R} (hc : Function.Injective c) {w q : ℕ} (hw : 1 ≤ w)
    (hq : q ≤ w) {d : ℕ} (t : Fin d → ℕ) [∀ i, NeZero (t i)]
    (f h : ((i : Fin d) → ZMod (t i)) → ℂ)
    (hf : ∀ x, IsFixed q (f (cstCast t x))) (hh : ∀ x, IsFixed q (h (cstCast t x)))
    (hfw : ∀ x, Fits w (numer q (f (cstCast t x))))
    (hhw : ∀ x, Fits w (numer q (h (cstCast t x))))
    (ρ : R → List (Fin (A + 4))) (hr : Ready (fun x => ρ (c x)) w q)
    (hX : ρ (c .xs) = cstream A w (cstNumBox q t f))
    (hY : ρ (c .ys) = cstream A w (cstNumBox q t h)) (hxsv : ρ (c .xsv) = [])
    (hysv : ρ (c .ysv) = []) (hacc : ρ (c .acc) = []) :
    RsaRuns body rg ι (cmulStream (fun x => rg (c x)) (cmulOne ι hι hT hQ (fun x => rg (c x)))) ρ
      (Function.update ρ (c .out) (cstream A w (cstNumBox q t (rdV q (f * h))) ++ ρ (c .out)))
      ((∏ i, t i) * (cmulCost T w + 6 * w + 2) + 8) := by
  have hcr : Function.Injective (fun x => rg (c x)) := fun a b e => hc (hrg e)
  have hdisj' : ∀ r j, (fun x => rg (c x)) r ≠ ι j := fun r j => hdisj _ j
  have mem_box : ∀ (g : ((i : Fin d) → ZMod (t i)) → ℂ),
      (∀ x, Fits w (numer q (g (cstCast t x)))) → ∀ N ∈ cstNumBox q t g, Fits w N := by
    intro g hg N hN
    obtain ⟨x, rfl⟩ := cst_mem_numBox hN
    exact hg x
  have H := RsaRuns.of_c hrg hc
    (cmulStream_runs (body := body) (cr := fun x => rg (c x)) hcr hdisj' hι hT hQ hA
      (ρ := fun x => ρ (c x)) hr hw hq (cstNumBox q t f) (cstNumBox q t h)
      (by rw [cst_length_numBox, cst_length_numBox]) (mem_box f hfw) (mem_box h hhw) hX hY hxsv
      hysv hacc) ρ (fun _ => rfl)
  rw [cst_extend_update _ hc, cstNumBox_rdV t f h hf hh, cst_length_numBox] at H
  exact H

/-- **The chirp products.** `xs` holds the numerator box of the conjugate kernel
`k ↦ conj (a' k)`, `ys` that of `x` (grid values at scale `2^q`, numerators fitting `w` bits);
`out` gains the numerator box of `cstChirpProd t q a' x = k ↦ rhoC q (conj (a' k) · x k)`. -/
theorem cst_chirpMul_runs (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (hA : 96 ≤ A) {c : CR → R} (hc : Function.Injective c) {w q : ℕ} (hw : 1 ≤ w)
    (hq : q ≤ w) {d : ℕ} (t : Fin d → ℕ) [∀ i, NeZero (t i)]
    (a' x : ((i : Fin d) → ZMod (t i)) → ℂ)
    (ha : ∀ k, IsFixed q (a' (cstCast t k))) (hx : ∀ k, IsFixed q (x (cstCast t k)))
    (haw : ∀ k, Fits w (numer q (a' (cstCast t k))))
    (hxw : ∀ k, Fits w (numer q (x (cstCast t k))))
    (ρ : R → List (Fin (A + 4))) (hr : Ready (fun x => ρ (c x)) w q)
    (hX : ρ (c .xs) = cstream A w (cstNumBox q t fun k => starRingEnd ℂ (a' k)))
    (hY : ρ (c .ys) = cstream A w (cstNumBox q t x)) (hxsv : ρ (c .xsv) = [])
    (hysv : ρ (c .ysv) = []) (hacc : ρ (c .acc) = []) :
    RsaRuns body rg ι (cmulStream (fun x => rg (c x)) (cmulOne ι hι hT hQ (fun x => rg (c x)))) ρ
      (Function.update ρ (c .out) (cstream A w (cstNumBox q t (cstChirpProd t q a' x)) ++
        ρ (c .out)))
      ((∏ i, t i) * (cmulCost T w + 6 * w + 2) + 8) := by
  rw [cstChirpProd_eq_rdV]
  exact cst_point_runs hrg hdisj hι hT hQ hA hc hw hq t _ x (fun k => cst_isFixed_conj (ha k)) hx
    (fun k => by rw [cst_numer_conj]; exact cst_fits_star (haw k)) hxw ρ hr hX hY hxsv hysv hacc

omit hdisj in
/-- **Conjugation of a stream.** The conjugation automaton of `conj_exec` consumes the stream of
`l` on `src` and pushes the stream of `l.map star` reversed onto `out`; the counter `ctr` holds
`w` symbols and `tmp` is empty (both kept); the automaton state lives in the scan slot of `st`. -/
theorem cst_conj_runs {src out st ctr tmp : R} (hd : [src, out, ctr, tmp].Nodup) (hst : src ≠ st)
    (hA : 5 ≤ A) {w : ℕ} (hw : 1 ≤ w) (ρ : R → List (Fin (A + 4))) (l : List GaussianInt)
    (hsrc : ρ src = cstream A w l) (hctr : (ρ ctr).length = w) (htmp : ρ tmp = []) :
    RsaRuns body rg ι
      (autoWords ![rg src] ![rg out] (rg st) (rg ctr) (rg tmp) (gaussAuto A ![![(0, -1)]] 1 true))
      ρ (Function.update (Function.update ρ src []) out
        ((cstream A w (l.map star)).reverse ++ ρ out))
      (l.length * (5 * w + 6) + 2) := by
  have hd' := hd
  regs_ne hd'
  have hL : AutoLayout ![rg src] ![rg out] (rg st) (rg ctr) (rg tmp) := by
    refine ⟨fun i j _ => Subsingleton.elim i j, fun i j _ => Subsingleton.elim i j, ?_, ?_, ?_,
      ?_, ?_, hrg.ne ‹ctr ≠ tmp›, ?_⟩
    · intro i j; fin_cases i; fin_cases j; exact hrg.ne ‹src ≠ out›
    · intro i; fin_cases i; exact hrg.ne ‹src ≠ ctr›
    · intro i; fin_cases i; exact hrg.ne ‹src ≠ tmp›
    · intro j; fin_cases j; exact hrg.ne ‹out ≠ ctr›
    · intro j; fin_cases j; exact hrg.ne ‹out ≠ tmp›
    · intro i; fin_cases i; exact hrg.ne hst
  intro v S _ hS
  obtain ⟨v', m, S', hu, hm, he, hi, ho, hl, hins, houts, hoth⟩ :=
    conj_exec body hL (by omega) hw (ctrs := S.R (rg ctr)) (by rw [hS, hctr]) (l.map (red w)) v S
      rfl (by rw [hS, htmp])
      (by simp only [Matrix.cons_val_fin_one]; rw [hS, hsrc, cst_cstream_eq_red])
  refine ⟨v', S', m, hu, by simpa using hm, he, fun r => ?_, hi, ho, hl, fun k hk => ?_⟩
  · simp only [Matrix.cons_val_fin_one] at hins houts hoth
    by_cases h1 : r = out
    · subst h1
      rw [houts, Function.update_self, cst_red_star_map, ← cst_cstream_eq_red, hS]
    · rw [Function.update_of_ne h1]
      by_cases h2 : r = src
      · subst h2; rw [Function.update_self, hins]
      · rw [Function.update_of_ne h2, ← hS]
        exact hoth _ (hrg.ne h2) (hrg.ne h1)
  · simp only [Matrix.cons_val_fin_one] at hoth
    exact hoth k (fun h => hk src h.symm) (fun h => hk out h.symm)

variable (rg) in
/-- The conjugate copy: `src` copied onto `tA`, conjugated onto `tB` (reversed) and moved onto
`dst` in forward order; `src` is kept. -/
def cstConjKeep (src dst tA tB t1 t2 st ctr tmp : R) : Pr P T Q A U :=
  .seq (bcopy (rg src) (rg tA) (rg t1) (rg t2))
  (.seq (autoWords ![rg tA] ![rg tB] (rg st) (rg ctr) (rg tmp) (gaussAuto A ![![(0, -1)]] 1 true))
    (moveR (rg tB) (rg dst) id))

/-- **The conjugate stream, source kept.** `dst` gains the stream of `l.map star` (forward
order), every other register ends as it started, within `|l| (13 w + 6) + 10` steps. -/
theorem cst_conjKeep_runs {src dst tA tB t1 t2 st ctr tmp : R}
    (hd : [src, dst, tA, tB, t1, t2, ctr, tmp].Nodup) (hst : tA ≠ st) (hA : 5 ≤ A) {w : ℕ}
    (hw : 1 ≤ w) (ρ : R → List (Fin (A + 4))) (l : List GaussianInt)
    (hsrc : ρ src = cstream A w l) (htA : ρ tA = []) (htB : ρ tB = []) (ht1 : ρ t1 = [])
    (ht2 : ρ t2 = []) (hctr : (ρ ctr).length = w) (htmp : ρ tmp = []) :
    RsaRuns body rg ι (cstConjKeep rg src dst tA tB t1 t2 st ctr tmp) ρ
      (Function.update ρ dst (cstream A w (l.map star) ++ ρ dst))
      (l.length * (13 * w + 6) + 10) := by
  have hd' := hd
  regs_ne hd'
  have h1 := rsa_bcopy (body := body) (ι := ι) hrg (a := src) (c := tA) (t₁ := t1) (t₂ := t2)
    (by regs_nodup) ρ ht1 ht2
  rw [hsrc, htA, List.append_nil] at h1
  set ρ₁ := Function.update ρ tA (cstream A w l) with hρ₁
  have h2 := cst_conj_runs (body := body) (ι := ι) hrg (src := tA) (out := tB) (st := st)
    (ctr := ctr) (tmp := tmp) (by regs_nodup) hst hA hw ρ₁ l (by simp [hρ₁])
    (by rw [hρ₁, Function.update_of_ne (Ne.symm ‹tA ≠ ctr›)]; exact hctr)
    (by rw [hρ₁, Function.update_of_ne (Ne.symm ‹tA ≠ tmp›)]; exact htmp)
  have h3 := rsa_moveR (body := body) (ι := ι) hrg (a := tB) (b := dst) (Ne.symm ‹dst ≠ tB›)
    (Function.update (Function.update ρ₁ tA []) tB
      ((cstream A w (l.map star)).reverse ++ ρ₁ tB))
  refine ((RsaRuns.seq hdisj h1 (RsaRuns.seq hdisj h2 h3)).congr ?_).mono ?_
  · funext k
    simp only [hρ₁]
    cst_upd
  · have e1 : (Function.update (Function.update ρ₁ tA []) tB
        ((cstream A w (l.map star)).reverse ++ ρ₁ tB) tB).length = l.length * w := by
      simp only [hρ₁]
      cst_upd
    rw [e1, length_cstream]
    nlinarith

omit hdisj in
/-- **The exact scale by `2^γ`.** `shiftInto` turns the stream of `l` on `src` into the stream
of `l.map (2^γ * ·)` on `out` (on top of its contents unless `out = src`); `src` ends empty
unless it is `out`, `dst` is an empty spare, `cS` and `cR` hold `γ` and `w - γ` symbols, `tS`,
`tR` are empty; every other register is kept. Exactly `|l| (6 w + 4 γ + 14) + 4` steps. -/
theorem cst_scale_runs {src dst out cS cR tS tR : R} (hreg : [src, dst, cS, cR, tS, tR].Nodup)
    (hout : out ≠ dst) {w γ : ℕ} (hw : 1 ≤ w) (hγ : γ ≤ w)
    (ρ : R → List (Fin (A + 4))) (l : List GaussianInt) (hsrc : ρ src = cstream A w l)
    (hcS : (ρ cS).length = γ) (hcR : (ρ cR).length = w - γ) (htS : ρ tS = [])
    (htR : ρ tR = []) (hdst : ρ dst = []) :
    RsaRuns body rg ι
      (shiftInto (rg src) (rg dst) (rg out) (rg cS) (rg cR) (rg tS) (rg tR) (pairSym A false false))
      ρ (Function.update (Function.update ρ src []) out
        (cstream A w (l.map fun N => 2 ^ γ * N) ++ if out = src then [] else ρ out))
      (l.length * (6 * w + 4 * γ + 14) + 4) := by
  refine RsaRuns.of_raw fun v S _ hS => ?_
  obtain ⟨v', R', hu, -, he, hout', hsrc', hoth⟩ := shiftInto_exec body (rg src) (rg dst)
    (rg out) (rg cS) (rg cR) (rg tS) (rg tR) (hreg.map hrg) (hrg.ne hout) hw hγ (l.map (red w))
    v S (by rw [hS, hsrc, cst_cstream_eq_red]) (by rw [hS, hcS]) (by rw [hS, hcR])
    (by rw [hS, htS]) (by rw [hS, htR]) (by rw [hS, hdst])
  have hX : (List.map (fun z => ((2 : ZMod (2 ^ w)) ^ γ * z.1, (2 : ZMod (2 ^ w)) ^ γ * z.2))
      (l.map (red w))).flatMap (coeffSyms A w) = cstream A w (l.map fun N => 2 ^ γ * N) := by
    rw [cst_cstream_eq_red, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro N _
    simp only [Function.comp_apply]
    rw [cst_red_two_pow_mul]
  refine ⟨v', R', _, hu, by rw [List.length_map], he, fun r => ?_, fun k hk => ?_⟩
  · by_cases h1 : r = out
    · subst h1
      rw [hout', hX, Function.update_self, hS]
      simp only [hrg.eq_iff]
    · rw [Function.update_of_ne h1]
      by_cases h2 : r = src
      · subst h2
        rw [Function.update_self, hsrc' (fun h => h1 (hrg h).symm)]
      · rw [Function.update_of_ne h2, ← hS]
        exact hoth _ (hrg.ne h2) (hrg.ne h1)
  · exact hoth k (fun h => hk src h.symm) (fun h => hk out h.symm)

/-! ### Box forms -/

omit hdisj in
/-- `cst_conj_runs` on a numerator box: `out` gains the numerator box of `k ↦ conj (z k)`
reversed. -/
theorem cst_conj_box {src out st ctr tmp : R} (hd : [src, out, ctr, tmp].Nodup) (hst : src ≠ st)
    (hA : 5 ≤ A) {w q d : ℕ} (hw : 1 ≤ w) (t : Fin d → ℕ)
    (z : ((i : Fin d) → ZMod (t i)) → ℂ)
    (ρ : R → List (Fin (A + 4))) (hsrc : ρ src = cstream A w (cstNumBox q t z))
    (hctr : (ρ ctr).length = w) (htmp : ρ tmp = []) :
    RsaRuns body rg ι
      (autoWords ![rg src] ![rg out] (rg st) (rg ctr) (rg tmp) (gaussAuto A ![![(0, -1)]] 1 true))
      ρ (Function.update (Function.update ρ src []) out
        ((cstream A w (cstNumBox q t fun k => starRingEnd ℂ (z k))).reverse ++ ρ out))
      ((∏ i, t i) * (5 * w + 6) + 2) := by
  have h := cst_conj_runs (body := body) (ι := ι) hrg hd hst hA hw ρ _ hsrc hctr htmp
  rwa [cstNumBox_conj, cst_length_numBox] at h

/-- `cst_conjKeep_runs` on a numerator box: `dst` gains the numerator box of `k ↦ conj (a' k)`;
the source is kept. -/
theorem cst_conjKeep_box {src dst tA tB t1 t2 st ctr tmp : R}
    (hd : [src, dst, tA, tB, t1, t2, ctr, tmp].Nodup) (hst : tA ≠ st) (hA : 5 ≤ A) {w q d : ℕ}
    (hw : 1 ≤ w) (t : Fin d → ℕ) (a' : ((i : Fin d) → ZMod (t i)) → ℂ)
    (ρ : R → List (Fin (A + 4))) (hsrc : ρ src = cstream A w (cstNumBox q t a'))
    (htA : ρ tA = []) (htB : ρ tB = []) (ht1 : ρ t1 = []) (ht2 : ρ t2 = [])
    (hctr : (ρ ctr).length = w) (htmp : ρ tmp = []) :
    RsaRuns body rg ι (cstConjKeep rg src dst tA tB t1 t2 st ctr tmp) ρ
      (Function.update ρ dst
        (cstream A w (cstNumBox q t fun k => starRingEnd ℂ (a' k)) ++ ρ dst))
      ((∏ i, t i) * (13 * w + 6) + 10) := by
  have h := cst_conjKeep_runs (body := body) (ι := ι) hrg hdisj hd hst hA hw ρ _ hsrc htA htB
    ht1 ht2 hctr htmp
  rwa [cstNumBox_conj, cst_length_numBox] at h

omit hdisj in
/-- `cst_scale_runs` on a numerator box of grid values: `out` gains the numerator box of
`(2 : ℂ)^γ • v`. -/
theorem cst_scale_box {src dst out cS cR tS tR : R} (hreg : [src, dst, cS, cR, tS, tR].Nodup)
    (hout : out ≠ dst) {w γ q d : ℕ} (hw : 1 ≤ w) (hγ : γ ≤ w) (t : Fin d → ℕ)
    (v : ((i : Fin d) → ZMod (t i)) → ℂ) (hv : ∀ x, IsFixed q (v (cstCast t x)))
    (ρ : R → List (Fin (A + 4))) (hsrc : ρ src = cstream A w (cstNumBox q t v))
    (hcS : (ρ cS).length = γ) (hcR : (ρ cR).length = w - γ) (htS : ρ tS = [])
    (htR : ρ tR = []) (hdst : ρ dst = []) :
    RsaRuns body rg ι
      (shiftInto (rg src) (rg dst) (rg out) (rg cS) (rg cR) (rg tS) (rg tR) (pairSym A false false))
      ρ (Function.update (Function.update ρ src []) out
        (cstream A w (cstNumBox q t ((2 : ℂ) ^ γ • v)) ++ if out = src then [] else ρ out))
      ((∏ i, t i) * (6 * w + 4 * γ + 14) + 4) := by
  have h := cst_scale_runs (body := body) (ι := ι) hrg hreg hout hw hγ ρ _ hsrc hcS hcR
    htS htR hdst
  rwa [cstNumBox_scale t γ v hv, cst_length_numBox] at h

/-! ### The chirp product with the conjugation -/

variable (ι) in
/-- The chirp products against the kernel on `kr`: the conjugate kernel onto `xs`
(`cstConjKeep`), the products onto `out` (`cmulStream`), `xs` cleared. -/
def cstChirpMul (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (rg : R → Fin T) (c : CR → R) (kr tA tB t1 t2 : R) : Pr P T Q A U :=
  .seq (cstConjKeep rg kr (c .xs) tA tB t1 t2 (c .tmp) (c .wn) (c .tmp))
  (.seq (cmulStream (fun x => rg (c x)) (cmulOne ι hι hT hQ (fun x => rg (c x))))
    (uclear (rg (c .xs))))

/-- **The chirp products, kernel kept.** `kr` holds the numerator box of the kernel `a'`, `ys`
that of `x` (grid values at scale `2^q`, numerators fitting `w` bits), `xs` and the spares
`tA`, `tB`, `t1`, `t2` are empty; `out` gains the numerator box of
`cstChirpProd t q a' x = k ↦ rhoC q (conj (a' k) · x k)`, every other register ends as it
started, within `(∏ t_i) (cmulCost T w + 21 w + 8) + 20` steps. -/
theorem cst_chirpMulKeep_runs (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (hA : 96 ≤ A) {c : CR → R} (hc : Function.Injective c) {kr tA tB t1 t2 : R}
    (hd : [kr, tA, tB, t1, t2].Nodup)
    (hcx : ∀ x, c x ≠ kr ∧ c x ≠ tA ∧ c x ≠ tB ∧ c x ≠ t1 ∧ c x ≠ t2) {w q : ℕ}
    (hw : 1 ≤ w) (hq : q ≤ w) {d : ℕ} (t : Fin d → ℕ) [∀ i, NeZero (t i)]
    (a' x : ((i : Fin d) → ZMod (t i)) → ℂ)
    (ha : ∀ k, IsFixed q (a' (cstCast t k))) (hx : ∀ k, IsFixed q (x (cstCast t k)))
    (haw : ∀ k, Fits w (numer q (a' (cstCast t k))))
    (hxw : ∀ k, Fits w (numer q (x (cstCast t k))))
    (ρ : R → List (Fin (A + 4))) (hr : Ready (fun x => ρ (c x)) w q)
    (hK : ρ kr = cstream A w (cstNumBox q t a')) (hY : ρ (c .ys) = cstream A w (cstNumBox q t x))
    (hxs : ρ (c .xs) = []) (hxsv : ρ (c .xsv) = []) (hysv : ρ (c .ysv) = [])
    (hacc : ρ (c .acc) = []) (htA : ρ tA = []) (htB : ρ tB = []) (ht1 : ρ t1 = [])
    (ht2 : ρ t2 = []) :
    RsaRuns body rg ι (cstChirpMul ι hι hT hQ rg c kr tA tB t1 t2) ρ
      (Function.update ρ (c .out) (cstream A w (cstNumBox q t (cstChirpProd t q a' x)) ++
        ρ (c .out)))
      ((∏ i, t i) * (cmulCost T w + 21 * w + 8) + 20) := by
  have hd' := hd
  regs_ne hd'
  obtain ⟨a1, a2, a3, a4, a5⟩ := hcx .xs
  obtain ⟨b1, b2, b3, b4, b5⟩ := hcx .wn
  obtain ⟨c1, c2, c3, c4, c5⟩ := hcx .tmp
  have n1 : c .xs ≠ c .wn := hc.ne (by decide)
  have n2 : c .xs ≠ c .tmp := hc.ne (by decide)
  have n3 : c .wn ≠ c .tmp := hc.ne (by decide)
  have hn : [kr, c .xs, tA, tB, t1, t2, c .wn, c .tmp].Nodup := by regs_nodup
  have h1 := cst_conjKeep_box (body := body) (ι := ι) hrg hdisj (src := kr) (dst := c .xs)
    (tA := tA) (tB := tB) (t1 := t1) (t2 := t2) (st := c .tmp) (ctr := c .wn) (tmp := c .tmp) hn
    (Ne.symm c2)
    (by omega) hw t a' ρ hK htA htB ht1 ht2 hr.wn hr.tmp
  rw [hxs, List.append_nil] at h1
  set ρ₁ := Function.update ρ (c .xs)
    (cstream A w (cstNumBox q t fun k => starRingEnd ℂ (a' k))) with hρ₁
  have hr₁ : Ready (fun y => ρ₁ (c y)) w q :=
    cst_ready_of_eq hr (fun y h1 _ _ _ _ _ => by
      simp only [hρ₁]; rw [Function.update_of_ne (hc.ne h1)])
  have hne : ∀ y, y ≠ CR.xs → ρ₁ (c y) = ρ (c y) := fun y hy => by
    simp only [hρ₁]; rw [Function.update_of_ne (hc.ne hy)]
  have h2 := cst_chirpMul_runs (body := body) (ι := ι) hrg hdisj hι hT hQ hA hc hw hq t a' x ha
    hx haw hxw ρ₁ hr₁
    (by simp [hρ₁]) (by rw [hne _ (by decide)]; exact hY) (by rw [hne _ (by decide)]; exact hxsv)
    (by rw [hne _ (by decide)]; exact hysv) (by rw [hne _ (by decide)]; exact hacc)
  have h3 := rsa_uclear (body := body) (ι := ι) hrg (c .xs)
    (Function.update ρ₁ (c .out) (cstream A w (cstNumBox q t (cstChirpProd t q a' x)) ++
      ρ₁ (c .out)))
  refine ((RsaRuns.seq hdisj h1 (RsaRuns.seq hdisj h2 h3)).congr ?_).mono ?_
  · have n4 : c .xs ≠ c .out := hc.ne (by decide)
    funext k
    simp only [hρ₁, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · have e1 : (Function.update ρ₁ (c .out)
        (cstream A w (cstNumBox q t (cstChirpProd t q a' x)) ++ ρ₁ (c .out)) (c .xs)).length =
          (∏ i, t i) * w := by
      rw [Function.update_of_ne (hc.ne (by decide)), hρ₁, Function.update_self, length_cstream,
        cst_length_numBox]
    rw [e1]
    nlinarith

end Contracts

end

end IntegerMultBounds.MathlibTM2.Fast.ChirpSt
