module

public import IntegerMultBounds.MathlibTM2.Fast.ChirpBox
public import IntegerMultBounds.MathlibTM2.Fast.ResampARegs
public import IntegerMultBounds.MathlibTM2.Mult.Pipeline
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star
public import IntegerMultBounds.MathlibTM2.Fast.CMulStream

/-!
# The chirp kernel box

The stage builds the stream of the numerators at scale `2^p` of the chirp kernel
`Chirp.chirpProd p g t s` on the padded box `∏_{i<d} [0, t_i)` (axis `0` most significant,
`ResampA.rsaBox`), from the axis tables: for axis `k`, the `t_k` numerators at scale `2^(p+g)` of
`axisPhase p g (t k) (s k) j`, `j = 0 … t_k - 1`.

**Repetition pass** (`cstRep`, generic in the register family). For every coefficient of `src`
(`w` pair symbols, counted by `wn`): the coefficient moves onto the buffer `cb`, `|cL|` copies of
the buffer go onto the accumulator `ra` (`bcopy`, counted by `scanP` on `cL`), the buffer is
cleared; at the end `ra` moves onto `dst`. `cst_rep_runs`: `dst` gains the stream of
`B.flatMap (List.replicate L)` (every coefficient repeated `L = |cL|` times), `src` ends empty,
within `cstRepCost w |B| L = |B| (8 w + 12 + L (6 w + 11)) + 2 |B| L w + 4` steps.

**Axis step** (`cstStep`). The box over the axes `0 … k` is on `out`, the table of axis `k + 1`
(`L` coefficients) on `ys`, `L` symbols on `cL`: the repetition pass from `out` to `xs` puts each
box entry `L` times on `xs` (the table is broadcast along the new least significant axis:
each table entry is taken once per box entry and cycled over the more significant axes by
`cmulTable`); `cmulTable` with shift `q = |pn|` writes `tdivN q (e · tab j)` onto `out` in
address order; `xs`, `ys`, `cL` are cleared (`cst_step_runs`).

**Stage** (`cstChirpBox prep`). `prep` is the caller's table loader: run with axis `k` pending, it
puts the table of axis `k` onto `ys` and `t_k` symbols onto `cL`, and changes only `ys`, `cL` and
the caller's registers `x j` (from `cfg k` to `cfg (k + 1)`). The stage loads axis `0` and copies
its table onto `out` (the box over axis `0`), runs `prep ; cstStep` for the axes `1 … d - 1`
(`scanP` on the axis counter `ax`, `d - 1` symbols), and then the disk rounding: `cmulTable`
through the second complex-product layout `cstDmap` (operand `xs ↦ out`, table `ys ↦ kc` holding
the constant `2^(p+2) - 1`, shift `pn ↦ pn2` holding `p + g + 2` symbols, result `out ↦ kr`)
writes `tdivN (p+g+2) (M · (2^(p+2) - 1))` for every box entry `M` onto `kr`.

**Results.**
* `cst_chirpBox_runs`: for tables `tab k j` and lengths `ts` (generic), `kr` gains the stream of
  `((cstAddrs ts).map (cstEnt (p+g) tab)).map fun M => tdivN (p+g+2) (M · cstDiskC p)`.
* `cst_chirpBox_pipeline`: with the chirp tables `cstAxTab p g t s` and `ts = List.ofFn t`,
  `kr` gains `cstream A w (cstNumBox p t (chirpProd p g t s))`, the numerator box of the chirp
  kernel at scale `2^p`; `cst_chirpBox_kernel` is the instance `Pipeline.chirpKernel n`.

**Registers.** `CsR X`: the complex-product registers `c x` (`x : CR`), the stage registers
`cb`, `ra`, `cL`, `cL'`, `s1`, `s2`, `ax`, `ax'`, `pn2`, `kc`, `kr`, and the caller's registers
`x j`. Before the stage (`CstBase`): the complex-product registers are ready for `w` and
`q = p + g` (`wn`, `pn`, `nn` hold `w`, `q`, `topN w` symbols; scratch empty), `xs`, `ys`, `xsv`,
`ysv`, `acc`, `out`, `cb`, `ra`, `cL`, `cL'`, `s1`, `s2`, `ax'` are empty, `pn2` holds `q + 2`
symbols, `kc` holds the coefficient `cstDiskC p`; `ax` holds `d - 1` symbols. Afterwards every
register is as before except `kr` (gains the kernel stream) and the caller's registers
(`cfg d`).

**Cost** (`cstChirpCost`, `cst_chirpCost_le`): at most `∑_{k<d} bp k + 4 d V cmulCost w`,
`V = ∏ t_k`, `bp k` the cost of loading axis `k`.

**Conditions.** `96 ≤ A`, `1 ≤ d`, `1 ≤ t_k`, `p + g + 2 ≤ w` and every table entry, partial
product and the constant fit `w` bits; for the chirp tables `p + g + 3 ≤ w` and
`d ≤ 2^(p+g)` suffice (`cst_fits_axTab`, `cst_fits_ent`, `cst_fits_diskC`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.ChirpSt

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ResampA
open IntegerMultBounds.Schoenhage.Schedule (topN)


noncomputable section

/-! ### Lists -/

lemma cst_cstream_replicate (A w : ℕ) (L : ℕ) (e : GaussianInt) :
    (cstream A w (List.replicate L e)).reverse =
      (List.replicate L (csyms A w e).reverse).flatten := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [List.replicate_succ, cstream_cons, List.reverse_append, ih, List.replicate_succ',
        List.flatten_append, List.flatten_singleton]

lemma cst_replicate_flatten_succ {α : Type} (L : ℕ) (x : List α) (y : List α) :
    x ++ ((List.replicate L x).flatten ++ y) = (List.replicate (L + 1) x).flatten ++ y := by
  rw [List.replicate_succ, List.flatten_cons, List.append_assoc]

lemma cst_zipWith_replicate {α β γ : Type} (f : α → β → γ) (a : α) :
    ∀ (l : List β), List.zipWith f (List.replicate l.length a) l = l.map (f a)
  | [] => rfl
  | b :: l => by
      simp only [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, List.map_cons]
      rw [cst_zipWith_replicate f a l]

lemma cst_tableOut_replicate (g : GaussianInt → GaussianInt → GaussianInt)
    (B ts : List GaussianInt) :
    tableOut g (B.map (List.replicate ts.length)) ts = B.flatMap fun e => ts.map (g e) := by
  simp only [tableOut, List.flatMap_map]
  exact List.flatMap_congr fun e _ => cst_zipWith_replicate g e ts

lemma cst_flatten_singleton {α : Type} : ∀ l : List α, (l.map fun e => [e]).flatten = l
  | [] => rfl
  | e :: l => by simp only [List.map_cons, List.flatten_cons, cst_flatten_singleton l]; rfl

lemma cst_tableOut_single (g : GaussianInt → GaussianInt → GaussianInt) (B : List GaussianInt)
    (C : GaussianInt) : tableOut g (B.map fun e => [e]) [C] = B.map fun e => g e C := by
  simp only [tableOut, List.flatMap_map, List.zipWith_cons_cons, List.zipWith_nil_right]
  induction B with
  | nil => rfl
  | cons e B ih => simp [ih]

/-! ### The repetition pass -/

section Rep

variable {T Q A : ℕ} {U P R : Type} [DecidableEq R] {body : P → Pr P T Q A U} {rg : R → Fin T}
  {ι : Fin 64 → Fin T}

/-- One coefficient of the repetition pass: `|wn|` symbols of `src` onto the buffer `cb`
(reversed), `|cL|` copies of the buffer onto `ra`, the buffer cleared. -/
def cstRepOne (rg : R → Fin T) (src wn cb ra cL cL' s1 s2 : R) : Pr P T Q A U :=
  .seq (scanP (rg wn) (rg s1) (.act (popPush (rg src) (rg cb))))
    (.seq (scanP (rg cL) (rg cL') (bcopy (rg cb) (rg ra) (rg s1) (rg s2))) (uclear (rg cb)))

/-- The repetition pass: every coefficient of `src` repeated `|cL|` times onto `dst`. -/
def cstRep (rg : R → Fin T) (src dst wn cb ra cL cL' s1 s2 : R) : Pr P T Q A U :=
  .seq (cwhileP (rg src) (cstRepOne rg src wn cb ra cL cL' s1 s2)) (moveR (rg ra) (rg dst) id)

/-- The step bound of `cstRep` on `n` coefficients of `w` symbols repeated `L` times. -/
def cstRepCost (w n L : ℕ) : ℕ := n * (8 * w + 12 + L * (6 * w + 11)) + 2 * (n * L * w) + 4

variable (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
include hrg hdisj

theorem cst_repOne_runs {src wn cb ra cL cL' s1 s2 : R}
    (hd : [src, wn, cb, ra, cL, cL', s1, s2].Nodup) {w : ℕ} (ρ : R → List (Fin (A + 4)))
    (e : GaussianInt) (rest : List (Fin (A + 4))) (hsrc : ρ src = csyms A w e ++ rest)
    (hwn : (ρ wn).length = w) (hcb : ρ cb = []) (hcL' : ρ cL' = []) (hs1 : ρ s1 = [])
    (hs2 : ρ s2 = []) :
    RsaRuns body rg ι (cstRepOne rg src wn cb ra cL cL' s1 s2) ρ
      (Function.update (Function.update ρ src rest) ra
        ((List.replicate (ρ cL).length (csyms A w e).reverse).flatten ++ ρ ra))
      (8 * w + 10 + (ρ cL).length * (6 * w + 11)) := by
  have hd' := hd
  regs_ne hd'
  have hlen : (csyms A w e).length = w := by simp [csyms]
  -- the transfer of one coefficient onto the buffer
  have h1 := rsa_xfer (body := body) hrg hdisj (a := wn) (sp := s1) (src := src) (dst := cb)
    (by regs_nodup) ρ hs1 (by rw [hwn, hsrc]; simp [hlen])
  rw [hwn, hsrc] at h1
  have htk : (csyms A w e ++ rest).take w = csyms A w e := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have hdr : (csyms A w e ++ rest).drop w = rest := by
    rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega),
      List.nil_append]
  rw [htk, hdr, hcb, List.append_nil] at h1
  set ρ₁ := Function.update (Function.update ρ src rest) cb (csyms A w e).reverse with hρ₁
  -- the copies
  set cs := ρ cL with hcs
  set Φ : ℕ → R → List (Fin (A + 4)) := fun j =>
    Function.update ρ₁ ra ((List.replicate j (csyms A w e).reverse).flatten ++ ρ ra) with hΦ
  have h2 := rsa_scanP_runs (body := body) (ι := ι) hrg hdisj ‹cL ≠ cL'› Φ (b := 6 * w + 6)
    cs (fun j _ => by
      have hb := rsa_bcopy (body := body) (ι := ι) hrg (a := cb) (c := ra) (t₁ := s1)
        (t₂ := s2) (by regs_nodup)
        (Function.update (Function.update (Φ j) cL (cs.drop (j + 1))) cL'
          (cs.take (j + 1)).reverse)
        (by simp only [hΦ, hρ₁]; cst_upd) (by simp only [hΦ, hρ₁]; cst_upd)
      have hcbv : Function.update (Function.update (Φ j) cL (cs.drop (j + 1))) cL'
          (cs.take (j + 1)).reverse cb = (csyms A w e).reverse := by
        simp only [hΦ, hρ₁]; cst_upd
      rw [hcbv] at hb
      refine (hb.congr ?_).mono (by simp [hlen])
      funext k
      simp only [Function.update_apply, hΦ, hρ₁]
      split_ifs <;> subst_vars <;> simp_all [cst_replicate_flatten_succ])
  have e₀ : Function.update (Function.update (Φ 0) cL cs) cL' [] = ρ₁ := by
    funext k
    simp only [Function.update_apply, hΦ, hρ₁]
    split_ifs <;> subst_vars <;> simp_all
  rw [e₀] at h2
  -- clearing the buffer
  have h3 := rsa_uclear (body := body) (ι := ι) hrg cb
    (Function.update (Function.update (Φ cs.length) cL cs) cL' [])
  have hcbl : (Function.update (Function.update (Φ cs.length) cL cs) cL' [] cb).length = w := by
    simp only [hΦ, hρ₁]; cst_upd
  rw [hcbl] at h3
  refine ((RsaRuns.seq hdisj h1 (RsaRuns.seq hdisj h2 h3)).congr ?_).mono ?_
  · funext k
    simp only [Function.update_apply, hΦ, hρ₁]
    split_ifs <;> subst_vars <;> simp_all
  · nlinarith

theorem cst_rep_runs {src dst wn cb ra cL cL' s1 s2 : R}
    (hd : [src, dst, wn, cb, ra, cL, cL', s1, s2].Nodup) {w : ℕ} (hw : 1 ≤ w)
    (ρ : R → List (Fin (A + 4))) (B : List GaussianInt) (hsrc : ρ src = cstream A w B)
    (hwn : (ρ wn).length = w) (hcb : ρ cb = []) (hra : ρ ra = []) (hcL' : ρ cL' = [])
    (hs1 : ρ s1 = []) (hs2 : ρ s2 = []) :
    RsaRuns body rg ι (cstRep rg src dst wn cb ra cL cL' s1 s2) ρ
      (Function.update (Function.update ρ src []) dst
        (cstream A w (B.flatMap (List.replicate (ρ cL).length)) ++ ρ dst))
      (cstRepCost w B.length (ρ cL).length) := by
  have hd' := hd
  regs_ne hd'
  set L := (ρ cL).length with hL
  set st : List GaussianInt → List GaussianInt → R → List (Fin (A + 4)) := fun l done =>
    Function.update (Function.update ρ src (cstream A w l)) ra
      (cstream A w (done.flatMap (List.replicate L))).reverse with hst
  have hloop := rsa_cwhileP_runs (body := body) (ι := ι) hdisj src
    (cstRepOne rg src wn cb ra cL cL' s1 s2) (fun _ => True) st
    (8 * w + 10 + L * (6 * w + 11))
    (fun a rest done _ => by
      have h := cst_repOne_runs (body := body) (ι := ι) hrg hdisj
        (src := src) (wn := wn) (cb := cb) (ra := ra) (cL := cL) (cL' := cL') (s1 := s1)
        (s2 := s2) (by regs_nodup) (w := w) (st (a :: rest) done) a (cstream A w rest)
        (by simp only [hst]; cst_upd) (by simp only [hst]; cst_upd)
        (by simp only [hst]; cst_upd) (by simp only [hst]; cst_upd)
        (by simp only [hst]; cst_upd) (by simp only [hst]; cst_upd)
      have hcLv : (st (a :: rest) done cL).length = L := by
        simp only [hst]; cst_upd
      rw [hcLv] at h
      refine h.congr ?_
      funext k
      simp only [hst, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all [List.flatMap_append, cst_cstream_replicate])
    (fun a rest done _ => by
      have h1 := cstream_ne_nil (A := A) hw (x := a) (l := rest)
      have h2 := csyms_ne_nil (A := A) hw a
      simp only [hst]; cst_upd)
    (fun done => by simp only [hst]; cst_upd)
  have e₀ : st B [] = ρ := by
    funext k
    simp only [hst, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  have hl := hloop B [] (fun _ _ => trivial)
  rw [e₀, List.nil_append] at hl
  have hmv := rsa_moveR (body := body) (ι := ι) hrg (Ne.symm ‹dst ≠ ra›) (st [] B)
  refine ((RsaRuns.seq hdisj hl hmv).congr ?_).mono ?_
  · funext k
    simp only [hst, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · have hlen : (st [] B ra).length = B.length * L * w := by
      simp only [hst, Function.update_self, List.length_reverse, length_cstream,
        List.length_flatMap, List.length_replicate]
      simp [List.map_const', List.sum_replicate]
    rw [hlen]
    unfold cstRepCost
    nlinarith

end Rep

/-! ### Registers of the stage -/

/-- The registers of the chirp stage: the complex-product registers `c x`, the repetition
registers `cb`, `ra`, `cL`, `cL'`, the spares `s1`, `s2`, the axis counter `ax` with its spare
`ax'`, the shift `pn2` and the constant `kc` of the disk rounding, the kernel register `kr`, and
the caller's registers `x j`. -/
inductive CsR (X : Type) where
  | c (x : CR)
  | cb | ra | cL | cL' | s1 | s2 | ax | ax' | pn2 | kc | kr
  | x (j : X)
  deriving DecidableEq

lemma CsR.c_injective {X : Type} : Function.Injective (CsR.c : CR → CsR X) :=
  fun _ _ h => CsR.c.inj h

/-- The layout of the disk rounding: operand `xs ↦ out`, table `ys ↦ kc`, shift `pn ↦ pn2`,
result `out ↦ kr`, every other complex-product register in place. -/
def cstDmap {X : Type} : CR → CsR X
  | .xs => .c .out
  | .ys => .kc
  | .pn => .pn2
  | .out => .kr
  | x => .c x

/-- A left inverse of `cstDmap`. -/
def cstDinv {X : Type} : CsR X → CR
  | .c .out => .xs
  | .kc => .ys
  | .pn2 => .pn
  | .kr => .out
  | .c x => x
  | _ => .xs

lemma cstDmap_injective {X : Type} : Function.Injective (cstDmap : CR → CsR X) := by
  refine Function.LeftInverse.injective (g := cstDinv) ?_
  intro a
  cases a <;> rfl

/-- The register file `ρ` with the caller's registers replaced by `xx`. -/
def cstSetX {X : Type} {A : ℕ} (ρ : CsR X → List (Fin (A + 4)))
    (xx : X → List (Fin (A + 4))) : CsR X → List (Fin (A + 4))
  | .x j => xx j
  | r => ρ r

@[simp] lemma cstSetX_x {X : Type} {A : ℕ} (ρ : CsR X → List (Fin (A + 4)))
    (xx : X → List (Fin (A + 4))) (j : X) : cstSetX ρ xx (.x j) = xx j := rfl

@[simp] lemma cstSetX_c {X : Type} {A : ℕ} (ρ : CsR X → List (Fin (A + 4)))
    (xx : X → List (Fin (A + 4))) (y : CR) : cstSetX ρ xx (.c y) = ρ (.c y) := rfl

@[simp] lemma cstSetX_cb {X : Type} {A : ℕ} (ρ : CsR X → List (Fin (A + 4)))
    (xx : X → List (Fin (A + 4))) : cstSetX ρ xx .cb = ρ .cb := rfl
@[simp] lemma cstSetX_ra {X : Type} {A : ℕ} (ρ : CsR X → List (Fin (A + 4)))
    (xx : X → List (Fin (A + 4))) : cstSetX ρ xx .ra = ρ .ra := rfl
@[simp] lemma cstSetX_cL {X : Type} {A : ℕ} (ρ : CsR X → List (Fin (A + 4)))
    (xx : X → List (Fin (A + 4))) : cstSetX ρ xx .cL = ρ .cL := rfl
@[simp] lemma cstSetX_cL' {X : Type} {A : ℕ} (ρ : CsR X → List (Fin (A + 4)))
    (xx : X → List (Fin (A + 4))) : cstSetX ρ xx .cL' = ρ .cL' := rfl
@[simp] lemma cstSetX_s1 {X : Type} {A : ℕ} (ρ : CsR X → List (Fin (A + 4)))
    (xx : X → List (Fin (A + 4))) : cstSetX ρ xx .s1 = ρ .s1 := rfl
@[simp] lemma cstSetX_s2 {X : Type} {A : ℕ} (ρ : CsR X → List (Fin (A + 4)))
    (xx : X → List (Fin (A + 4))) : cstSetX ρ xx .s2 = ρ .s2 := rfl
@[simp] lemma cstSetX_ax {X : Type} {A : ℕ} (ρ : CsR X → List (Fin (A + 4)))
    (xx : X → List (Fin (A + 4))) : cstSetX ρ xx .ax = ρ .ax := rfl
@[simp] lemma cstSetX_ax' {X : Type} {A : ℕ} (ρ : CsR X → List (Fin (A + 4)))
    (xx : X → List (Fin (A + 4))) : cstSetX ρ xx .ax' = ρ .ax' := rfl
@[simp] lemma cstSetX_pn2 {X : Type} {A : ℕ} (ρ : CsR X → List (Fin (A + 4)))
    (xx : X → List (Fin (A + 4))) : cstSetX ρ xx .pn2 = ρ .pn2 := rfl
@[simp] lemma cstSetX_kc {X : Type} {A : ℕ} (ρ : CsR X → List (Fin (A + 4)))
    (xx : X → List (Fin (A + 4))) : cstSetX ρ xx .kc = ρ .kc := rfl
@[simp] lemma cstSetX_kr {X : Type} {A : ℕ} (ρ : CsR X → List (Fin (A + 4)))
    (xx : X → List (Fin (A + 4))) : cstSetX ρ xx .kr = ρ .kr := rfl

/-! ### The axis step -/

section Step

variable {T Q A : ℕ} {U P X : Type} [DecidableEq X] {body : P → Pr P T Q A U}
  {rg : CsR X → Fin T} {ι : Fin 64 → Fin T}

/-- The complex-product registers of the stage. -/
abbrev cstCr (rg : CsR X → Fin T) : CR → Fin T := fun x => rg (.c x)

/-- The complex-product registers of the disk rounding. -/
abbrev cstDr (rg : CsR X → Fin T) : CR → Fin T := fun x => rg (cstDmap x)

variable (ι) in
/-- One axis: the box on `out` repeated `|cL|` times onto `xs`, multiplied block by block by the
table on `ys` onto `out`; `xs`, `ys`, `cL` cleared. -/
def cstStep (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (rg : CsR X → Fin T) : Pr P T Q A U :=
  .seq (cstRep rg (.c .out) (.c .xs) (.c .wn) .cb .ra .cL .cL' .s1 .s2)
  (.seq (cmulTable (cstCr rg) (cmulOne ι hι hT hQ (cstCr rg)))
  (.seq (uclear (rg (.c .xs))) (.seq (uclear (rg (.c .ys))) (uclear (rg .cL)))))

/-- The step bound of `cstStep` on a box of `n` entries and a table of `L` entries. -/
def cstStepCost (w n L : ℕ) : ℕ :=
  cstRepCost w n L + (n * L * (cmulCost w + 6 * w + 8) + 6) + (2 * (n * L * w) + 2) +
    (2 * (L * w) + 2) + (2 * L + 2)

variable (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
include hrg hdisj

theorem cst_step_runs (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (hA : 96 ≤ A) {w q : ℕ} (hw : 1 ≤ w) (hq : q ≤ w) (ρ : CsR X → List (Fin (A + 4)))
    (hr : Ready (fun x => ρ (.c x)) w q) (B ts : List GaussianInt) (hL : 1 ≤ ts.length)
    (hB : ∀ x ∈ B, Fits w x) (hts : ∀ y ∈ ts, Fits w y)
    (hout : ρ (.c .out) = cstream A w B) (hys : ρ (.c .ys) = cstream A w ts)
    (hcL : (ρ .cL).length = ts.length) (hxs : ρ (.c .xs) = []) (hxsv : ρ (.c .xsv) = [])
    (hysv : ρ (.c .ysv) = []) (hacc : ρ (.c .acc) = []) (hcb : ρ .cb = []) (hra : ρ .ra = [])
    (hcL' : ρ .cL' = []) (hs1 : ρ .s1 = []) (hs2 : ρ .s2 = []) :
    RsaRuns body rg ι (cstStep ι hι hT hQ rg) ρ
      (Function.update (Function.update (Function.update ρ (.c .out)
        (cstream A w (B.flatMap fun e => ts.map fun y => tdivN q (e * y)))) (.c .ys) []) .cL [])
      (cstStepCost w B.length ts.length) := by
  -- the repetition pass
  have h1 := cst_rep_runs (body := body) (ι := ι) hrg hdisj (src := .c .out) (dst := .c .xs)
    (wn := .c .wn) (cb := .cb) (ra := .ra) (cL := .cL) (cL' := .cL') (s1 := .s1) (s2 := .s2)
    (by simp) hw ρ B hout hr.wn hcb hra hcL' hs1 hs2
  rw [hcL, hxs, List.append_nil] at h1
  set ρ₁ := Function.update (Function.update ρ (.c .out) []) (.c .xs)
    (cstream A w (B.flatMap (List.replicate ts.length))) with hρ₁
  -- the products
  have hcr : Function.Injective (cstCr rg) := fun a b h => CsR.c_injective (hrg h)
  have hdisj' : ∀ r j, cstCr rg r ≠ ι j := fun r j => hdisj _ j
  have hr₁ : Ready (fun x => ρ₁ (.c x)) w q :=
    cst_ready_of_eq hr (fun x h1 h2 h3 h4 h5 h6 => by simp [*])
  have hflat : (B.map (List.replicate ts.length)).flatten = B.flatMap (List.replicate ts.length) :=
    by simp [List.flatMap_def]
  have h2 := RsaRuns.of_c hrg CsR.c_injective
    (cmulTable_runs (body := body) (cr := cstCr rg) hcr hdisj' hι hT hQ hA
      (ρ := fun x => ρ₁ (.c x)) hr₁ hw hq (B.map (List.replicate ts.length)) ts hL
      (by intro b hb; obtain ⟨e, _, rfl⟩ := List.mem_map.1 hb; simp)
      (by
        intro x hx
        rw [hflat] at hx
        obtain ⟨e, he, hx⟩ := List.mem_flatMap.1 hx
        rw [List.eq_of_mem_replicate hx]
        exact hB e he)
      hts (by simp [hρ₁, hflat]) (by simp [hρ₁, hys]) (by simp [hρ₁, hxsv])
      (by simp [hρ₁, hysv]) (by simp [hρ₁, hacc])) ρ₁ (fun _ => rfl)
  rw [cst_extend_update _ CsR.c_injective, cst_tableOut_replicate] at h2
  set ρ₂ := Function.update ρ₁ (.c .out)
    (cstream A w (B.flatMap fun e => ts.map fun y => tdivN q (e * y)) ++ ρ₁ (.c .out))
    with hρ₂
  -- clearing
  have h3 := rsa_uclear (body := body) (ι := ι) hrg (.c .xs) ρ₂
  have h4 := rsa_uclear (body := body) (ι := ι) hrg (.c .ys) (Function.update ρ₂ (.c .xs) [])
  have h5 := rsa_uclear (body := body) (ι := ι) hrg .cL
    (Function.update (Function.update ρ₂ (.c .xs) []) (.c .ys) [])
  refine ((RsaRuns.seq hdisj h1 (RsaRuns.seq hdisj h2 (RsaRuns.seq hdisj h3
    (RsaRuns.seq hdisj h4 h5)))).congr ?_).mono ?_
  · funext r
    simp only [hρ₂, hρ₁]
    cst_upd
  · have e1 : (ρ₂ (.c .xs)).length = B.length * ts.length * w := by
      simp [hρ₂, hρ₁, List.length_flatMap, List.map_const',
        List.sum_replicate]
    have e2 : (Function.update ρ₂ (.c .xs) [] (.c .ys)).length = ts.length * w := by
      simp [hρ₂, hρ₁, hys]
    have e3 : (Function.update (Function.update ρ₂ (.c .xs) []) (.c .ys) [] .cL).length =
        ts.length := by
      simp [hρ₂, hρ₁, hcL]
    have e4 : (B.map (List.replicate ts.length)).flatten.length = B.length * ts.length := by
      rw [hflat]; simp [List.length_flatMap, List.map_const', List.sum_replicate]
    rw [e1, e2, e3, e4]
    unfold cstStepCost cstRepCost
    nlinarith

end Step

/-! ### Boxes of the stage -/

section Boxes

/-- The table of axis `k`: `tab k j` for `j < t_k`. -/
def cstTab (ts : List ℕ) (tab : ℕ → ℕ → GaussianInt) (k : ℕ) : List GaussianInt :=
  (List.range (ts.getD k 0)).map (tab k)

/-- The box over the axes `0 … k`: the truncated products along its addresses. -/
def cstBoxK (q : ℕ) (ts : List ℕ) (tab : ℕ → ℕ → GaussianInt) (k : ℕ) :
    List GaussianInt :=
  (cstAddrs (ts.take (k + 1))).map (cstEnt q tab)

lemma cst_getD {ts : List ℕ} {k : ℕ} (h : k < ts.length) : ts.getD k 0 = ts[k] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

lemma cst_take_succ {ts : List ℕ} {k : ℕ} (h : k < ts.length) :
    ts.take (k + 1) = ts.take k ++ [ts.getD k 0] := by
  rw [List.take_succ_eq_append_getElem h, cst_getD h]

theorem cstBoxK_zero (q : ℕ) {ts : List ℕ} (hd : 1 ≤ ts.length)
    (tab : ℕ → ℕ → GaussianInt) :
    cstBoxK q ts tab 0 = cstTab ts tab 0 := by
  have h := cst_take_succ (ts := ts) (k := 0) (by omega)
  simp only [List.take_zero, List.nil_append] at h
  unfold cstBoxK cstTab
  rw [h]
  simp only [cstAddrs, List.map_flatMap, List.map_cons, List.map_nil, cstEnt_single]
  induction (List.range (ts.getD 0 0)) with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem cstBoxK_succ (q : ℕ) {ts : List ℕ} (tab : ℕ → ℕ → GaussianInt) {j : ℕ}
    (hj : j + 1 < ts.length) :
    cstBoxK q ts tab (j + 1) =
      (cstBoxK q ts tab j).flatMap fun e =>
        (cstTab ts tab (j + 1)).map fun y => tdivN q (e * y) := by
  unfold cstBoxK cstTab
  rw [cst_take_succ hj, cstAddrs_append, List.map_flatMap, List.flatMap_map]
  refine List.flatMap_congr fun l hl => ?_
  have hlen : l.length = j + 1 := by
    rw [cst_length_of_mem_addrs hl, List.length_take]; omega
  have hne : l ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  simp only [List.map_map]
  refine List.map_congr_left fun x _ => ?_
  simp only [Function.comp_apply]
  rw [cstEnt_append q tab hne, hlen]

theorem cstBoxK_last (q : ℕ) (ts : List ℕ) (tab : ℕ → ℕ → GaussianInt)
    (hd : 1 ≤ ts.length) :
    cstBoxK q ts tab (ts.length - 1) = (cstAddrs ts).map (cstEnt q tab) := by
  unfold cstBoxK
  rw [Nat.sub_add_cancel hd, List.take_length]

theorem cst_length_boxK (q : ℕ) (ts : List ℕ) (tab : ℕ → ℕ → GaussianInt) (k : ℕ) :
    (cstBoxK q ts tab k).length = (ts.take (k + 1)).prod := by
  unfold cstBoxK; rw [List.length_map, cst_length_addrs]

theorem cst_fits_boxK {w q : ℕ} {ts : List ℕ} {tab : ℕ → ℕ → GaussianInt}
    (hfE : ∀ l : List ℕ, 1 ≤ l.length → l.length ≤ ts.length → Fits w (cstEnt q tab l))
    {k : ℕ} (hk : k < ts.length) : ∀ e ∈ cstBoxK q ts tab k, Fits w e := by
  intro e he
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 he
  have := cst_length_of_mem_addrs hl
  rw [List.length_take] at this
  exact hfE l (by omega) (by omega)

theorem cst_fits_tab {w : ℕ} {ts : List ℕ} {tab : ℕ → ℕ → GaussianInt}
    (hfT : ∀ k < ts.length, ∀ j < ts.getD k 0, Fits w (tab k j)) {k : ℕ}
    (hk : k < ts.length) : ∀ y ∈ cstTab ts tab k, Fits w y := by
  intro y hy
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
  exact hfT k hk j (List.mem_range.1 hj)

lemma cst_prod_take_le :
    ∀ (ts : List ℕ), (∀ x ∈ ts, 1 ≤ x) → ∀ k, (ts.take k).prod ≤ ts.prod
  | [], _, k => by simp
  | a :: ts, h, 0 => by
      simp only [List.take_zero, List.prod_nil, List.prod_cons]
      have h1 : 1 ≤ a := h a (by simp)
      have h2 : 0 < ts.prod :=
        CanonicallyOrderedAdd.list_prod_pos.2 fun x hx => h x (by simp [hx])
      nlinarith
  | a :: ts, h, k + 1 => by
      simp only [List.take_succ_cons, List.prod_cons]
      exact Nat.mul_le_mul_left _ (cst_prod_take_le ts (fun x hx => h x (by simp [hx])) k)

lemma cst_one_le_prod_take (ts : List ℕ) (h : ∀ x ∈ ts, 1 ≤ x) (k : ℕ) :
    1 ≤ (ts.take k).prod :=
  CanonicallyOrderedAdd.list_prod_pos.2 fun x hx => h x (List.mem_of_mem_take hx)

end Boxes

/-! ### The stage -/

section Stage

variable {T Q A : ℕ} {U P X : Type} [DecidableEq X] {body : P → Pr P T Q A U}
  {rg : CsR X → Fin T} {ι : Fin 64 → Fin T}

/-- The register file before and after the stage, off `ax`, `kr` and the caller's registers:
ready for `w` and `q = p + g`, the work registers empty, `pn2` with `q + 2` symbols, `kc` with
the disk constant. -/
structure CstBase (ρ : CsR X → List (Fin (A + 4))) (w p g : ℕ) : Prop where
  ready : Ready (fun x => ρ (.c x)) w (p + g)
  xs : ρ (.c .xs) = []
  ys : ρ (.c .ys) = []
  xsv : ρ (.c .xsv) = []
  ysv : ρ (.c .ysv) = []
  acc : ρ (.c .acc) = []
  out : ρ (.c .out) = []
  cb : ρ .cb = []
  ra : ρ .ra = []
  cL : ρ .cL = []
  cL' : ρ .cL' = []
  s1 : ρ .s1 = []
  s2 : ρ .s2 = []
  ax' : ρ .ax' = []
  pn2 : (ρ .pn2).length = p + g + 2
  kc : ρ .kc = csyms A w (cstDiskC p)

variable (ι) in
/-- The chirp stage: axis `0` loaded and copied onto `out`, `prep ; cstStep` for every further
axis, then the disk rounding onto `kr`. -/
def cstChirpBox (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (rg : CsR X → Fin T) (prep : Pr P T Q A U) : Pr P T Q A U :=
  .seq prep
  (.seq (bcopy (rg (.c .ys)) (rg (.c .out)) (rg .s1) (rg .s2))
  (.seq (uclear (rg (.c .ys)))
  (.seq (uclear (rg .cL))
  (.seq (scanP (rg .ax) (rg .ax') (.seq prep (cstStep ι hι hT hQ rg)))
  (.seq (cmulTable (cstDr rg) (cmulOne ι hι hT hQ (cstDr rg)))
    (uclear (rg (.c .out))))))))

/-- The step bound of the stage, `bp k` the bound of loading axis `k`. -/
def cstChirpCost (w : ℕ) (ts : List ℕ) (bp : ℕ → ℕ) : ℕ :=
  bp 0 + (6 * (ts.getD 0 0 * w) + 6) + (2 * (ts.getD 0 0 * w) + 2) + (2 * ts.getD 0 0 + 2) +
    (∑ j ∈ Finset.range (ts.length - 1),
      (bp (j + 1) + cstStepCost w (ts.take (j + 1)).prod (ts.getD (j + 1) 0) + 3) +
      2 * (ts.length - 1) + 4) +
    (ts.prod * (cmulCost w + 6 * w + 8) + 6) + (2 * (ts.prod * w) + 2)

variable (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
include hrg hdisj

/-- **The chirp kernel box.** `prep`, run with axis `k` pending (`ys`, `cL` empty, the caller's
registers at `cfg k`), loads the table `cstTab ts tab k` onto `ys` and `t_k` symbols onto `cL`
and moves the caller's registers to `cfg (k + 1)`. From a base register file (`CstBase`) with
`d - 1` symbols on `ax`, the stage pushes onto `kr` the stream of the disk-rounded truncated
products `tdivN (q+2) (cstEnt q tab l · (2^(p+2) - 1))` over all addresses `l` of
`∏ [0, t_k)`, `q = p + g`, in address order; every other register ends as it started, the
caller's registers at `cfg d`. -/
theorem cst_chirpBox_runs (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (hA : 96 ≤ A) {w p g : ℕ} (hw : p + g + 2 ≤ w) (ts : List ℕ) (hd : 1 ≤ ts.length)
    (hts : ∀ x ∈ ts, 1 ≤ x) (tab : ℕ → ℕ → GaussianInt)
    (hfT : ∀ k < ts.length, ∀ j < ts.getD k 0, Fits w (tab k j))
    (hfE : ∀ l : List ℕ, 1 ≤ l.length → l.length ≤ ts.length →
      Fits w (cstEnt (p + g) tab l))
    (hfC : Fits w (cstDiskC p)) (prep : Pr P T Q A U) (cfg : ℕ → X → List (Fin (A + 4)))
    (cnt : ℕ → List (Fin (A + 4))) (bp : ℕ → ℕ)
    (hprep : ∀ k < ts.length, ∀ ρ : CsR X → List (Fin (A + 4)), ρ (.c .ys) = [] →
      ρ .cL = [] → (∀ j, ρ (.x j) = cfg k j) →
      RsaRuns body rg ι prep ρ (cstSetX (Function.update (Function.update ρ (.c .ys)
        (cstream A w (cstTab ts tab k))) .cL (cnt k)) (cfg (k + 1))) (bp k))
    (hcnt : ∀ k < ts.length, (cnt k).length = ts.getD k 0)
    (ρ : CsR X → List (Fin (A + 4))) (hb : CstBase ρ w p g)
    (hax : (ρ .ax).length + 1 = ts.length) (hx : ∀ j, ρ (.x j) = cfg 0 j) :
    RsaRuns body rg ι (cstChirpBox ι hι hT hQ rg prep) ρ
      (cstSetX (Function.update ρ .kr (cstream A w (((cstAddrs ts).map (cstEnt (p + g) tab)).map
        fun M => tdivN (p + g + 2) (M * cstDiskC p)) ++ ρ .kr)) (cfg ts.length))
      (cstChirpCost w ts bp) := by
  set q := p + g with hq
  have hw1 : 1 ≤ w := by omega
  have hqw : q ≤ w := by omega
  have hgetD : ∀ k < ts.length, 1 ≤ ts.getD k 0 := fun k hk => by
    rw [cst_getD hk]; exact hts _ (List.getElem_mem hk)
  -- axis 0
  have hP0 := hprep 0 hd ρ hb.ys hb.cL hx
  set σ₀ := cstSetX (Function.update (Function.update ρ (.c .ys)
    (cstream A w (cstTab ts tab 0))) .cL (cnt 0)) (cfg 1) with hσ₀
  have hB0 := rsa_bcopy (body := body) (ι := ι) hrg (a := .c .ys) (c := .c .out) (t₁ := .s1)
    (t₂ := .s2) (by simp) σ₀ (by simp [hσ₀, hb.s1]) (by simp [hσ₀, hb.s2])
  have e0 : σ₀ (.c .ys) = cstream A w (cstTab ts tab 0) := by simp [hσ₀]
  have e0' : σ₀ (.c .out) = [] := by simp [hσ₀, hb.out]
  rw [e0, e0', List.append_nil] at hB0
  set σ₁ := Function.update σ₀ (.c .out) (cstream A w (cstTab ts tab 0)) with hσ₁
  have hU1 := rsa_uclear (body := body) (ι := ι) hrg (.c .ys) σ₁
  have hU2 := rsa_uclear (body := body) (ι := ι) hrg .cL (Function.update σ₁ (.c .ys) [])
  -- the further axes
  set cs := ρ .ax with hcs
  set Φ : ℕ → CsR X → List (Fin (A + 4)) := fun j =>
    cstSetX (Function.update ρ (.c .out) (cstream A w (cstBoxK q ts tab j))) (cfg (j + 1))
    with hΦ
  have hloop := rsa_scanP_sum (body := body) (ι := ι) hrg hdisj (a := .ax) (t := .ax') (by simp)
    (p := .seq prep (cstStep ι hι hT hQ rg)) Φ
    (b := fun j => bp (j + 1) + cstStepCost w (ts.take (j + 1)).prod (ts.getD (j + 1) 0)) cs
    (fun j hj => by
      have hj1 : j + 1 < ts.length := by omega
      set σ := Function.update (Function.update (Φ j) .ax (cs.drop (j + 1))) .ax'
        (cs.take (j + 1)).reverse with hσ
      have hP := hprep (j + 1) hj1 σ (by simp [hσ, hΦ, hb.ys]) (by simp [hσ, hΦ, hb.cL])
        (fun j' => by simp [hσ, hΦ])
      set τ := cstSetX (Function.update (Function.update σ (.c .ys)
        (cstream A w (cstTab ts tab (j + 1)))) .cL (cnt (j + 1))) (cfg (j + 1 + 1)) with hτ
      have hS := cst_step_runs (body := body) (ι := ι) hrg hdisj hι hT hQ hA hw1 hqw τ
        (cst_ready_of_eq hb.ready (fun x h1 h2 h3 h4 h5 h6 => by
          simp [*]))
        (cstBoxK q ts tab j) (cstTab ts tab (j + 1))
        (by simp only [cstTab, List.length_map, List.length_range]; exact hgetD _ hj1)
        (cst_fits_boxK hfE (by omega)) (cst_fits_tab hfT hj1)
        (by simp [hτ, hσ, hΦ]) (by simp [hτ, hσ, hΦ])
        (by simp [hτ, hσ, hΦ, cstTab, hcnt _ hj1]) (by simp [hτ, hσ, hΦ, hb.xs])
        (by simp [hτ, hσ, hΦ, hb.xsv]) (by simp [hτ, hσ, hΦ, hb.ysv])
        (by simp [hτ, hσ, hΦ, hb.acc]) (by simp [hτ, hσ, hΦ, hb.cb])
        (by simp [hτ, hσ, hΦ, hb.ra]) (by simp [hτ, hσ, hΦ, hb.cL'])
        (by simp [hτ, hσ, hΦ, hb.s1]) (by simp [hτ, hσ, hΦ, hb.s2])
      have hlen : (cstBoxK q ts tab j).length = (ts.take (j + 1)).prod := cst_length_boxK q ts tab j
      have hlenT : (cstTab ts tab (j + 1)).length = ts.getD (j + 1) 0 := by simp [cstTab]
      rw [hlen, hlenT, ← cstBoxK_succ q tab hj1] at hS
      refine (RsaRuns.seq hdisj hP hS).congr ?_
      funext r
      cases r with
      | c y => cases y <;> simp [hτ, hσ, hΦ, hb.ys]
      | x j' => simp [hτ, hσ, hΦ]
      | _ => simp [hτ, hσ, hΦ, hb.cL])
  have hstart : Function.update (Function.update σ₁ (.c .ys) []) .cL [] =
      Function.update (Function.update (Φ 0) .ax cs) .ax' [] := by
    funext r
    cases r with
    | c y =>
        cases y <;> simp [hσ₁, hσ₀, hΦ, hb.ys, cstBoxK_zero q hd tab]
    | x j' => simp [hσ₁, hσ₀, hΦ]
    | _ => simp [hσ₁, hσ₀, hΦ, hb.cL, hcs, hb.ax']
  rw [← hstart] at hloop
  -- the disk rounding
  set σL := Function.update (Function.update (Φ cs.length) .ax cs) .ax' [] with hσL
  have hlast : cs.length = ts.length - 1 := by omega
  have hboxL : cstBoxK q ts tab cs.length = (cstAddrs ts).map (cstEnt q tab) := by
    rw [hlast]; exact cstBoxK_last q ts tab hd
  have hdr : Function.Injective (cstDr rg) := fun a b h => cstDmap_injective (hrg h)
  have hdisj' : ∀ r j, cstDr rg r ≠ ι j := fun r j => hdisj _ j
  have hrd : Ready (fun x => σL (cstDmap x)) w (q + 2) := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24⟩ := hb.ready
    constructor <;> simp [cstDmap, hb.pn2, *]
  set Bx := (cstAddrs ts).map (cstEnt q tab) with hBx
  have hsingle : (Bx.map fun e => [e]).flatten = Bx := cst_flatten_singleton Bx
  have hD := RsaRuns.of_c hrg cstDmap_injective
    (cmulTable_runs (body := body) (cr := cstDr rg) hdr hdisj' hι hT hQ hA
      (ρ := fun x => σL (cstDmap x)) hrd hw1 (by omega) (Bx.map fun e => [e]) [cstDiskC p]
      (by simp) (by intro b hb'; obtain ⟨e, _, rfl⟩ := List.mem_map.1 hb'; simp)
      (by
        rw [hsingle]
        intro e he
        have := cst_fits_boxK hfE (k := cs.length) (by omega) e
        rw [hboxL] at this
        exact this he)
      (by simpa using hfC)
      (by simp [hσL, hΦ, cstDmap, hboxL, hsingle])
      (by simp [hσL, hΦ, cstDmap, hb.kc])
      (by simp [hσL, hΦ, cstDmap, hb.xsv]) (by simp [hσL, hΦ, cstDmap, hb.ysv])
      (by simp [hσL, hΦ, cstDmap, hb.acc])) σL (fun _ => rfl)
  rw [cst_extend_update _ cstDmap_injective, cst_tableOut_single] at hD
  have hUo := rsa_uclear (body := body) (ι := ι) hrg (.c .out)
    (Function.update σL (cstDmap .out)
      (cstream A w (Bx.map fun e => tdivN (q + 2) (e * cstDiskC p)) ++ σL (cstDmap .out)))
  refine ((RsaRuns.seq hdisj hP0 (RsaRuns.seq hdisj hB0 (RsaRuns.seq hdisj hU1
    (RsaRuns.seq hdisj hU2 (RsaRuns.seq hdisj hloop
      (RsaRuns.seq hdisj hD hUo)))))).congr ?_).mono ?_
  · funext r
    cases r with
    | c y => cases y <;> simp [hσL, hΦ, cstDmap, hboxL, hb.out]
    | x j' => simp [hσL, hΦ, cstDmap, hlast, Nat.sub_add_cancel hd]
    | _ => simp [hσL, hΦ, cstDmap, hcs, hb.ax']
  · have l1 : (cstream A w (cstTab ts tab 0)).length = ts.getD 0 0 * w := by simp [cstTab]
    have l2 : (σ₁ (.c .ys)).length = ts.getD 0 0 * w := by simp [hσ₁, hσ₀, cstTab]
    have l3 : (Function.update σ₁ (.c .ys) [] .cL).length = ts.getD 0 0 := by
      simp [hσ₁, hσ₀, hcnt 0 hd]
    have l4 : ((Bx.map fun e => [e]).flatten).length = ts.prod := by
      rw [hsingle, hBx, List.length_map, cst_length_addrs]
    have l5 : (Function.update σL (cstDmap .out)
        (cstream A w (Bx.map fun e => tdivN (q + 2) (e * cstDiskC p)) ++ σL (cstDmap .out))
        (.c .out)).length = ts.prod * w := by
      simp [hσL, hΦ, cstDmap, hboxL, hBx, cst_length_addrs]
    rw [l1, l2, l3, l4, l5, hlast]
    unfold cstChirpCost
    omega

end Stage

/-! ### Cost -/

section Cost

lemma cst_cmulCost_ge (w : ℕ) : 128 * w + 128 ≤ cmulCost w := by
  unfold cmulCost; omega

/-- One axis costs at most `2 n L cmulCost w`. -/
theorem cst_stepCost_le (w n L : ℕ) (hn : 1 ≤ n) (hL : 1 ≤ L) :
    cstStepCost w n L ≤ 2 * (n * L) * cmulCost w := by
  have hC := cst_cmulCost_ge w
  set m := n * L with hm
  have h1 : n ≤ m := Nat.le_mul_of_pos_right n hL
  have h2 : L ≤ m := Nat.le_mul_of_pos_left L hn
  have e1 : n * (8 * w + 12 + L * (6 * w + 11)) = n * (8 * w + 12) + m * (6 * w + 11) := by
    rw [hm]; ring
  have h3 : n * (8 * w + 12) ≤ m * (8 * w + 12) := Nat.mul_le_mul_right _ h1
  have h4 : L * w ≤ m * w := Nat.mul_le_mul_right _ h2
  have h5 : m * (24 * w + 49) ≤ m * cmulCost w := Nat.mul_le_mul_left _ (by omega)
  have h6 : 1 ≤ m := le_trans hn h1
  unfold cstStepCost cstRepCost
  rw [e1, show n * L * w = m * w by rw [hm]]
  nlinarith

/-- **The cost of the chirp stage**: the loads, and at most `4 d V cmulCost w` for the
products, `V = ∏ t_k`. -/
theorem cst_chirpCost_le (w : ℕ) (ts : List ℕ) (bp : ℕ → ℕ) (hd : 1 ≤ ts.length)
    (hts : ∀ x ∈ ts, 1 ≤ x) :
    cstChirpCost w ts bp ≤
      ∑ k ∈ Finset.range ts.length, bp k + 4 * ts.length * ts.prod * cmulCost w := by
  have hC := cst_cmulCost_ge w
  have hV1 : 1 ≤ ts.prod := by
    have := cst_one_le_prod_take ts hts ts.length
    rwa [List.take_length] at this
  have hL0 : ts.getD 0 0 ≤ ts.prod := by
    have h := cst_prod_take_le ts hts 1
    rw [cst_take_succ (by omega), List.take_zero, List.nil_append, List.prod_singleton] at h
    exact h
  have hstep : ∀ j ∈ Finset.range (ts.length - 1),
      bp (j + 1) + cstStepCost w (ts.take (j + 1)).prod (ts.getD (j + 1) 0) + 3 ≤
        bp (j + 1) + (2 * ts.prod * cmulCost w + 3) := by
    intro j hj
    have hj' : j + 1 < ts.length := by have := Finset.mem_range.1 hj; omega
    have hL : 1 ≤ ts.getD (j + 1) 0 := by rw [cst_getD hj']; exact hts _ (List.getElem_mem hj')
    have h1 := cst_stepCost_le w _ _ (cst_one_le_prod_take ts hts (j + 1)) hL
    have h2 : (ts.take (j + 1)).prod * ts.getD (j + 1) 0 ≤ ts.prod := by
      have := cst_prod_take_le ts hts (j + 2)
      rwa [cst_take_succ hj', List.prod_append, List.prod_singleton] at this
    have h3 : 2 * ((ts.take (j + 1)).prod * ts.getD (j + 1) 0) * cmulCost w ≤
        2 * ts.prod * cmulCost w :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 h2)
    omega
  have hsum : ∑ j ∈ Finset.range (ts.length - 1),
      (bp (j + 1) + cstStepCost w (ts.take (j + 1)).prod (ts.getD (j + 1) 0) + 3) ≤
        ∑ j ∈ Finset.range (ts.length - 1), bp (j + 1) +
          (ts.length - 1) * (2 * ts.prod * cmulCost w + 3) := by
    refine (Finset.sum_le_sum hstep).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hbp : ∑ k ∈ Finset.range ts.length, bp k =
      bp 0 + ∑ j ∈ Finset.range (ts.length - 1), bp (j + 1) := by
    obtain ⟨d', hd'⟩ : ∃ d', ts.length = d' + 1 := ⟨ts.length - 1, by omega⟩
    rw [hd', Finset.sum_range_succ', Nat.add_sub_cancel, Nat.add_comm]
  unfold cstChirpCost
  rw [hbp]
  have hLw : ts.getD 0 0 * w ≤ ts.prod * w := Nat.mul_le_mul_right _ hL0
  generalize ∑ j ∈ Finset.range (ts.length - 1),
    (bp (j + 1) + cstStepCost w (ts.take (j + 1)).prod (ts.getD (j + 1) 0) + 3) = S at hsum ⊢
  generalize ∑ j ∈ Finset.range (ts.length - 1), bp (j + 1) = Sb at hsum ⊢
  generalize cmulCost w = C at *
  generalize ts.prod = V at *
  generalize ts.getD 0 0 = L0 at *
  obtain ⟨e, he⟩ : ∃ e, ts.length = e + 1 := ⟨ts.length - 1, by omega⟩
  rw [he, Nat.add_sub_cancel] at hsum ⊢
  generalize ts.length = d at *
  subst he
  clear hbp hstep
  have hVC : 128 * V ≤ V * C := by nlinarith
  have hVw : 128 * (V * w) ≤ V * C := by nlinarith
  have hVC1 : 128 ≤ V * C := by nlinarith
  have hE : e * (2 * V * C + 3) + 5 * e ≤ e * (3 * V * C) := by
    have : 2 * V * C + 3 + 5 ≤ 3 * V * C := by nlinarith
    nlinarith
  linarith

end Cost

/-! ### The pipeline instance -/

section Pipeline

open IntegerMultBounds.MathlibTM2.Mult.Chirp

/-- The chirp table of axis `k` in index form: the numerators at scale `2^(p+g)` of
`axisPhase p g (t k) (s k) j`, `j = 0 … t_k - 1`. -/
theorem cstTab_axTab (p g : ℕ) {d : ℕ} (t s : Fin d → ℕ) {k : ℕ} (hk : k < d) :
    cstTab (List.ofFn t) (cstAxTab p g t s) k =
      List.ofFn fun j : Fin (t ⟨k, hk⟩) =>
        numer (p + g)
          (axisPhase p g (t ⟨k, hk⟩) (s ⟨k, hk⟩) ((j : ℕ) : ZMod (t ⟨k, hk⟩))) := by
  have hg : (List.ofFn t).getD k 0 = t ⟨k, hk⟩ := by
    rw [cst_getD (by simpa using hk), List.getElem_ofFn]
  apply List.ext_getElem (by rw [cstTab, List.length_map, List.length_range, hg, List.length_ofFn])
  intro j h₁ h₂
  simp only [cstTab, List.getElem_map, List.getElem_range, List.getElem_ofFn, cstAxTab, hk,
    ↓reduceDIte]

variable {T Q A : ℕ} {U P X : Type} [DecidableEq X] {body : P → Pr P T Q A U}
  {rg : CsR X → Fin T} {ι : Fin 64 → Fin T}

variable (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
include hrg hdisj

/-- **The chirp kernel box of the pipeline.** With the chirp axis tables
(`cstTab_axTab`: the numerators of `axisPhase p g (t k) (s k) j` at scale `2^(p+g)`),
`p + g + 3 ≤ w` and `d ≤ 2^(p+g)`, the stage pushes onto `kr` the numerator box at scale `2^p`
of the chirp kernel `chirpProd p g t s` (`cstNumBox`, address order, axis `0` most
significant), within `cstChirpCost w (List.ofFn t) bp` steps, at most
`∑_{k<d} bp k + 4 d (∏ t_k) cmulCost w` (`cst_chirpCost_le`). -/
theorem cst_chirpBox_pipeline (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (hA : 96 ≤ A) {w p g d : ℕ} (t s : Fin d → ℕ) [∀ i, NeZero (t i)] (hd : 1 ≤ d)
    (hw : p + g + 3 ≤ w) (hdq : d ≤ 2 ^ (p + g)) (prep : Pr P T Q A U)
    (cfg : ℕ → X → List (Fin (A + 4))) (cnt : ℕ → List (Fin (A + 4))) (bp : ℕ → ℕ)
    (hprep : ∀ k < d, ∀ ρ : CsR X → List (Fin (A + 4)), ρ (.c .ys) = [] → ρ .cL = [] →
      (∀ j, ρ (.x j) = cfg k j) →
      RsaRuns body rg ι prep ρ (cstSetX (Function.update (Function.update ρ (.c .ys)
        (cstream A w (cstTab (List.ofFn t) (cstAxTab p g t s) k))) .cL (cnt k)) (cfg (k + 1)))
        (bp k))
    (hcnt : ∀ k (hk : k < d), (cnt k).length = t ⟨k, hk⟩)
    (ρ : CsR X → List (Fin (A + 4))) (hb : CstBase ρ w p g) (hax : (ρ .ax).length + 1 = d)
    (hx : ∀ j, ρ (.x j) = cfg 0 j) :
    RsaRuns body rg ι (cstChirpBox ι hι hT hQ rg prep) ρ
      (cstSetX (Function.update ρ .kr
        (cstream A w (cstNumBox p t (chirpProd p g t s)) ++ ρ .kr)) (cfg d))
      (cstChirpCost w (List.ofFn t) bp) := by
  have hlen : (List.ofFn t).length = d := List.length_ofFn
  have h := cst_chirpBox_runs (body := body) (ι := ι) hrg hdisj hι hT hQ hA (w := w) (p := p)
    (g := g) (by omega) (List.ofFn t) (by omega)
    (by
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      exact Nat.one_le_iff_ne_zero.2 (NeZero.ne (t i)))
    (cstAxTab p g t s) (fun k _ j _ => cst_fits_axTab t s hw k j)
    (fun l _ hl => cst_fits_ent t s hw hdq l (by omega)) (cst_fits_diskC (by omega)) prep cfg cnt
    bp (fun k hk => hprep k (by omega))
    (fun k hk => by
      rw [hcnt k (by omega), cst_getD hk, List.getElem_ofFn])
    ρ hb (by omega) hx
  rw [hlen, ← cstNumBox_chirpProd] at h
  exact h

/-- The instance `Pipeline.chirpKernel n = chirpProd (p n) (chirpGuard (d n)) (t n) (s n)`. -/
theorem cst_chirpBox_kernel (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (hA : 96 ≤ A) (n : ℕ) {w : ℕ} (hd : 1 ≤ Mult.Sizes.d n)
    (hw : Mult.Sizes.p n + chirpGuard (Mult.Sizes.d n) + 3 ≤ w) (prep : Pr P T Q A U)
    (cfg : ℕ → X → List (Fin (A + 4))) (cnt : ℕ → List (Fin (A + 4))) (bp : ℕ → ℕ)
    (hprep : ∀ k < Mult.Sizes.d n, ∀ ρ : CsR X → List (Fin (A + 4)), ρ (.c .ys) = [] →
      ρ .cL = [] → (∀ j, ρ (.x j) = cfg k j) →
      RsaRuns body rg ι prep ρ (cstSetX (Function.update (Function.update ρ (.c .ys)
        (cstream A w (cstTab (List.ofFn (Mult.Sizes.t n))
          (cstAxTab (Mult.Sizes.p n) (chirpGuard (Mult.Sizes.d n)) (Mult.Sizes.t n)
            (Mult.Sizes.s n)) k))) .cL (cnt k)) (cfg (k + 1))) (bp k))
    (hcnt : ∀ k (hk : k < Mult.Sizes.d n), (cnt k).length = Mult.Sizes.t n ⟨k, hk⟩)
    (ρ : CsR X → List (Fin (A + 4)))
    (hb : CstBase ρ w (Mult.Sizes.p n) (chirpGuard (Mult.Sizes.d n)))
    (hax : (ρ .ax).length + 1 = Mult.Sizes.d n) (hx : ∀ j, ρ (.x j) = cfg 0 j) :
    RsaRuns body rg ι (cstChirpBox ι hι hT hQ rg prep) ρ
      (cstSetX (Function.update ρ .kr
        (cstream A w (cstNumBox (Mult.Sizes.p n) (Mult.Sizes.t n) (Mult.Pipeline.chirpKernel n)) ++
          ρ .kr)) (cfg (Mult.Sizes.d n)))
      (cstChirpCost w (List.ofFn (Mult.Sizes.t n)) bp) := by
  have hg := sixteen_mul_le_chirpGuard (Mult.Sizes.d n)
  have hdq : Mult.Sizes.d n ≤ 2 ^ (Mult.Sizes.p n + chirpGuard (Mult.Sizes.d n)) := by
    have : 2 ^ chirpGuard (Mult.Sizes.d n) ≤ 2 ^ (Mult.Sizes.p n + chirpGuard (Mult.Sizes.d n)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact cst_chirpBox_pipeline hrg hdisj hι hT hQ hA (Mult.Sizes.t n) (Mult.Sizes.s n) hd hw hdq
    prep cfg cnt bp hprep hcnt ρ hb hax hx

end Pipeline

end

end IntegerMultBounds.MathlibTM2.Fast.ChirpSt
