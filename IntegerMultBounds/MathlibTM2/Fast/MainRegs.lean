module

public import IntegerMultBounds.MathlibTM2.Fast.SrcStage
public import IntegerMultBounds.MathlibTM2.Fast.Round
public import IntegerMultBounds.MathlibTM2.Fast.ParamMachine
public import IntegerMultBounds.MathlibTM2.Fast.Input
public import IntegerMultBounds.MathlibTM2.Fast.Glue
public import IntegerMultBounds.MathlibTM2.Node.TopProc

/-!
# The register file, the procedures and the machine constants of the fast multiplier

The top-level host program of the fast multiplier (`Fast/MainProg`) runs on one register file.
This file fixes it.

**Registers.** `MnR` names the registers of the stages, one family per stage register type:

* `src r` (`r : SrcR 6`): the source transforms (`Fast/SrcStage`), with the CRT box, the
  resampling, chirp, convolution and product families and their transfer registers;
* `pm r` (`r : TblR pmNV`): the parameter machine (`Fast/ParamMachine`);
* `io r` (`r : MnIO`): the input stage, the unary input length, the parameter streams, the digit
  stage (`Fast/Input`), the hold register of the first transform and a spare;
* `rnd r` (`r : RndReg`): the rounding stage (`Fast/Round`);
* `out r` (`r : OReg`): the carries and the output (`Fast/Output`).

The whole file is `MnAll = MnR ⊕ Fin 64 ⊕ LReg CReg`: the stage registers, the 64 registers of
the Schönhage–Strassen multiplier (`Host/SSMul`), and a reserved copy of the register file of the
layer machine (`Node/Regs`) for the synthetic transforms and the parameter distribution. The
host has `mnT = card MnAll` registers, numbered by `mnEq : MnAll ≃ Fin mnT`; the three layouts
`mnRg`, `mnι`, `mnLay` are injective with disjoint images.

`Fintype` instances for the stage register types are given by explicit lists
(`Fintype.ofList`), with the parametric types listed through `Finset.univ.toList` of their
arguments.

**Procedures.** `MnProc` has the main procedure and the layer procedures `LProc` of
`Node/LayerProc` (`MnProc.lay`, injective); `mnBody Lb mainP` runs `mainP` as the main procedure
and `Lb f` as the layer procedure `f`. The layer table `Lb` is a parameter: the layer machine is
a program on `nT CReg` registers, and runs here on the reserved copy, embedded by
`mnLayE : Fin (nT CReg) → Fin mnT` (injective, meeting `mnRg` exactly in `src (.v .io)`, the
layer register `lreg .io` on which the transforms act, and disjoint from `mnι`), so `Lb f` is the
embedded `layerTable hQ ds f` with calls renamed through `MnProc.lay` (`Fast/MainEmbed`).

**Constants.** `mnQ` bounds the states of every simulated multitape program of the stages: the
multiplier `SS.states`, the ring products `rpStates`, the interchanges of the CRT layouts and the
resampling stages (`swapStates crtHd crtPay`) and of the layer (`swapStates sxHd sxPay`). `mnM`
is the `SrcMach` of the source transforms: layout `src`, multiplier `mnι`, headers `crtHd`,
payload `crtPay`, `t₀ = 6`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt IntegerMultBounds.MathlibTM2.Fast.ConvSt
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.LayerMachine

set_option linter.unusedSimpArgs false

noncomputable section

/-! ### `Fintype` instances of the stage register types -/

instance mnFintypeCR : Fintype CR :=
  Fintype.ofList [.xs, .ys, .xsv, .ysv, .acc, .out, .wn, .pn, .nn, .tmp, .u0, .u1, .u2, .u3, .ma,
    .mb, .mc, .md, .sa, .sb, .sc, .sd, .p1, .p2, .p3, .p4, .qr, .qi, .sr, .si]
    (by intro x; cases x <;> simp)

instance mnFintypeRpReg : Fintype RpReg :=
  Fintype.ofList [.xs, .ys, .out, .wn, .sv, .ta, .tb, .acc, .tmp, .d0, .d1, .d2, .d3]
    (by intro x; cases x <;> simp)

instance mnFintypeCvR : Fintype CvR :=
  Fintype.ofList ((Finset.univ : Finset CR).toList.map CvR.cm ++
    (Finset.univ : Finset RpReg).toList.map CvR.rr ++ (Finset.univ : Finset (Fin 91)).toList.map CvR.rpi ++
    [.io, .sy, .so, .t1, .fi, .gi, .fo, .tp, .tm, .shD, .shS, .shR, .shT, .shU])
    (by intro x; cases x <;> simp)

instance mnFintypeCrtReg : Fintype CrtReg :=
  Fintype.ofList [.str, .acc, .tA, .tB, .tc, .tr, .u1, .u2, .zr, .bU, .sig, .msk, .wT, .sT, .mT, .wD,
    .sD, .mD, .wW, .aI, .sI, .muI, .aK, .preU, .postU, .uU, .vU, .vacc, .e3B, .t3B, .tu, .stmp, .rbU,
    .tsU, .lo, .hi, .ov, .nF, .tN, .fc, .sg, .mq, .c0, .c1, .c2, .it, .st, .cy]
    (by intro x; cases x <;> simp)

instance mnFintypeSrcX : Fintype SrcX :=
  Fintype.ofList [.sb, .tr, .cA, .cB, .c1, .c2, .gS, .gR, .gT, .gU, .gD, .lU, .tSp, .sSp]
    (by intro x; cases x <;> simp)

instance mnFintypeRsbR : Fintype RsbR :=
  Fintype.ofList ((Finset.univ : Finset CR).toList.map RsbR.cm ++
    [.src, .dst, .msk, .ms, .mwn, .m2wn, .m2n, .kn, .sn, .smwn, .tswn, .ef, .df, .hf, .tK, .tL, .tJ,
      .tC, .tA, .sr, .sel, .hv, .vk, .b1, .ya, .tb, .xa, .xs, .pr, .hc, .ac, .ac2, .nv, .dout, .bx,
      .bo])
    (by intro x; cases x <;> simp)

instance mnFintypeTblR (k : ℕ) : Fintype (TblR k) :=
  Fintype.ofList ((Finset.univ : Finset (Fin k)).toList.map TblR.v ++ [.wr, .wn, .acc] ++
    (Finset.univ : Finset (Fin 12)).toList.map TblR.z)
    (by intro x; cases x <;> simp)

instance mnFintypeLdcX : Fintype ldcX :=
  Fintype.ofList ((Finset.univ : Finset (TblR 84)).toList.map ldcX.tbl ++
    [.tS, .sS, .pU, .gU, .wU, .tU, .sU])
    (by intro x; cases x <;> simp)

instance mnFintypeCsR (X : Type) [DecidableEq X] [Fintype X] : Fintype (CsR X) :=
  Fintype.ofList ((Finset.univ : Finset CR).toList.map CsR.c ++
    [.cb, .ra, .cL, .cL', .s1, .s2, .ax, .ax', .pn2, .kc, .kr] ++
    (Finset.univ : Finset X).toList.map CsR.x)
    (by intro x; cases x <;> simp)

instance mnFintypeRsaR (X : Type) [DecidableEq X] [Fintype X] : Fintype (RsaR X) :=
  Fintype.ofList ((Finset.univ : Finset CR).toList.map RsaR.c ++
    [.ln, .ob, .sm, .pz, .sm2, .ea, .eb, .er, .cS, .cM, .cP, .cW, .cT, .kW, .kT, .kx, .ka, .kb, .atm,
      .rr, .bS, .bxa, .bya, .bza] ++
    (Finset.univ : Finset X).toList.map RsaR.x)
    (by intro x; cases x <;> simp)

instance mnFintypeRsaX (t₀ : ℕ) : Fintype (RsaX t₀) :=
  Fintype.ofList ((Finset.univ : Finset (Fin (swapT t₀))).toList.map RsaX.sw ++
    [.xt, .ax, .ax', .e1, .e2])
    (by intro x; cases x <;> simp)

instance mnFintypeRsbX (t₀ : ℕ) : Fintype (RsbX t₀) :=
  Fintype.ofList ((Finset.univ : Finset (Fin (swapT t₀))).toList.map RsbX.sw ++
    [.xt, .ax, .ax', .e1, .e2])
    (by intro x; cases x <;> simp)

instance mnFintypeSrcR (t₀ : ℕ) : Fintype (SrcR t₀) :=
  Fintype.ofList ((Finset.univ : Finset (RsaR (RsaX t₀))).toList.map SrcR.a ++
    (Finset.univ : Finset (RsbR ⊕ RsbX t₀)).toList.map SrcR.b ++
    (Finset.univ : Finset (CsR ldcX)).toList.map SrcR.k ++
    (Finset.univ : Finset CvR).toList.map SrcR.v ++
    (Finset.univ : Finset CrtReg).toList.map SrcR.c ++
    (Finset.univ : Finset (Fin (swapT 6))).toList.map SrcR.cb ++
    (Finset.univ : Finset CR).toList.map SrcR.m ++
    (Finset.univ : Finset SrcX).toList.map SrcR.x)
    (by intro x; cases x <;> simp)

instance mnFintypeRndReg : Fintype RndReg :=
  Fintype.ofList [.src, .dst, .wn, .mn, .nn, .sq, .bn, .pn, .wo, .tm, .u1, .sg, .xa, .xc, .cy, .acc,
    .sb, .ns, .pd] (by intro x; cases x <;> simp)

instance mnFintypeOReg : Fintype OReg :=
  Fintype.ofList [.dat, .wr, .br, .ct, .cr, .sm, .acc] (by intro x; cases x <;> simp)

instance mnFintypeLProc : Fintype LProc :=
  ⟨{.layer}, by intro x; cases x; exact Finset.mem_singleton_self _⟩

/-! ### The register file -/

/-- The glue registers: the input temporaries `tx`, `ty` and the bits `rx`, `ry` of the operands;
the unary input length `uN` and its copy spare `ct`; the parameter streams `oT`, `oS`; the unary
`b`, `p`, `w`, `S` of the digit stage (`dbn`, `dpn`, `dwn`, `dsn`) and its scratch `tpl`, `tmp`,
`stmp`, `acc`; the hold register `hx` of the first transform; the transfer spare `sp`. -/
inductive MnIO
  | tx | ty | rx | ry | uN | ct | oT | oS | dbn | dpn | dwn | dsn | tpl | tmp | stmp | acc | hx | sp
  deriving DecidableEq

instance mnFintypeMnIO : Fintype MnIO :=
  Fintype.ofList [.tx, .ty, .rx, .ry, .uN, .ct, .oT, .oS, .dbn, .dpn, .dwn, .dsn, .tpl, .tmp, .stmp,
    .acc, .hx, .sp] (by intro x; cases x <;> simp)

/-- The stage registers: the source transforms, the parameter machine, the glue registers, the
rounding stage and the output stage. -/
inductive MnR
  | src (r : SrcR 6)
  | pm (r : TblR pmNV)
  | io (r : MnIO)
  | rnd (r : RndReg)
  | out (r : OReg)
  deriving DecidableEq

instance mnFintypeMnR : Fintype MnR :=
  Fintype.ofList ((Finset.univ : Finset (SrcR 6)).toList.map MnR.src ++
    (Finset.univ : Finset (TblR pmNV)).toList.map MnR.pm ++
    (Finset.univ : Finset MnIO).toList.map MnR.io ++
    (Finset.univ : Finset RndReg).toList.map MnR.rnd ++
    (Finset.univ : Finset OReg).toList.map MnR.out)
    (by intro x; cases x <;> simp)

/-- The whole register file: the stage registers, the multiplier registers and the reserved copy
of the layer machine's register file. -/
abbrev MnAll := MnR ⊕ Fin 64 ⊕ LReg CReg

/-- The number of host registers. -/
def mnT : ℕ := Fintype.card MnAll

/-- The numbering of the registers. -/
def mnEq : MnAll ≃ Fin mnT := Fintype.equivFin MnAll

/-- The layout of the stage registers. -/
def mnRg (r : MnR) : Fin mnT := mnEq (.inl r)

/-- The registers of the Schönhage–Strassen multiplier. -/
def mnι (j : Fin 64) : Fin mnT := mnEq (.inr (.inl j))

/-- The reserved copy of the layer machine's registers. -/
def mnLay (x : LReg CReg) : Fin mnT := mnEq (.inr (.inr x))

lemma mnRg_inj : Function.Injective mnRg := fun _ _ h => Sum.inl_injective (mnEq.injective h)

lemma mnι_inj : Function.Injective mnι :=
  fun _ _ h => Sum.inl_injective (Sum.inr_injective (mnEq.injective h))

lemma mnLay_inj : Function.Injective mnLay :=
  fun _ _ h => Sum.inr_injective (Sum.inr_injective (mnEq.injective h))

lemma mnRg_ne_ι (r : MnR) (j : Fin 64) : mnRg r ≠ mnι j := fun h => by
  have := mnEq.injective h; simp at this

lemma mnRg_ne_lay (r : MnR) (x : LReg CReg) : mnRg r ≠ mnLay x := fun h => by
  have := mnEq.injective h; simp at this

lemma mnι_ne_lay (j : Fin 64) (x : LReg CReg) : mnι j ≠ mnLay x := fun h => by
  have := mnEq.injective h; simp at this

@[simp] lemma mnRg_eq_iff {r r' : MnR} : mnRg r = mnRg r' ↔ r = r' := mnRg_inj.eq_iff

/-- The register `lreg .io` of the layer machine: the array of the current call, the register the
synthetic transforms read and write. -/
abbrev mnLio : Fin (nT CReg) := reg (BReg := CReg) .io

/-- The layer machine's register file `Fin (nT CReg)` inside the host's: its register `lreg .io`
is the convolution register `src (.v .io)` (the transforms act on it), every other register is the
reserved copy `mnLay` through the numbering `regEquiv`. -/
def mnLayE (i : Fin (nT CReg)) : Fin mnT :=
  if i = mnLio then mnRg (.src (.v .io)) else mnLay ((regEquiv CReg).symm i)

@[simp] lemma mnLayE_io : mnLayE mnLio = mnRg (.src (.v .io)) := if_pos rfl

lemma mnLayE_of_ne {i : Fin (nT CReg)} (h : i ≠ mnLio) :
    mnLayE i = mnLay ((regEquiv CReg).symm i) := if_neg h

lemma mnLayE_inj : Function.Injective mnLayE := by
  intro i j h
  by_cases hi : i = mnLio <;> by_cases hj : j = mnLio
  · rw [hi, hj]
  · rw [mnLayE_of_ne hj, hi, mnLayE_io] at h; exact absurd h (mnRg_ne_lay _ _)
  · rw [mnLayE_of_ne hi, hj, mnLayE_io] at h; exact absurd h.symm (mnRg_ne_lay _ _)
  · rw [mnLayE_of_ne hi, mnLayE_of_ne hj] at h
    exact (regEquiv CReg).symm.injective (mnLay_inj h)

/-- Off `lreg .io`, the layer file is outside the stage registers. -/
lemma mnLayE_ne_rg {i : Fin (nT CReg)} (hi : i ≠ mnLio) (r : MnR) : mnLayE i ≠ mnRg r := by
  rw [mnLayE_of_ne hi]; exact fun h => mnRg_ne_lay r _ h.symm

/-- Every stage register other than `src (.v .io)` is outside the layer file. -/
lemma mnRg_ne_layE {r : MnR} (hr : r ≠ .src (.v .io)) (i : Fin (nT CReg)) :
    mnRg r ≠ mnLayE i := by
  by_cases hi : i = mnLio
  · rw [hi, mnLayE_io]; exact fun h => hr (mnRg_inj h)
  · exact (mnLayE_ne_rg hi r).symm

lemma mnLayE_ne_ι (i : Fin (nT CReg)) (j : Fin 64) : mnLayE i ≠ mnι j := by
  by_cases hi : i = mnLio
  · rw [hi, mnLayE_io]; exact mnRg_ne_ι _ j
  · rw [mnLayE_of_ne hi]; exact fun h => mnι_ne_lay j _ h.symm

/-- Every register is a stage register, a multiplier register or a reserved layer register. -/
lemma mn_reg_cases (k : Fin mnT) :
    (∃ r, k = mnRg r) ∨ (∃ j, k = mnι j) ∨ ∃ x, k = mnLay x := by
  obtain ⟨y, rfl⟩ := mnEq.surjective k
  rcases y with r | j | x
  · exact Or.inl ⟨r, rfl⟩
  · exact Or.inr (Or.inl ⟨j, rfl⟩)
  · exact Or.inr (Or.inr ⟨x, rfl⟩)

lemma mn_card_le_of_inj {α : Type} [Fintype α] {f : α → MnAll} (hf : Function.Injective f) :
    Fintype.card α ≤ mnT :=
  Fintype.card_le_of_injective f hf

lemma mnT_ge_64 : 64 ≤ mnT := by
  have := mn_card_le_of_inj (f := fun j : Fin 64 => (Sum.inr (Sum.inl j) : MnAll))
    (fun _ _ h => by simpa using h)
  simpa using this

lemma mnT_ge_91 : 91 ≤ mnT := by
  have := mn_card_le_of_inj (f := fun j : Fin 91 => (Sum.inl (MnR.src (.v (.rpi j))) : MnAll))
    (fun _ _ h => by simpa using h)
  simpa using this

lemma mnT_ge_swapT : swapT 6 ≤ mnT := by
  have := mn_card_le_of_inj (f := fun j : Fin (swapT 6) => (Sum.inl (MnR.src (.cb j)) : MnAll))
    (fun _ _ h => by simpa using h)
  simpa using this

/-! ### Machine constants -/

/-- The state bound of the simulated multitape programs (one more than the largest
requirement, so that `Fin mnQ` is inhabited). -/
def mnQ : ℕ :=
  max SS.states (max rpStates (max (swapStates crtHd crtPay crtHd_inj)
    (swapStates sxHd sxPay sxHd_inj))) + 1

lemma mnQ_pos : 0 < mnQ := by unfold mnQ; omega

lemma mnQ_ss : SS.states ≤ mnQ := by
  unfold mnQ; exact (le_max_left _ _).trans (Nat.le_add_right _ _)

lemma mnQ_rp : rpStates ≤ mnQ := by
  unfold mnQ; exact ((le_max_left _ _).trans (le_max_right _ _)).trans (Nat.le_add_right _ _)

lemma mnQ_crt : swapStates crtHd crtPay crtHd_inj ≤ mnQ := by
  unfold mnQ
  exact ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans
    (Nat.le_add_right _ _)

lemma mnQ_layer : swapStates sxHd sxPay sxHd_inj ≤ mnQ := by
  unfold mnQ
  exact ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans
    (Nat.le_add_right _ _)

lemma mn_crtHd_ne_pay (k : Fin 5) : crtHd k ≠ crtPay := by
  intro h
  have := congrArg Fin.val h
  simp [crtHd, crtPay] at this
  omega

/-- **The machine constants of the source transforms**: layout `src`, multiplier `mnι`,
interchange headers `crtHd`, payload `crtPay`. -/
def mnM : SrcMach 6 mnT mnQ where
  rg r := mnRg (.src r)
  ι := mnι
  hrg _ _ h := MnR.src.inj (mnRg_inj h)
  hι := mnι_inj
  hdisj _ j := mnRg_ne_ι _ j
  hT := mnT_ge_64
  hT91 := mnT_ge_91
  hQ := mnQ_ss
  hQrp := mnQ_rp
  hd := crtHd
  pay := crtPay
  hi := crtHd_inj
  hdpay := mn_crtHd_ne_pay
  hQs := mnQ_crt
  hTs := mnT_ge_swapT
  hQc := mnQ_crt
  hTc := mnT_ge_swapT

@[simp] lemma mnM_rg (r : SrcR 6) : mnM.rg r = mnRg (.src r) := rfl
@[simp] lemma mnM_ι : mnM.ι = mnι := rfl
@[simp] lemma mnM_hd : mnM.hd = crtHd := rfl

/-! ### Procedures -/

/-- The procedures: the main procedure and the layer procedures. -/
inductive MnProc
  | main
  | lay (f : LProc)

/-- `MnProc` as `Option LProc`, for its `Fintype` instance. -/
def mnProcEquiv : MnProc ≃ Option LProc where
  toFun
    | .main => none
    | .lay f => some f
  invFun
    | none => .main
    | some f => .lay f
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

instance mnFintypeMnProc : Fintype MnProc := Fintype.ofEquiv _ mnProcEquiv.symm

variable {A : ℕ}

/-- Host programs of the fast multiplier. -/
abbrev MnPr (A : ℕ) := Pr MnProc mnT mnQ A Unit

lemma mnProc_lay_inj : Function.Injective MnProc.lay := fun _ _ h => MnProc.lay.inj h

/-- The procedure table: `mainP` as the main procedure, `Lb f` as the layer procedure `f`. -/
def mnBody (Lb : LProc → MnPr A) (mainP : MnPr A) : MnProc → MnPr A
  | .main => mainP
  | .lay f => Lb f

@[simp] lemma mnBody_main (Lb : LProc → MnPr A) (mainP : MnPr A) :
    mnBody Lb mainP .main = mainP := rfl

end

end IntegerMultBounds.MathlibTM2.Fast.Main
