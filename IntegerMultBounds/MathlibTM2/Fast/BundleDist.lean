module

public import IntegerMultBounds.MathlibTM2.Fast.BundleRnd
import IntegerMultBounds.MathlibTM2.Fast.MainStatement
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# The distribution bundle of the fast multiplier

The parameter distribution `distP` of the host program (`Fast/MainProg`, `MnDist`) is assembled
from three parts, run in sequence from the state the parameter machine leaves:

1. the verified distribution machine `dsMain mnPm bdG` on the host's register file
   (`Fast/BundleLay`): the file between runs of the source transform on `mnSrc`, the converter's
   outputs on the parking registers `bdIo`;
2. `bdRnd` (`Fast/BundleRnd`): the unary and binary parameters of the rounding and output stages;
3. a **wires program** `W.prog` (`BdWires σ`), an abstract hypothesis: from the state after 1 and
   2 (`BdPre`), it writes `σ n` on every reserved layer register `mnLay x` and keeps every stage
   register off the parameter layout and the distribution's own glue registers (`bdWKeep`),
   within `W.cost n = O((b n + 1)^k + r n · dsW n)` steps (`r n · dsW n ≤ 576 n`, `bd_r_dsW_le`). The parking registers `bdIo x = mnLay (bdLayX x)`
   hold the converter's outputs `bdO n x` (the unary widths and the layout-stage parameters) when
   `W.prog` starts, and `σ n` afterwards.

**The precondition.** `MnDistSpec` starts from `MnPostParam`, which says nothing about the
registers the distribution writes (`io .dwn`, `rnd .wn`, `rnd .mn`, `rnd .nn`, `rnd .sq`,
`rnd .wo`, `out .wr`). No program of bounded cost can bring a register of unknown content to a
prescribed one, so the contract is met here from `BdPostParam`: `MnPostParam` and those seven
registers empty (`bd_dist_spec`; in the run of `mnFast` they are empty, `MnFront.rest` of
`Fast/MainCorrect`). `bdDist W hP : MnDist mnKa mnLb bdW σ` takes the implication
`MnPostParam → BdPostParam` as its hypothesis `hP`; it becomes a projection once `MnPostParam`
carries the seven facts.

`bd_statement`: `IntegerMultBounds.MathlibTM2.Statement` from `hP`, a layout bundle `L : MnLay bdW` and a wires
program `BdWires (mnσL L)`, through `statement_of_specs`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Pipeline
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open IntegerMultBounds.Schoenhage.Schedule (topN)
open Filter


noncomputable section

/-- The coefficient width of the pipeline: `dsW n`. -/
abbrev bdW (n : ℕ) : ℕ := dsW n

/-! ### The precondition -/

/-- The registers after the parameter machine, with the seven registers the distribution
writes empty. -/
structure BdPostParam (R : Regs mnT bdA) (n : ℕ) : Prop extends MnPostParam R n where
  rnd : ∀ r ∈ bdRndRegs, R (mnRg r) = []

/-! ### The state before the wires program -/

/-- The register file after the distribution machine and `bdRnd`. -/
def bdR₂ (n : ℕ) (R : Regs mnT bdA) : Regs mnT bdA :=
  dsOv mnPm (bdRndF n (dsOv bdG R (bdFin n))) (bdρ n)

section R₂

variable {n : ℕ} {R : Regs mnT bdA}

lemma bdR₂_pm (r : TblR pmNV) : bdR₂ n R (mnPm r) = bdρ n r := dsOv_rg bdPm_inj _ _ r

lemma bdR₂_off {k : Fin mnT} (hk : ∀ r, mnPm r ≠ k) :
    bdR₂ n R k = bdRndF n (dsOv bdG R (bdFin n)) k := dsOv_off _ _ hk

lemma bdR₂_src (r : SrcR 6) : bdR₂ n R (mnSrc r) = (bdE n).get r := by
  rw [bdR₂_off (fun q => bd_pm_ne q (by simp)), bdRndF_rg (by simp [bdRndRegs])]
  exact dsOv_rg bdLay.ig R _ (.s r)

lemma bdR₂_io (x : DsX) : bdR₂ n R (bdIo x) = bdO n x := by
  show bdR₂ n R (mnLay (bdLayX x)) = _
  rw [bdR₂_off (fun q => mnRg_ne_lay _ _), bdRndF_lay]
  exact dsOv_rg bdLay.ig R _ (.o x)

lemma bdR₂_lay {x : LReg SXReg} (hx : ∀ y, bdLayX y ≠ x) : bdR₂ n R (mnLay x) = R (mnLay x) := by
  rw [bdR₂_off (fun q => mnRg_ne_lay _ _), bdRndF_lay, dsOv_off _ _ (bdG_ne_lay hx)]

lemma bdR₂_ι (j : Fin 64) : bdR₂ n R (mnι j) = R (mnι j) := by
  rw [bdR₂_off (fun q => mnRg_ne_ι _ j), bdRndF_ι, dsOv_off _ _ (fun y => bdG_ne_ι y j)]

lemma bdR₂_rg {r : MnR} (hp : ∀ q, r ≠ .pm q) (hs : ∀ q, r ≠ .src q) (hr : r ∉ bdRndRegs) :
    bdR₂ n R (mnRg r) = R (mnRg r) := by
  rw [bdR₂_off (fun q => bd_pm_ne q (hp q)), bdRndF_rg hr, dsOv_off _ _ (bdG_ne_rg hs)]

lemma bdR₂_dwn : bdR₂ n R (mnIo .dwn) = List.replicate (dsW n) tick := by
  rw [bdR₂_off (fun q => bd_pm_ne q (by simp)), bdRndF_dwn]

lemma bdR₂_rwn : bdR₂ n R (mnRnd .wn) = List.replicate (dsW n) tick := by
  rw [bdR₂_off (fun q => bd_pm_ne q (by simp)), bdRndF_rwn]

lemma bdR₂_rmn : bdR₂ n R (mnRnd .mn) = List.replicate (bdMw n) tick := by
  rw [bdR₂_off (fun q => bd_pm_ne q (by simp)), bdRndF_rmn]

lemma bdR₂_rnn : bdR₂ n R (mnRnd .nn) = List.replicate (dsTopN (bdMw n)) tick := by
  rw [bdR₂_off (fun q => bd_pm_ne q (by simp)), bdRndF_rnn]

lemma bdR₂_rsq : bdR₂ n R (mnRnd .sq) = binSyms (bdMw n) (S n * S n) := by
  rw [bdR₂_off (fun q => bd_pm_ne q (by simp)), bdRndF_rsq]

lemma bdR₂_rwo : bdR₂ n R (mnRnd .wo) = List.replicate (bdWo n) tick := by
  rw [bdR₂_off (fun q => bd_pm_ne q (by simp)), bdRndF_rwo]

lemma bdR₂_owr : bdR₂ n R (mnOutR .wr) = List.replicate (bdWo n) tick := by
  rw [bdR₂_off (fun q => bd_pm_ne q (by simp)), bdRndF_owr]

end R₂

/-- **The state before the wires program**: the parameter layout as the parameter machine left
it, the source file `bdE n`, the converter's outputs `bdO n` on the parking registers, every
other reserved layer register empty, the unary length `n` on `uN`, the streams on `oT`, `oS`,
and the rounding and output parameters. -/
structure BdPre (R : Regs mnT bdA) (n : ℕ) : Prop where
  pm : ∀ r, R (mnPm r) = bdρ n r
  src : ∀ r, R (mnSrc r) = (bdE n).get r
  io : ∀ x, R (bdIo x) = bdO n x
  lay : ∀ x, (∀ y, bdLayX y ≠ x) → R (mnLay x) = []
  uN : (R (mnIo .uN)).length = n
  oT : R (mnIo .oT) = pmTStream bdA (pmW n) n
  oS : R (mnIo .oS) = pmSStream bdA (pmW n) n
  dwn : R (mnIo .dwn) = List.replicate (dsW n) tick
  rwn : R (mnRnd .wn) = List.replicate (dsW n) tick
  rmn : R (mnRnd .mn) = List.replicate (bdMw n) tick
  rnn : R (mnRnd .nn) = List.replicate (dsTopN (bdMw n)) tick
  rsq : R (mnRnd .sq) = binSyms (bdMw n) (S n * S n)
  rwo : R (mnRnd .wo) = List.replicate (bdWo n) tick
  owr : R (mnOutR .wr) = List.replicate (bdWo n) tick

theorem bd_pre {n : ℕ} {R : Regs mnT bdA} (hP : BdPostParam R n) : BdPre (bdR₂ n R) n where
  pm := bdR₂_pm
  src := bdR₂_src
  io := bdR₂_io
  lay x hx := by rw [bdR₂_lay hx]; exact hP.lay x
  uN := by rw [bdR₂_rg (by simp) (by simp) (by simp [bdRndRegs])]; exact hP.uN
  oT := by rw [bdR₂_rg (by simp) (by simp) (by simp [bdRndRegs])]; exact hP.oT
  oS := by rw [bdR₂_rg (by simp) (by simp) (by simp [bdRndRegs])]; exact hP.oS
  dwn := bdR₂_dwn
  rwn := bdR₂_rwn
  rmn := bdR₂_rmn
  rnn := bdR₂_rnn
  rsq := bdR₂_rsq
  rwo := bdR₂_rwo
  owr := bdR₂_owr

/-! ### The wires program -/

/-- The stage registers the wires program keeps: everything off the parameter layout and the
distribution's own glue registers `tx`, `ty`, `uN`, `ct`, `oT`, `oS`. -/
def bdWKeep (r : MnR) : Prop :=
  (∀ q, r ≠ .pm q) ∧ r ≠ .io .tx ∧ r ≠ .io .ty ∧ r ≠ .io .uN ∧ r ≠ .io .ct ∧ r ≠ .io .oT ∧
    r ≠ .io .oS

/-- **The wires program**: from a store with empty left stacks and multiplier registers meeting
`BdPre n`, `prog` runs within `cost n` steps (for every main program, with the layer
procedures `mnLb`) to a store with the reserved layer registers holding `σ n`, the multiplier
registers empty and every register of `bdWKeep` unchanged; `cost n = O((b n + 1)^k + r n · dsW n)`
(the park record of `σ n` alone has `≥ 2^ℓ · dsW n` symbols, so the second term cannot be
avoided). -/
structure BdWires (σ : ℕ → LReg SXReg → List (Fin (bdA + 4))) where
  prog : MnPr bdA
  cost : ℕ → ℕ
  spec : ∀ᶠ n in atTop, ∀ mainP : MnPr bdA, ∀ (v : HS mnT mnQ bdA Unit) (S : Stacks mnT bdA),
    (∀ y, S.L y = []) → (∀ j, S.R (mnι j) = []) → BdPre S.R n →
    ∃ (v' : HS mnT mnQ bdA Unit) (S' : Stacks mnT bdA) (m : ℕ), m ≤ cost n ∧
      Exec (mnBody mnLb mainP) prog (mk v S) m (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ (∀ j, S'.R (mnι j) = []) ∧
      (∀ x, S'.R (mnLay x) = σ n x) ∧ ∀ r, bdWKeep r → S'.R (mnRg r) = S.R (mnRg r)
  costBound : ∃ C k : ℕ, ∀ᶠ n in atTop, cost n ≤ C * (b n + 1) ^ k + C * (r n * dsW n)

/-! ### The distribution -/

variable {σ : ℕ → LReg SXReg → List (Fin (bdA + 4))}

/-- **The distribution program**: the distribution machine, the rounding and output parameters,
the wires program. -/
def bdDistP (W : BdWires σ) : MnPr bdA := .seq (.seq (dsMain mnPm bdG) bdRnd) W.prog

/-- The step bound of `bdDistP`. -/
def bdDistCost (W : BdWires σ) (n : ℕ) : ℕ := dsMainCost n + bdRndCost n + W.cost n

/-- A kept register of the distribution contract is off the parameter layout, off the source
registers, off the seven registers of `bdRnd` and kept by the wires program. -/
lemma bd_keep {r : MnR} (hk : mnDistKeep r) :
    (∀ q, r ≠ .pm q) ∧ (∀ q, r ≠ .src q) ∧ r ∉ bdRndRegs ∧ bdWKeep r := by
  cases r with
  | src _ => exact hk.elim
  | pm _ => exact hk.elim
  | io x =>
    simp only [mnDistKeep] at hk
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hk
    simp [bdRndRegs, bdWKeep, h1, h2, h3, h4, h5, h6, h7]
  | rnd x =>
    simp only [mnDistKeep] at hk
    obtain ⟨h1, h2, h3, h4, h5⟩ := hk
    simp [bdRndRegs, bdWKeep, h1, h2, h3, h4, h5]
  | out x =>
    simp only [mnDistKeep] at hk
    simp [bdRndRegs, bdWKeep, hk]

lemma bd_rndRegs_ne_src {r : MnR} (hr : r ∈ bdRndRegs) (q : SrcR 6) : r ≠ .src q := by
  simp only [bdRndRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- **The distribution contract from `BdPostParam`**: `MnDistSpec` with its precondition
strengthened by the seven registers of `bdRnd` empty. -/
theorem bd_dist_spec (W : BdWires σ) : ∀ᶠ n in atTop, ∀ mainP : MnPr bdA,
    ∀ (v : HS mnT mnQ bdA Unit) (S : Stacks mnT bdA), (∀ y, S.L y = []) →
      (∀ j, S.R (mnι j) = []) → BdPostParam S.R n →
      ∃ (v' : HS mnT mnQ bdA Unit) (S' : Stacks mnT bdA) (m : ℕ), m ≤ bdDistCost W n ∧
        Exec (mnBody mnLb mainP) (bdDistP W) (mk v S) m (mk v' S') ∧
        S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ (∀ j, S'.R (mnι j) = []) ∧
        MnDistOut S'.R n (bdW n) (bdE n) (σ n) ∧
        ∀ r, mnDistKeep r → S'.R (mnRg r) = S.R (mnRg r) := by
  filter_upwards [eventually_big, W.spec] with n hbig hW
  intro mainP v S hL hι hP
  -- the distribution machine
  obtain ⟨v₁, m₁, hm₁, he₁⟩ :=
    bd_main_exec (body := mnBody mnLb mainP) hbig v S hP.toMnPostParam
  -- the rounding and output parameters
  have hR' : ∀ r ∈ bdRndRegs, dsOv bdG S.R (bdFin n) (mnRg r) = [] := fun r hr => by
    rw [dsOv_off _ _ (bdG_ne_rg (bd_rndRegs_ne_src hr))]
    exact hP.rnd r hr
  obtain ⟨v₂, m₂, -, hm₂, he₂⟩ := bd_rnd_runs (body := mnBody mnLb mainP) hbig _ hR' v₁
    { S with R := bdR₁ n S.R } (bdR₁_eq n S.R)
  -- the wires program
  obtain ⟨v₃, S₃, m₃, hm₃, he₃, hinp, hout, hL₃, hι₃, hlay, hkeep⟩ :=
    hW mainP v₂ { S with R := bdR₂ n S.R } hL
      (fun j => by show bdR₂ n S.R (mnι j) = []; rw [bdR₂_ι]; exact hι j) (bd_pre hP)
  refine ⟨v₃, S₃, m₁ + m₂ + m₃, ?_, Exec.seq (Exec.seq he₁ he₂) he₃, hinp, hout, hL₃, hι₃,
    ?_, ?_⟩
  · unfold bdDistCost; omega
  · have key : ∀ r : MnR, bdWKeep r → S₃.R (mnRg r) = bdR₂ n S.R (mnRg r) := fun r hr =>
      hkeep r hr
    refine ⟨fun r => ?_, hlay, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [key (.src r) (by simp [bdWKeep]), bdR₂_src]
    · rw [key (.io .dwn) (by simp [bdWKeep]), bdR₂_dwn, List.length_replicate]
    · rw [key (.rnd .wn) (by simp [bdWKeep]), bdR₂_rwn, List.length_replicate]
    · rw [key (.rnd .mn) (by simp [bdWKeep]), bdR₂_rmn, List.length_replicate, bdMw_eq hbig]
    · rw [key (.rnd .nn) (by simp [bdWKeep]), bdR₂_rnn, List.length_replicate, bdMw_eq hbig,
        ds_dsTopN]
    · rw [key (.rnd .sq) (by simp [bdWKeep]), bdR₂_rsq, bdMw_eq hbig]
    · rw [key (.rnd .wo) (by simp [bdWKeep]), bdR₂_rwo, List.length_replicate, bdWo_eq hbig]
    · rw [key (.out .wr) (by simp [bdWKeep]), bdR₂_owr, List.length_replicate, bdWo_eq hbig]
  · intro r hr
    obtain ⟨hp, hs, hn, hw⟩ := bd_keep hr
    rw [hkeep r hw]
    exact bdR₂_rg hp hs hn

/-- The registers the first loaders clear are empty in `bdV₀`. -/
lemma bd_clrA {n : ℕ} (hd0 : 0 < d n) (x : RsaR (RsaX 6)) (hx : x ∈ preClrA crtHd) :
    (bdV₀ n).get x = [] := by
  rw [bdV₀_of hd0]
  simp only [preClrA, preHA, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [dsV₀, RsaV.get, dsSrcEa]

/-- The registers the first band loader clears are empty in `bdσ₀`. -/
lemma bd_clrB {n : ℕ} (hd0 : 0 < d n) (r : RsbR ⊕ RsbX 6) (hr : r ∈ bandClrB crtHd) :
    bdσ₀ n r = [] := by
  rw [bdσ₀_of hd0]
  simp only [bandClrB, preHB, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [dsσ₀, dsSrcEb]

/-- `r n · dsW n ≤ 576 n`: `r ≤ T` (`ℓ ≤ logT`), `dsW ≤ 12 p` and `T p ≤ 48 n`. -/
lemma bd_r_dsW_le : ∀ᶠ n in atTop, r n * dsW n ≤ 576 * n := by
  filter_upwards [eventually_big] with n hbig
  have hn := hbig.1
  have hrT : r n ≤ T n := Nat.pow_le_pow_right (by norm_num) (pm_ℓ_le_logT hn)
  have hw : dsW n ≤ 12 * p n := ds_dsW_le_p hn
  have hTp : T n * p n ≤ 48 * n := by exact_mod_cast IntegerMultBounds.MathlibTM2.Cost.gr_Tp_le hn
  calc r n * dsW n ≤ T n * (12 * p n) := Nat.mul_le_mul hrT hw
    _ = 12 * (T n * p n) := by ring
    _ ≤ 12 * (48 * n) := Nat.mul_le_mul_left 12 hTp
    _ = 576 * n := by ring

/-- **The distribution bundle** from a wires program, under the implication
`MnPostParam → BdPostParam` (see the module docstring). -/
def bdDist (W : BdWires σ)
    (hP : ∀ (R : Regs mnT bdA) (n : ℕ), MnPostParam R n → BdPostParam R n) :
    MnDist mnKa mnLb bdW σ where
  distP := bdDistP W
  Wt := dsWW
  E := bdE
  V₀ := bdV₀
  σ₀ := bdσ₀
  restA _ := []
  restB _ := []
  axsA n := dsAxs n
  axsB n := dsAxs n
  cost := bdDistCost W
  spec := by
    filter_upwards [bd_dist_spec W] with n h
    intro mainP v S hL hι hpost
    exact h mainP v S hL hι (hP _ _ hpost)
  base := by
    filter_upwards [eventually_big] with n hbig
    intro hd0
    have h := (dsAll_base (K := mnKa) (t₀ := 6) mnM hbig).1
    unfold dsRestA dsRestB at h
    rw [bdE_of hd0, bdV₀_of hd0, bdσ₀_of hd0]
    simp only [List.append_nil]
    exact h
  crt := by
    filter_upwards [eventually_big] with n hbig
    rw [bdE_of (srcHd0 hbig)]
    exact (dsAll_base (K := mnKa) (t₀ := 6) mnM hbig).2.1
  ln := by
    filter_upwards [eventually_big] with n hbig
    rw [bdE_of (srcHd0 hbig)]
    exact (dsAll_base (K := mnKa) (t₀ := 6) mnM hbig).2.2.1
  str := by
    filter_upwards [eventually_big] with n hbig
    rw [bdE_of (srcHd0 hbig)]
    exact (dsAll_base (K := mnKa) (t₀ := 6) mnM hbig).2.2.2.1
  sb := by
    filter_upwards [eventually_big] with n hbig
    rw [bdE_of (srcHd0 hbig)]
    exact (dsAll_base (K := mnKa) (t₀ := 6) mnM hbig).2.2.2.2
  clrA := by
    filter_upwards [eventually_big] with n hbig
    intro x hx
    rw [bd_clrA (srcHd0 hbig) x hx]
    exact Nat.zero_le _
  clrB := by
    filter_upwards [eventually_big] with n hbig
    intro r hr
    rw [bd_clrB (srcHd0 hbig) r hr]
    exact Nat.zero_le _
  widths := by
    filter_upwards [eventually_big] with n hbig
    obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := ds_src_widths hbig
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  ratio := ⟨12, 100, by
    filter_upwards [eventually_big] with n hbig
    exact ⟨ds_dsW_le_p hbig.1, ds_dsWW_le_p hbig⟩⟩
  costBound := by
    obtain ⟨C, k, hC⟩ := W.costBound
    refine ⟨10 ^ 10 + 2 * 10 ^ 16 + 576 * C, 5 + k, ?_⟩
    filter_upwards [ds_mainCost_le, bd_rndCost_le, hC, bd_r_dsW_le] with n h1 h2 h3 h4
    have hb : 1 ≤ b n + 1 := by omega
    have e4 : (b n + 1) ^ 4 ≤ (b n + 1) ^ (5 + k) := Nat.pow_le_pow_right hb (by omega)
    have e5 : (b n + 1) ^ 5 ≤ (b n + 1) ^ (5 + k) := Nat.pow_le_pow_right hb (by omega)
    have ek : (b n + 1) ^ k ≤ (b n + 1) ^ (5 + k) := Nat.pow_le_pow_right hb (by omega)
    have f1 := Nat.mul_le_mul_left C ek
    have f2 := Nat.mul_le_mul_left (10 ^ 10) e5
    have f3 := Nat.mul_le_mul_left (2 * 10 ^ 16) e4
    have f4 := Nat.mul_le_mul_left C h4
    have f5 : C * (576 * n) = 576 * C * n := by ring
    have f6 : C * (b n + 1) ^ (5 + k) ≤ 576 * C * (b n + 1) ^ (5 + k) :=
      Nat.mul_le_mul_right _ (by omega)
    show dsMainCost n + bdRndCost n + W.cost n ≤ _
    rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul]
    omega

/-- **The statement** from the implication `MnPostParam → BdPostParam`, a layout bundle and a
wires program. -/
theorem bd_statement
    (hP : ∀ (R : Regs mnT bdA) (n : ℕ), MnPostParam R n → BdPostParam R n)
    (h : ∃ L : MnLay bdW, Nonempty (BdWires (mnσL L))) : IntegerMultBounds.MathlibTM2.Statement := by
  obtain ⟨L, ⟨W⟩⟩ := h
  exact statement_of_specs ⟨bdW, L, ⟨bdDist W hP⟩⟩

end

end IntegerMultBounds.MathlibTM2.Fast.Main
