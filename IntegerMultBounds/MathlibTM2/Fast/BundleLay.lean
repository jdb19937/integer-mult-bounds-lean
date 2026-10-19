module

public import IntegerMultBounds.MathlibTM2.Fast.DistMain
import IntegerMultBounds.MathlibTM2.Fast.MainCorrect
public import IntegerMultBounds.MathlibTM2.Fast.MainEmbed
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# The distribution machine on the register file of the fast multiplier

The verified distribution machine `dsMain rg g` (`Fast/DistMain`) runs on a parameter layout
`rg : TblR pmNV → Fin T`, the registers of a source transform `M.rg` and its own registers
`io : DsX → Fin T`. This file places it on the register file of `Fast/MainRegs`:

* the layout is `mnPm`, the source registers are `mnM.rg = mnSrc`;
* the converter's own registers `DsX` are parked on the reserved block `mnLay` of the layer
  machine, on the wire temporaries `bdLayX x = wtmp (wireOf (bdIdx x))` (`bdIo`); the whole
  family is `bdG = dsGY mnM.rg bdIo`, a layout (`bdLay : DsLay mnPm bdG`).

`bd_main_exec`: from a store meeting `MnPostParam` at `n` (`Big n`), `dsMain mnPm bdG` runs
within `dsMainCost n` steps to the store with register file `bdR₁ n S.R`: the file
`bdE n = dsSrcE n (dsW n) (dsWW n) _` of the source transform on `mnSrc`, the converter's outputs
`bdO n` on `bdIo`, the parameter layout `bdρ n` as the parameter machine left it, every other
register as it was (`bdR₁_src`, `bdR₁_io`, `bdR₁_pm`, `bdR₁_off`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Filter


noncomputable section

/-- The alphabet of the host, `prime + mnKa` (a notation: `mnLb` is stated at `prime + mnKa`,
and unifying a folded constant against it makes the elaborator evaluate the numerals). -/
notation "bdA" => IntegerMultBounds.Networks.Shared50ModularControl.prime + IntegerMultBounds.MathlibTM2.Fast.Main.mnKa

/-! ### Parking of the converter's registers -/

/-- An enumeration of the converter's own registers. -/
def bdIdx : DsX → Fin 19
  | .uW => 0 | .uw => 1 | .uD => 2 | .tm => 3 | .xT => 4 | .xS => 5 | .tR => 6 | .uq => 7
  | .ut => 8 | .tb => 9 | .tx => 10 | .rR => 11 | .lN => 12 | .lL => 13 | .lK => 14 | .lD => 15
  | .lB => 16 | .lW => 17 | .lE => 18

lemma bdIdx_inj : Function.Injective bdIdx := by
  intro x y h
  cases x <;> cases y <;> first | rfl | (simp [bdIdx] at h)

lemma bd_NW : 19 ≤ NW := by rw [IntegerMultBounds.MathlibTM2.Cost.br_NW_eq]; norm_num

/-- The reserved layer register holding the converter's register `x`: the wire temporary of
wire `bdIdx x`. -/
def bdLayX (x : DsX) : LReg SXReg := .wtmp (.inl (wireOf (Fin.castLE bd_NW (bdIdx x))))

lemma bdLayX_inj : Function.Injective bdLayX := by
  intro x y h
  exact bdIdx_inj (Fin.castLE_injective bd_NW (wireOf.injective (Sum.inl_injective (LReg.wtmp.inj h))))

lemma bdLayX_ne_wire (x : DsX) (v : NWire) : bdLayX x ≠ .wire v := by simp [bdLayX]

lemma bdLayX_ne_park (x : DsX) : bdLayX x ≠ .park := by simp [bdLayX]

/-- The host register of the converter's register `x`. -/
def bdIo (x : DsX) : Fin mnT := mnLay (bdLayX x)

lemma bdIo_inj : Function.Injective bdIo := fun _ _ h => bdLayX_inj (mnLay_inj h)

/-- The family of the source transform and the converter. -/
def bdG : DsY 6 → Fin mnT := dsGY mnM.rg bdIo

@[simp] lemma bdG_s (r : SrcR 6) : bdG (.s r) = mnSrc r := rfl

@[simp] lemma bdG_o (x : DsX) : bdG (.o x) = bdIo x := rfl

lemma bdPm_inj : Function.Injective mnPm := fun _ _ h => MnR.pm.inj (mnRg_inj h)

lemma bdM_ne_io (r : SrcR 6) (x : DsX) : mnM.rg r ≠ bdIo x := mnRg_ne_lay _ _

/-- A stage register that is not a source register is off the family. -/
lemma bdG_ne_rg {r : MnR} (hr : ∀ q, r ≠ .src q) (y : DsY 6) : bdG y ≠ mnRg r := by
  cases y with
  | s q => exact mn_rg_ne (fun h => hr q h.symm)
  | o x => exact (mnRg_ne_lay r _).symm

lemma bdG_ne_pm (r : TblR pmNV) (y : DsY 6) : bdG y ≠ mnPm r := bdG_ne_rg (fun q => by simp) y

lemma bdG_ne_ι (y : DsY 6) (j : Fin 64) : bdG y ≠ mnι j := by
  cases y with
  | s q => exact mnRg_ne_ι _ j
  | o x => exact (mnι_ne_lay j _).symm

/-- A reserved register that is not a parking register is off the family. -/
lemma bdG_ne_lay {x : LReg SXReg} (hx : ∀ y, bdLayX y ≠ x) (y : DsY 6) : bdG y ≠ mnLay x := by
  cases y with
  | s q => exact mnRg_ne_lay _ x
  | o z => exact fun h => hx z (mnLay_inj h)

/-- **The layout.** -/
lemma bdLay : DsLay mnPm bdG :=
  ds_lay mnM bdPm_inj bdIo_inj bdM_ne_io (fun r y => (bdG_ne_pm r y).symm)

/-! ### The files of the distribution machine -/

/-- The register file of the source transform after the distribution machine. -/
def bdE (n : ℕ) : SrcF 6 bdA :=
  if h : 0 < d n then dsSrcE n (dsW n) (dsWW n) h
  else dsSrcE 2 (dsW 2) (dsWW 2) (one_le_d le_rfl)

lemma bdE_of {n : ℕ} (h : 0 < d n) : bdE n = dsSrcE n (dsW n) (dsWW n) h := dite_eq_left h

/-- The base file of `Ã`. -/
def bdV₀ (n : ℕ) : RsaV (RsaX 6) bdA :=
  if h : 0 < d n then dsV₀ n (dsW n) (dsWW n) h
  else dsV₀ 2 (dsW 2) (dsWW 2) (one_le_d le_rfl)

lemma bdV₀_of {n : ℕ} (h : 0 < d n) : bdV₀ n = dsV₀ n (dsW n) (dsWW n) h := dite_eq_left h

/-- The base file of `B̃₀`. -/
def bdσ₀ (n : ℕ) : RsbR ⊕ RsbX 6 → List (Fin (bdA + 4)) :=
  if h : 0 < d n then dsσ₀ n (dsW n) (dsWW n) h
  else dsσ₀ 2 (dsW 2) (dsWW 2) (one_le_d le_rfl)

lemma bdσ₀_of {n : ℕ} (h : 0 < d n) : bdσ₀ n = dsσ₀ n (dsW n) (dsWW n) h := dite_eq_left h

/-- The converter's own outputs: `dsWW n` and `dsW n` ticks on `uW`, `uw`, the layout-stage
parameters `dsSrcO` elsewhere. -/
def bdO (n : ℕ) : DsX → List (Fin (bdA + 4))
  | .uW => List.replicate (dsWW n) tick
  | .uw => List.replicate (dsW n) tick
  | x => dsSrcO n (dsW n) x

lemma bdO_eq {n : ℕ} (hd0 : 0 < d n) (x : DsX) :
    dsFinal (t₀ := 6) (A := bdA) n hd0 (.o x) = bdO n x := by
  cases x <;> rfl

/-- The final family file. -/
def bdFin (n : ℕ) : DsY 6 → List (Fin (bdA + 4))
  | .s r => (bdE n).get r
  | .o x => bdO n x

lemma bdFin_eq {n : ℕ} (hd0 : 0 < d n) : dsFinal (t₀ := 6) (A := bdA) n hd0 = bdFin n := by
  funext y
  cases y with
  | s r => simp only [dsFinal, bdFin, bdE_of hd0]
  | o x => exact bdO_eq hd0 x

/-- The word lists of the parameter layout. -/
abbrev bdWl (n : ℕ) : List (Fin (bdA + 4)) := pmTicks bdA (pmW n)

lemma bdWl_length (n : ℕ) : (bdWl n).length = pmW n := by simp [pmTicks]

/-- The parameter layout as the parameter machine leaves it. -/
abbrev bdρ (n : ℕ) : TblR pmNV → List (Fin (bdA + 4)) :=
  tblRho (pmW n) (bdWl n) (bdWl n) ⟨pmVals n, []⟩

/-- The register file after the distribution machine. -/
def bdR₁ (n : ℕ) (R : Regs mnT bdA) : Regs mnT bdA :=
  dsF mnPm bdG R (bdFin n) (pmW n) (bdWl n) (pmVals n)

lemma bdR₁_eq (n : ℕ) (R : Regs mnT bdA) : bdR₁ n R = dsOv mnPm (dsOv bdG R (bdFin n)) (bdρ n) :=
  rfl

lemma bdR₁_pm (n : ℕ) (R : Regs mnT bdA) (r : TblR pmNV) : bdR₁ n R (mnPm r) = bdρ n r :=
  dsF_rg bdLay R _ _ _ _ r

lemma bdR₁_src (n : ℕ) (R : Regs mnT bdA) (r : SrcR 6) : bdR₁ n R (mnSrc r) = (bdE n).get r :=
  dsF_g bdLay R _ _ _ _ (.s r)

lemma bdR₁_io (n : ℕ) (R : Regs mnT bdA) (x : DsX) : bdR₁ n R (bdIo x) = bdO n x :=
  dsF_g bdLay R _ _ _ _ (.o x)

lemma bdR₁_off (n : ℕ) (R : Regs mnT bdA) {k : Fin mnT} (hk : ∀ r, mnPm r ≠ k)
    (hg : ∀ y, bdG y ≠ k) : bdR₁ n R k = R k :=
  dsF_off R _ _ _ _ hk hg

/-! ### The distribution machine -/

/-- **The distribution machine on the host.** -/
theorem bd_main_exec {body : MnProc → MnPr bdA} {n : ℕ} (hbig : Big n)
    (v : HS mnT mnQ bdA Unit) (S : Stacks mnT bdA) (hP : MnPostParam S.R n) :
    ∃ (v' : HS mnT mnQ bdA Unit) (m : ℕ), m ≤ dsMainCost n ∧
      Exec body (dsMain mnPm bdG) (mk v S) m (mk v' { S with R := bdR₁ n S.R }) := by
  have h := ds_main_runs (body := body) bdLay S.R hbig (bdWl n) (bdWl_length n)
  have e : S.R = dsF mnPm bdG S.R (fun _ => []) (pmW n) (bdWl n) (pmVals n) := by
    funext k
    by_cases hk : ∃ r, mnPm r = k
    · obtain ⟨r, rfl⟩ := hk
      rw [dsF_rg bdLay]
      cases r with
      | v i => exact hP.var i
      | wr => exact hP.wr
      | wn => exact hP.wn
      | acc => exact hP.acc
      | z j => exact hP.z j
    · by_cases hk' : ∃ y, bdG y = k
      · obtain ⟨y, rfl⟩ := hk'
        rw [dsF_g bdLay]
        cases y with
        | s r => exact hP.src r
        | o x => exact hP.lay _
      · push Not at hk hk'
        rw [dsF_off _ _ _ _ _ hk hk']
  obtain ⟨v', m, -, hm, he⟩ := h v S e
  rw [bdFin_eq (srcHd0 hbig)] at he
  exact ⟨v', m, hm, he⟩

end

end IntegerMultBounds.MathlibTM2.Fast.Main
