module
public import IntegerMultBounds.MathlibTM2.Fast.ResampBAll
public import IntegerMultBounds.MathlibTM2.Fast.PrepBase
public import IntegerMultBounds.MathlibTM2.Fast.TableWeight
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.ENatToNat


/-!
# The parameter records of `B̃₀`

The records the loaders of `B̃₀` read: a record (`PreAxB.fields`) is ten unary fields
(`preFld`): `t`, `s`, `m`, `L`, `Ld`, `P`, `G`, `α`, `p`, `W`. `preDB`, `preRecsB` are the
records of the pipeline axes, `preHsB` the interchange headers, `preHB` the header registers.
The pieces of the old Neumann loader still used by the banded loader (`Fast/BandPrep.lean`) stay
here: the row mask program (`preMaskCode`, `preMaskCode_do`, `preMaskE_map`), the headers
(`preHdrB`, `preB_hdr`, `preBankB`), the scratch frame `PreFreeB` and `preLoadB_inl`.
The Neumann loader itself (`preB`, `preB_runs`, `preCfgB`, `preCpB`, `rsbStage_exec`) was
removed with the Neumann `B̃₀`; restore from `1cb2723b`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.Networks.Shared50ModularControl (prime)


noncomputable section

/-! ### The row mask -/

section Mask

open IntegerMultBounds.Resampling

/-- The selected rows `q s t ℓ` increase. -/
lemma pre_q_mono (s t : ℕ) {a b : ℕ} (h : a ≤ b) : RowSelect.q s t a ≤ RowSelect.q s t b := by
  unfold RowSelect.q
  exact Nat.div_le_div_right (by nlinarith)

lemma pre_q_succ {s t : ℕ} (hs : 0 < s) (hst : s ≤ t) (a : ℕ) :
    RowSelect.q s t a + 1 ≤ RowSelect.q s t (a + 1) := by
  unfold RowSelect.q
  have h2 : 0 < 2 * s := by omega
  rw [← Nat.add_div_right _ h2]
  exact Nat.div_le_div_right (by nlinarith)

lemma pre_q_last {s t : ℕ} (hs : 0 < s) : RowSelect.q s t s = t := by
  unfold RowSelect.q
  rw [show 2 * (t * s) + s = s + t * (2 * s) by ring, Nat.add_mul_div_right _ _ (by omega),
    Nat.div_eq_of_lt (by omega), Nat.zero_add]

lemma pre_q_zero {s t : ℕ} (hs : 0 < s) : RowSelect.q s t 0 = 0 := by
  unfold RowSelect.q
  rw [Nat.mul_zero, Nat.mul_zero, Nat.zero_add, Nat.div_eq_of_lt (by omega)]

/-- The mask bit of row `j` as a number. -/
def preBit (s t j : ℕ) : ℕ := if ∃ a < s, RowSelect.q s t a = j then 1 else 0

/-- The emissions of the mask program after `j` rows. -/
def preMaskE (A s t j : ℕ) : List (Fin (A + 4)) :=
  (List.range j).flatMap fun j' => tblPairs A 1 (preBit s t j') 0

/-- The step of the mask program on a selected row: emit a one, advance `ℓ`, and
`q := (2 t ℓ + s) / (2 s)`. -/
def preMaskHit : TblCode 48 :=
  tblBlock 48 [.emit 6 7, .inc 1, .mul 4 1 5, .add 5 34 5] (.div 5 3 2)

/-- The mask program: for `j < t`, the bit of row `j` (`s` in variable `34`, `t` in `35`). The
next selected row `q ℓ` is kept in variable `2`, `ℓ` in `1`. -/
def preMaskCode : TblCode 48 :=
  tblBlock 48 [.zero 1, .zero 2, .add 34 34 3, .add 35 35 4, .zero 6, .inc 6] (.zero 7) ;;
  tblFor 0 35 (.ite 0 2 (.ins (.emit 7 7)) preMaskHit)

/-- The invariant of the mask loop before row `j`. -/
def PreMaskInv (A s t : ℕ) (j : ℕ) (st : TblSt 48 A) : Prop :=
  ∃ a, st.val 1 = a ∧ st.val 2 = RowSelect.q s t a ∧ st.val 3 = 2 * s ∧ st.val 4 = 2 * t ∧
    st.val 6 = 1 ∧ st.val 7 = 0 ∧ st.val 34 = s ∧ st.val 35 = t ∧ j ≤ RowSelect.q s t a ∧
    a ≤ s ∧ (∀ a' < a, RowSelect.q s t a' < j) ∧ st.acc = (preMaskE A s t j).reverse

theorem preMaskCode_do {A W : ℕ} (st : TblSt 48 A) {s t : ℕ} (hs' : st.val 34 = s)
    (ht' : st.val 35 = t) (hs : 0 < s) (hst : s < t) (hacc : st.acc = [])
    (hW : 4 * t * (s + 1) < 2 ^ W) :
    TblDo A W 1 preMaskCode st (fun s' => s'.acc = (preMaskE A s t t).reverse)
      (7 + (1 + (t * (6 + 1 + 2) + 2))) := by
  have hq : ∀ a ≤ s, RowSelect.q s t a ≤ t := fun a ha =>
    (pre_q_mono s t ha).trans (pre_q_last hs).le
  have hb1 : 2 * t + 2 * s + 1 < 2 ^ W := by nlinarith
  have hW0 : W ≠ 0 := by rintro rfl; simp at hb1
  refine (TblDo.block _ _ ?_ rfl).seq (fun s₁ hs₁ => ?_)
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hs', ht']
    and_intros <;> omega
  subst hs₁
  refine TblDo.for t 6 (by simp [tblExactList, TblIns.exact, ht']) (by omega) (by decide)
    (PreMaskInv A s t) ?_ ?_ ?_
  · refine ⟨0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [tblExactList, TblIns.exact, hs', ht', hacc, preMaskE, pre_q_zero hs]
    all_goals ring
  · intro j hj s₂ hinv hj0 h35'
    obtain ⟨a, h1, h2, h3, h4, h6, h7, h34, h35, hja, has, hlt, hacc₂⟩ := hinv
    have hqa := hq a has
    by_cases hlt' : j < RowSelect.q s t a
    · -- row `j` is not selected
      have hbit : preBit s t j = 0 := by
        unfold preBit
        rw [ite_eq_right]
        rintro ⟨a', ha', e⟩
        rcases Nat.lt_or_ge a' a with h | h
        · have := hlt a' h; omega
        · have := pre_q_mono s t h; omega
      refine TblDo.mono (TblDo.iteT (by rw [hj0, h2]; exact hlt')
        (TblDo.insX (.emit 7 7) trivial (P := fun s' => s'.val 0 = j ∧ s'.val 35 = t ∧
          PreMaskInv A s t (j + 1) ⟨Function.update s'.val 0 (j + 1), s'.acc⟩) ?_))
        (fun _ h => h) (by omega)
      refine ⟨by simp [TblIns.exact, hj0], by simp [TblIns.exact, h35'], a, ?_⟩
      simp only [TblIns.exact]
      refine ⟨by simp [h1], by simp [h2], by simp [h3], by simp [h4], by simp [h6], by simp [h7],
        by simp [h34], by simp [h35], by omega, has, fun a' ha' => by have := hlt a' ha'; omega,
        ?_⟩
      simp [hacc₂, preMaskE, List.range_succ, hbit, h7]
    · -- row `j` is the selected row `q a`
      have hqj : RowSelect.q s t a = j := by omega
      have has' : a < s := by
        rcases Nat.lt_or_ge a s with h | h
        · exact h
        · have : a = s := by omega
          subst this; rw [pre_q_last hs] at hqj; omega
      have hbit : preBit s t j = 1 := by
        unfold preBit; rw [ite_eq_left ⟨a, has', hqj⟩]
      have hsucc := pre_q_succ hs hst.le a
      have hqa1 := hq (a + 1) has'
      have hm1 : 2 * t * (a + 1) + s < 2 ^ W := by
        have : 2 * t * (a + 1) ≤ 2 * t * s := Nat.mul_le_mul_left _ has'
        nlinarith
      refine TblDo.mono (TblDo.iteF (by rw [hj0, h2]; exact hlt')
        (TblDo.block _ _ ?_ (P := fun s' => s'.val 0 = j ∧ s'.val 35 = t ∧
          PreMaskInv A s t (j + 1) ⟨Function.update s'.val 0 (j + 1), s'.acc⟩) ?_))
        (fun _ h => h) (by simp)
      · simp (config := { decide := true }) [tblFitsList, TblIns.fits, TblIns.exact,
          h1, h4, h34]
        exact ⟨by omega, by nlinarith, by nlinarith⟩
      · have hq1 : (2 * t * (a + 1) + s) / (2 * s) = RowSelect.q s t (a + 1) := by
          unfold RowSelect.q; ring_nf
        refine ⟨by simp (config := { decide := true }) [tblExactList, TblIns.exact,
            hj0],
          by simp (config := { decide := true }) [tblExactList, TblIns.exact,
            h35'], a + 1, ?_⟩
        simp (config := { decide := true }) only [tblExactList, TblIns.exact,
          Function.update_apply, List.cons_append, List.nil_append, ite_true, ite_false]
        refine ⟨by simp [h1], ?_, by simp [h3], by simp [h4], by simp [h6], by simp [h7],
          by simp [h34], by simp [h35], by omega, by omega, ?_, ?_⟩
        · simp [h1, h3, h4, h34, ← hq1]
        · intro a' ha'
          rcases Nat.lt_or_ge a' a with h | h
          · have := hlt a' h; omega
          · have : a' = a := by omega
            subst this; omega
        · simp [hacc₂, preMaskE, List.range_succ, hbit, h6, h7]
  · rintro s₂ ⟨a, -, -, -, -, -, -, -, -, -, -, -, hacc₂⟩ - -
    exact hacc₂

end Mask

/-! ### The halving constant -/

section Half

/-- `2^(p-1)` emitted as a real coefficient (`p` in variable `19`). -/
def preHfCode : TblCode 48 :=
  tblBlock 48 [.zero 1, .inc 1] (.sub 19 1 2) ;; tblPow2 3 2 4 ;; tblBlock 48 [.zero 5] (.emit 3 5)

theorem preHfCode_do {A W w : ℕ} (st : TblSt 48 A) {p : ℕ} (hp' : st.val 19 = p) (hp : 1 ≤ p)
    (hpW : p < W) (hacc : st.acc = []) :
    TblDo A W w preHfCode st (fun s' => s'.acc = (tblPairs A w (2 ^ (p - 1)) 0).reverse)
      (3 + ((4 * (p - 1) + 5) + 2)) := by
  have hpw : p < 2 ^ W := lt_trans hpW Nat.lt_two_pow_self
  refine (TblDo.block _ _ ?_ rfl).seq (fun s₁ hs₁ => ?_)
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hp']
    omega
  subst hs₁
  have h2 : (tblExactList A w ([.zero 1, .inc 1] ++ [.sub 19 1 2]) st).val 2 = p - 1 := by
    simp (config := { decide := true }) [tblExactList, TblIns.exact, hp']
  have hacc₁ : (tblExactList A w ([.zero 1, .inc 1] ++ [.sub 19 1 2]) st).acc = [] := by
    simp [tblExactList, TblIns.exact, hacc]
  refine TblDo.mono ((tblPow2_do (A := A) (W := W) (w := w) (c := (3 : Fin 48)) (e := 2) (i := 4)
    (by decide) (by decide) (by decide)
    (tblExactList A w ([.zero 1, .inc 1] ++ [.sub 19 1 2]) st)
    (by rw [h2]; omega)).seq (K₂ := 2) (fun s₂ hs₂ => ?_)) (fun _ h => h) (by rw [h2])
  obtain ⟨h3, -, -, hacc₂⟩ := hs₂
  rw [h2] at h3
  refine TblDo.block _ _ (by simp [tblFitsList, TblIns.fits]) ?_
  simp (config := { decide := true }) [tblExactList, TblIns.exact, h3,
    hacc₂, hacc]

end Half

/-! ### Records and programs -/

/-- The per-axis parameters of `B̃₀` read by the loader. -/
structure PreAxB where
  /-- the target length -/
  t : ℕ
  /-- the source length -/
  s : ℕ
  /-- the off-diagonal window -/
  m : ℕ
  /-- the target width -/
  L : ℕ
  /-- the target width of the last axis -/
  Ld : ℕ
  /-- the product of the target lengths before the axis -/
  P : ℕ
  /-- the product of the target lengths strictly between the axis and the last axis -/
  G : ℕ
  /-- the table parameter `α` -/
  α : ℕ
  /-- the table precision -/
  p : ℕ
  /-- the word size of the table machine -/
  W : ℕ

/-- The fields of a record, in reading order. -/
def PreAxB.fields (D : PreAxB) : List ℕ := [D.t, D.s, D.m, D.L, D.Ld, D.P, D.G, D.α, D.p, D.W]

/-- The canonical headers of the interchange of the axis with the last axis. -/
def PreAxB.hs (D : PreAxB) (w : ℕ) : Fin 5 → List Bool :=
  fun k => sxBits (swapValues D.P D.G (3 * w) D.L D.Ld k)

variable {t₀ T Q K : ℕ} {U F : Type}

/-- The header register `k` of the interchange bank. -/
def preHB (hd : Fin 5 → Fin t₀) (k : Fin 5) : RsbR ⊕ RsbX t₀ := .inr (.sw (reg (hd k)))

/-- Pair symbols of emission width one to bit symbols. -/
def preBitOf {A : ℕ} (x : Fin (A + 4)) : Fin (A + 4) := bitSymbol (decide (x = pairSym A true false))

section Prog

variable (g : RsbR ⊕ RsbX t₀ → Fin T) (ι : Fin 64 → Fin T) (hd : Fin 5 → Fin t₀)

/-- The five interchange headers. -/
def preHdrB : Pr F T Q (prime + K) U :=
  .seq (umul 3 (g (.inl (.cm .wn))) (g (.inl .tL)) (g (.inl .ac2)))
  (.seq (preHdr (g (.inl .xs)) (g (preHB hd 0)) (g (.inl .ac2)) (g (.inl .nv)))
  (.seq (preHdr (g (.inl .pr)) (g (preHB hd 1)) (g (.inl .ac2)) (g (.inl .nv)))
  (.seq (preHdr (g (.inl .tL)) (g (preHB hd 2)) (g (.inl .ac2)) (g (.inl .nv)))
  (.seq (preHdr (g (.inl .tb)) (g (preHB hd 3)) (g (.inl .ac2)) (g (.inl .nv)))
  (.seq (preHdr (g (.inl .xa)) (g (preHB hd 4)) (g (.inl .ac2)) (g (.inl .nv)))
    (uclear (g (.inl .tL))))))))

end Prog

/-! ### Register files -/

section Files

variable {A : ℕ}

/-- The register file of the stage with the table machine empty. -/
def preStB (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) :
    (RsbR ⊕ RsbX t₀) ⊕ TblR 48 → List (Fin (A + 4)) :=
  Sum.elim σ fun _ => []

/-- The bank with the headers `hs`. -/
def preBankB (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (hd : Fin 5 → Fin t₀)
    (hs : Fin 5 → List Bool) : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))
  | .inl r => σ (.inl r)
  | .inr (.sw j) => if ∃ k, reg (hd k) = j then rsbBank hd hs j else σ (.inr (.sw j))
  | .inr .xt => σ (.inr .xt)
  | .inr .ax => σ (.inr .ax)
  | .inr .ax' => σ (.inr .ax')
  | .inr .e1 => σ (.inr .e1)
  | .inr .e2 => σ (.inr .e2)
  | .inr (.vx j) => σ (.inr (.vx j))

/-- The step bound of step 4. -/
def preHdrCostB (D : PreAxB) (w : ℕ) : ℕ :=
  (4 * w + 4) + (16 * D.P + 5) + (16 * D.G + 5) + (16 * (3 * w) + 5) + (16 * D.L + 5) +
    (16 * D.Ld + 5) + (2 * (3 * w) + 2)

def preKD (D : PreAxB) : ℕ := D.s * (310 * D.p + 123) + (160 * D.p + 450)
def preKM (D : PreAxB) : ℕ := 7 + (1 + (D.t * (6 + 1 + 2) + 2))

/-- The register file after loading the axis `D` from `σ` (coefficient width `w`, the rest
`rest` of the parameter register). -/
def preLoadB (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (hd : Fin 5 → Fin t₀) (w : ℕ)
    (D : PreAxB) (rest : List (Fin (A + 4))) : RsbR ⊕ RsbX t₀ → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (preBankB σ hd (D.hs w))
    (.inl .bo) rest)
    (.inl .sn) (List.replicate D.s tick))
    (.inl (.cm .pn)) (List.replicate D.p tick))
    (.inl .mwn) (List.replicate (D.m * w) tick))
    (.inl .m2wn) (List.replicate (2 * (D.m * w)) tick))
    (.inl .m2n) (List.replicate (2 * D.m) tick))
    (.inl .smwn) (List.replicate ((D.s - D.m) * w) tick))
    (.inl .tswn) (List.replicate ((D.t - D.s) * w) tick))
    (.inl .kn) (List.replicate (D.α * D.α) tick))
    (.inl .ef) (tblStreamE A w D.s D.t D.α D.p D.m))
    (.inl .df) (tblStreamD A w D.s D.t D.α D.p))
    (.inl .hf) (tblPairs A w (2 ^ (D.p - 1)) 0))
    (.inl .msk) ((preMaskE A D.s D.t D.t).map preBitOf)

/-- The scratch registers of the loader are empty. -/
structure PreFreeB (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) : Prop where
  ya : σ (.inl .ya) = []
  b1 : σ (.inl .b1) = []
  tb : σ (.inl .tb) = []
  xa : σ (.inl .xa) = []
  xs : σ (.inl .xs) = []
  pr : σ (.inl .pr) = []
  hc : σ (.inl .hc) = []
  ac : σ (.inl .ac) = []
  ac2 : σ (.inl .ac2) = []
  nv : σ (.inl .nv) = []
  tC : σ (.inl .tC) = []
  tA : σ (.inl .tA) = []
  tJ : σ (.inl .tJ) = []
  tL : σ (.inl .tL) = []
  tK : σ (.inl .tK) = []
  sr : σ (.inl .sr) = []
  sel : σ (.inl .sel) = []

end Files

/-! ### Steps -/

section Steps

variable {body : F → Pr F T Q (prime + K) U} {g : RsbR ⊕ RsbX t₀ → Fin T} {ι : Fin 64 → Fin T}

variable (hg : Function.Injective g) (hι : Function.Injective ι) (hdisj : ∀ r j, g r ≠ ι j)
include hg hι hdisj

omit hg hι hdisj in
lemma preLayB_map (l : List (RsbR ⊕ RsbX t₀)) :
    (l.map Sum.inl).map (preLay g ι) = l.map g := by
  simp [List.map_map, Function.comp_def, preLay]

theorem preB_hdr {hd : Fin 5 → Fin t₀} (hdi : Function.Injective hd)
    (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB) (w : ℕ)
    (hxs : σ (.inl .xs) = List.replicate D.P tick) (hpr : σ (.inl .pr) = List.replicate D.G tick)
    (htb : σ (.inl .tb) = List.replicate D.L tick) (hxa : σ (.inl .xa) = List.replicate D.Ld tick)
    (hwn : (σ (.inl (.cm .wn))).length = w) (htL : σ (.inl .tL) = []) (hac2 : σ (.inl .ac2) = [])
    (hnv : σ (.inl .nv) = []) (hH : ∀ k, σ (.inr (.sw (reg (hd k)))) = []) :
    TwRuns body (preLay g ι) (preHdrB g hd) (preStB σ) (preStB (preBankB σ hd (D.hs w)))
      (preHdrCostB D w) := by
  have htg := preLay_inj hg hι hdisj
  have hinj : ∀ a b, reg (hd a) = reg (hd b) ↔ a = b := fun a b =>
    ⟨fun e => hdi (swapReg_injective e), fun e => e ▸ rfl⟩
  refine twRuns_congr (twRuns_mono
    (twRuns_seq (twRuns_umul (body := body) htg 3 (a := .inl (.inl (.cm .wn))) (b := .inl (.inl .tL))
      (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) (preStB σ) ?_)
    (twRuns_seq (preHdr_runs (body := body) htg (src := .inl (.inl .xs)) (h := .inl (preHB hd 0))
      (t₁ := .inl (.inl .ac2)) (t₂ := .inl (.inl .nv)) (by simp [preHB]) _ ?_ ?_ ?_)
    (twRuns_seq (preHdr_runs (body := body) htg (src := .inl (.inl .pr)) (h := .inl (preHB hd 1))
      (t₁ := .inl (.inl .ac2)) (t₂ := .inl (.inl .nv)) (by simp [preHB]) _ ?_ ?_ ?_)
    (twRuns_seq (preHdr_runs (body := body) htg (src := .inl (.inl .tL)) (h := .inl (preHB hd 2))
      (t₁ := .inl (.inl .ac2)) (t₂ := .inl (.inl .nv)) (by simp [preHB]) _ ?_ ?_ ?_)
    (twRuns_seq (preHdr_runs (body := body) htg (src := .inl (.inl .tb)) (h := .inl (preHB hd 3))
      (t₁ := .inl (.inl .ac2)) (t₂ := .inl (.inl .nv)) (by simp [preHB]) _ ?_ ?_ ?_)
    (twRuns_seq (preHdr_runs (body := body) htg (src := .inl (.inl .xa)) (h := .inl (preHB hd 4))
      (t₁ := .inl (.inl .ac2)) (t₂ := .inl (.inl .nv)) (by simp [preHB]) _ ?_ ?_ ?_)
      (twRuns_uclear (body := body) htg (.inl (.inl .tL)) _))))))) ?_) ?_
  all_goals try (simp (config := { decide := true }) only [preStB, preHB, Function.update_apply,
    Sum.elim_inl, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_false, ite_true, 
    RsbX.sw.injEq, hinj, hxs, hpr, htb, hxa, hwn, htL, hac2, hnv, hH, List.append_nil,
    List.length_replicate]; done)
  · simp (config := { decide := true }) only [preStB, preHB, Function.update_apply,
      Sum.elim_inl, Sum.inl.injEq, reduceCtorEq, ite_false, ite_true, 
      hxs, hpr, htb, hxa, hwn, htL, List.append_nil,
      List.length_replicate]
    unfold preHdrCostB
    exact le_of_eq (by ring)
  · funext r
    rcases r with (r | x) | y
    · cases r <;> simp only [Function.update_apply, preStB, preHB, preBankB, Sum.elim_inl,
        Sum.inl.injEq, reduceCtorEq, ite_false, ite_true]
      all_goals simp [htL]
    · simp only [Function.update_apply, preStB, preHB, Sum.elim_inl, Sum.inl.injEq,
        reduceCtorEq, ite_false, ite_true]
      rcases x with j | _ | _ | _ | _ | _
      · by_cases hj : ∃ k, reg (hd k) = j
        · obtain ⟨k, rfl⟩ := hj
          fin_cases k <;> simp (config := { decide := true }) [preBankB, hinj, rsbBank_hd hdi,
            PreAxB.hs, swapValues, hxs, hpr, htb, hxa, hwn, htL]
        · have hne : ∀ k, j ≠ reg (hd k) := fun k h => hj ⟨k, h.symm⟩
          simp [preBankB, hj, hne]
      all_goals simp [preBankB]
    · simp only [Function.update_apply, reduceCtorEq, ite_false, preStB, Sum.elim_inr]

omit hg hι hdisj in
theorem twRuns_moveRf {R : Type} [DecidableEq R] {tg : R → Fin T} (htg : Function.Injective tg)
    {a b : R} (hab : a ≠ b) (f : Fin (prime + K + 4) → Fin (prime + K + 4))
    (ρ : R → List (Fin (prime + K + 4))) :
    TwRuns body tg (moveR (tg a) (tg b) f) ρ
      (Function.update (Function.update ρ a []) b (((ρ a).map f).reverse ++ ρ b))
      (2 * (ρ a).length + 2) := by
  intro v S hS
  obtain ⟨v', hu, he⟩ := moveR_exec body (tg a) (tg b) (htg.ne hab) f v S
  refine ⟨v', _, _, hu, by rw [hS], he, ?_, ⟨rfl, rfl, rfl, fun k hk => ?_⟩⟩
  · have h1 := twHolds_upd htg (twHolds_upd htg hS a []) b (((ρ a).map f).reverse ++ ρ b)
    simp only [movedR]
    rw [hS a, hS b]
    exact h1
  · simp only [movedR, tw_upd_off _ _ _ hk]

omit hg hι hdisj in
lemma pre_W_facts {D : PreAxB} (hα : 2 ≤ D.α) (hs : 0 < D.s) (hst : D.s < D.t)
    (hW : D.α ^ 2 * ((D.s + D.t) * (D.m + 1)) ^ 2 * 2 ^ (13 * D.p + 8) < 2 ^ D.W) :
    D.s < 2 ^ D.W ∧ D.t < 2 ^ D.W ∧ D.α < 2 ^ D.W ∧ D.m < 2 ^ D.W ∧ D.p < D.W ∧
      D.α ^ 2 * (D.s + D.t) ^ 2 * 2 ^ (13 * D.p + 8) < 2 ^ D.W ∧
      4 * D.t * (D.s + 1) < 2 ^ D.W := by
  obtain ⟨h1, -, h3, h4⟩ := tbl_W_facts hα (Nat.mul_pos (by omega) (Nat.succ_pos D.m)) hW
  set N := (D.s + D.t) * (D.m + 1) with hN
  have hN1 : 1 ≤ N := Nat.mul_pos (by omega) (Nat.succ_pos D.m)
  have hsN : D.s + D.t ≤ N := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hmN : D.m + 1 ≤ N := Nat.le_mul_of_pos_left _ (by omega)
  have hNN : N ≤ N * N := Nat.le_mul_self N
  have hαα : D.α ≤ D.α * D.α * (N * N) := by nlinarith
  have hsq : (D.s + D.t) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hsN 2
  have hD : D.α ^ 2 * (D.s + D.t) ^ 2 * 2 ^ (13 * D.p + 8) < 2 ^ D.W :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsq)) hW
  have h4t : 4 * D.t * (D.s + 1) ≤ D.α * D.α * (N * N) := by
    have : D.t * (D.s + 1) ≤ N * N := Nat.mul_le_mul (by omega) (by omega)
    have : 4 ≤ D.α * D.α := by nlinarith
    nlinarith
  exact ⟨by omega, by omega, by omega, by omega, by omega, hD, lt_of_le_of_lt h4t h4⟩

omit hg hι hdisj in
lemma length_preMaskE (A s t j : ℕ) : (preMaskE A s t j).length = j := by
  simp [preMaskE, tblPairs, coeffSyms, List.length_flatMap]

omit hg hι hdisj in
lemma preMaskE_map {A : ℕ} (hA : 3 ≤ A) (s t : ℕ) :
    (preMaskE A s t t).map preBitOf = (rsbMask s t).map bitSymbol := by
  have hne : (pairSym A false false : Fin (A + 4)) ≠ pairSym A true false := by
    simp only [pairSym, ne_eq, Fin.mk.injEq, Bool.toNat_false, Bool.toNat_true]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have key : ∀ j, tblPairs A 1 (preBit s t j) 0 =
      [pairSym A (decide (∃ a < s, Resampling.RowSelect.q s t a = j)) false] := by
    intro j
    unfold preBit tblPairs coeffSyms
    split_ifs with h
    · simp [h]; rfl
    · simp [h]
  unfold preMaskE rsbMask
  simp only [key, ← List.map_eq_flatMap, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply, preBitOf]
  by_cases h : ∃ a < s, Resampling.RowSelect.q s t a = j
  · simp [h]
  · simp [h, hne]

omit hg hι hdisj in
lemma preStB_upd {A : ℕ} (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (r : RsbR ⊕ RsbX t₀)
    (x : List (Fin (A + 4))) :
    Function.update (preStB σ) (.inl r) x = preStB (Function.update σ r x) := by
  simp only [preStB, Sum.update_elim_inl]

omit hg hι hdisj in
lemma preStB_inl {A : ℕ} (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (r : RsbR ⊕ RsbX t₀) :
    preStB σ (.inl r) = σ r := rfl

end Steps

/-! ### Consecutive loads -/

section Glue

open IntegerMultBounds.Schoenhage.Schedule (topN)
open IntegerMultBounds.Resampling.WeightTable (tableE tableD)

variable {A : ℕ}

lemma rsbWith_inl_ne (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (l a a' : List (Fin (A + 4)))
    {r : RsbR} (hr : r ≠ .src) : rsbWith σ l a a' (.inl r) = σ (.inl r) := by
  simp only [rsbWith, Sum.elim_inl, Function.update_of_ne hr]

lemma preLoadB_inl (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (hd : Fin 5 → Fin t₀) (w : ℕ)
    (D : PreAxB) (rest : List (Fin (A + 4))) {r : RsbR} (h1 : r ≠ .bo) (h2 : r ≠ .sn)
    (h3 : r ≠ .cm .pn) (h4 : r ≠ .mwn) (h5 : r ≠ .m2wn) (h6 : r ≠ .m2n) (h7 : r ≠ .smwn)
    (h8 : r ≠ .tswn) (h9 : r ≠ .kn) (h10 : r ≠ .ef) (h11 : r ≠ .df) (h12 : r ≠ .hf)
    (h13 : r ≠ .msk) : preLoadB σ hd w D rest (.inl r) = σ (.inl r) := by
  simp only [preLoadB, Function.update_apply, Sum.inl.injEq, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h13, ite_false, preBankB]

lemma PreFreeB.rsbWith {σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))} (h : PreFreeB σ)
    (l a a' : List (Fin (A + 4))) : PreFreeB (rsbWith σ l a a') := by
  constructor <;> rw [rsbWith_inl_ne _ _ _ _ (by decide)]
  exacts [h.ya, h.b1, h.tb, h.xa, h.xs, h.pr, h.hc, h.ac, h.ac2, h.nv, h.tC, h.tA, h.tJ, h.tL,
    h.tK, h.sr, h.sel]

lemma PreFreeB.load {σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))} (h : PreFreeB σ)
    (hd : Fin 5 → Fin t₀) (w : ℕ) (D : PreAxB) (r : List (Fin (A + 4))) :
    PreFreeB (preLoadB σ hd w D r) := by
  constructor <;> rw [preLoadB_inl _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)]
  exacts [h.ya, h.b1, h.tb, h.xa, h.xs, h.pr, h.hc, h.ac, h.ac2, h.nv, h.tC, h.tA, h.tJ, h.tL,
    h.tK, h.sr, h.sel]

/-- The stream of `tblStreamDCode` is the diagonal table stream of the line machine. -/
theorem tblStreamD_cstream (w s t α p : ℕ) :
    tblStreamD A w s t α p = cstream A w (rsbArr fun ℓ => rsbReal (tableD s t α p ℓ)) := by
  simp only [tblStreamD, rsbArr, cstream, List.flatMap_map]
  rfl

end Glue


/-! ### The stage -/

section Stage

open IntegerMultBounds.MathlibTM2.Mult.Pipeline IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.NLogN
open IntegerMultBounds.Resampling.WeightTable (tableE tableD)

/-- The record of step `k` (axis `d - 1 - k`) of the pipeline at length `n`, word size `W`. -/
def preDB (n W : ℕ) (hd0 : 0 < d n) (k : ℕ) : PreAxB where
  t := t n (rsbAx hd0 k)
  s := s n (rsbAx hd0 k)
  m := Mult.FastB0.fastWindow (p n) (alpha n)
  L := Nat.log 2 (t n (rsbAx hd0 k))
  Ld := Nat.log 2 (t n (rsbAx hd0 0))
  P := rsbPre (t n) (rsbAx hd0 k)
  G := rsbMid (t n) (rsbAx hd0 k)
  α := alpha n
  p := p n
  W := W

/-- The parameter stream from step `j` on. -/
def preRecsB {A : ℕ} (n W : ℕ) (hd0 : 0 < d n) (j : ℕ) : List (Fin (A + 4)) :=
  ((List.range (d n)).drop j).flatMap fun k => preRec (preDB n W hd0 k).fields

lemma preRecsB_succ {A : ℕ} (n W : ℕ) (hd0 : 0 < d n) {j : ℕ} (hj : j < d n) :
    (preRecsB n W hd0 j : List (Fin (A + 4))) =
      preRec (preDB n W hd0 j).fields ++ preRecsB n W hd0 (j + 1) := by
  unfold preRecsB
  rw [List.drop_eq_getElem_cons (by simpa using hj), List.flatMap_cons, List.getElem_range]

/-- The canonical interchange headers of the pipeline at width `w`. -/
def preHsB (n w : ℕ) (hd0 : 0 < d n) : Fin (d n) → Fin 5 → List Bool := fun i k =>
  sxBits (swapValues (rsbPre (t n) i) (rsbMid (t n) i) (3 * w)
    (Nat.log 2 (t n i)) (Nat.log 2 (t n (rsbAx hd0 0))) k)

variable {body : F → Pr F T Q (prime + K) U} {rg : RsbR → Fin T} {rgx : RsbX t₀ → Fin T}
  {ι : Fin 64 → Fin T}

end Stage

end

end IntegerMultBounds.MathlibTM2.Fast
