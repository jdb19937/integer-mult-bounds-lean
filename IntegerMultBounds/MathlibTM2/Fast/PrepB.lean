module

public import IntegerMultBounds.MathlibTM2.Fast.PrepA

/-!
# The parameter loader of `B̃₀`

`preB rg rgx ι hd` is the loader `prep` of `rsbAllP` (`Fast/ResampBAll.lean`): a fixed program
over the stage layout `Sum.elim rg rgx : RsbR ⊕ RsbX t₀ → Fin T` (the table machine on the
multiplier registers `ι`), which configures the register file for the next axis.

**Parameter register.** The register `bo` (not used by the stage) holds the records of the axes
in processing order `d - 1, …, 0`; the loader consumes the record on top. A record
(`PreAxB.fields`) is ten unary fields (`preFld`): `t`, `s`, `m`, `L`, `Ld`, `P`, `G`, `α`, `p`,
`W` — the target and source lengths, the off-diagonal window `m`, the target widths of the axis
and of the last axis, the products `P`, `G` of the target lengths before the axis and strictly
between it and the last axis, the table parameters `α`, `p`, and the word size `W` of the table
machine. The coefficient width `w` is the length of `cm .wn`.

**Program** (`preB`).
1. Clear the previous axis: `msk`, `ef`, `df`, `hf`, `sn`, `mwn`, `m2wn`, `m2n`, `smwn`, `tswn`,
   `kn`, `pn` and the five interchange headers.
2. Take the fields onto `ya`, `sn`, `b1`, `tb`, `xa`, `xs`, `pr`, `hc`, `pn`, `ac`.
3. Counters: `mwn = m w`, `m2wn = 2 m w`, `m2n = 2 m`, `smwn = (s - m) w`, `tswn = (t - s) w`,
   `kn = α²`.
4. Headers: the canonical binary digits of `P`, `G`, `3 w`, `L`, `Ld` under a separator.
5. Tables by the table machine: `ef` (`tableE`, `tblStreamECode`), `df` (`tableD`,
   `tblStreamDCode`), `hf` (the coefficient `2^(p-1)`, `preHfCode`), and the row mask `msk`
   (`preMaskCode` at emission width one, its pair symbols mapped to bit symbols).
6. Clear the fields.

**The mask program** (`preMaskCode_do`): for rows `j = 0, …, t - 1` it keeps the next selected
row `q ℓ = ⌊(2 t ℓ + s) / (2 s)⌋` and emits whether `j = q ℓ`; `q` is strictly increasing
for `s ≤ t` (`pre_q_succ`), so the emitted bits are `rsbMask s t` (`preMaskE_map`).

**Results.**
* `preB_runs`: from a register file `σ` with empty loader scratch (`PreFreeB`), the record `D`
  on top of `bo` and `w` symbols on `cm .wn`, the loader ends in `preLoadB σ hd w D rest`;
  `preB_rsbWith` is the same contract in the form `hprep` of `rsb_all_runs`; `preLoadB_cfg`
  gives `RsbAxisCfg` of a loaded file over a base file (`PreBaseB`), with
  `tblStreamE_cstream`, `tblStreamD_cstream`, `tbl_pairs_red`, `preMaskE_map`.
* `rsbStage_exec`: `rsb_all_lineB_disk` with the loader (configured files `preCfgB`, records
  `preRecsB`, bounds `preCpB`).

**Cost** (`preCostB`): clearing the previous axis, `3 Σ fields + 31` for the record, the counters
(`preNumCostB`, `O((s + m + t) w + α²)`), the headers (`preHdrCostB`), and four runs of the
table machine (`preTabCostB`): `preKE D = s (2m)(310 p + 126) + 14 s + 150 p + 420` atoms for
`tableE`, `preKD D = s (310 p + 123) + 160 p + 450` for `tableD`, `preKH D = 4 p + 6` for
`2^(p-1)`, `preKM D = 9 t + 10` for the mask, each atom at most `tblC W w` steps.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

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
        rw [if_neg]
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
        unfold preBit; rw [if_pos ⟨a, has', hqj⟩]
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
          Function.update_apply, h1, h4, h34]
        exact ⟨by omega, by nlinarith, by nlinarith⟩
      · have hq1 : (2 * t * (a + 1) + s) / (2 * s) = RowSelect.q s t (a + 1) := by
          unfold RowSelect.q; ring_nf
        refine ⟨by simp (config := { decide := true }) [tblExactList, TblIns.exact,
            Function.update_apply, hj0],
          by simp (config := { decide := true }) [tblExactList, TblIns.exact,
            Function.update_apply, h35'], a + 1, ?_⟩
        simp (config := { decide := true }) only [tblExactList, TblIns.exact,
          Function.update_apply, List.cons_append, List.nil_append, if_true, if_false]
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
    simp (config := { decide := true }) [tblExactList, TblIns.exact, Function.update_apply, hp']
  have hacc₁ : (tblExactList A w ([.zero 1, .inc 1] ++ [.sub 19 1 2]) st).acc = [] := by
    simp [tblExactList, TblIns.exact, hacc]
  refine TblDo.mono ((tblPow2_do (A := A) (W := W) (w := w) (c := (3 : Fin 48)) (e := 2) (i := 4)
    (by decide) (by decide) (by decide)
    (tblExactList A w ([.zero 1, .inc 1] ++ [.sub 19 1 2]) st)
    (by rw [h2]; omega)).seq (K₂ := 2) (fun s₂ hs₂ => ?_)) (fun _ h => h) (by rw [h2])
  obtain ⟨h3, -, -, hacc₂⟩ := hs₂
  rw [h2] at h3
  refine TblDo.block _ _ (by simp [tblFitsList, TblIns.fits]) ?_
  simp (config := { decide := true }) [tblExactList, TblIns.exact, Function.update_apply, h3,
    hacc₂, hacc₁, hacc]

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
  fun k => sxBits (BinaryInterchangeRun.values D.P D.G (3 * w) D.L D.Ld k)

variable {t₀ T Q K : ℕ} {U F : Type}

/-- The header register `k` of the interchange bank. -/
def preHB (hd : Fin 5 → Fin t₀) (k : Fin 5) : RsbR ⊕ RsbX t₀ := .inr (.sw (reg (hd k)))

/-- The registers cleared before loading an axis. -/
def preClrB (hd : Fin 5 → Fin t₀) : List (RsbR ⊕ RsbX t₀) :=
  [.inl .msk, .inl .ef, .inl .df, .inl .hf, .inl .sn, .inl .mwn, .inl .m2wn, .inl .m2n, .inl .smwn,
    .inl .tswn, .inl .kn, .inl (.cm .pn), preHB hd 0, preHB hd 1, preHB hd 2, preHB hd 3,
    preHB hd 4]

/-- The registers receiving the fields. -/
def preDstB : List (RsbR ⊕ RsbX t₀) :=
  [.inl .ya, .inl .sn, .inl .b1, .inl .tb, .inl .xa, .inl .xs, .inl .pr, .inl .hc, .inl (.cm .pn),
    .inl .ac]

/-- The field registers cleared at the end. -/
def preScrB : List (RsbR ⊕ RsbX t₀) :=
  [.inl .ya, .inl .b1, .inl .tb, .inl .xa, .inl .xs, .inl .pr, .inl .hc, .inl .ac]

/-- Pair symbols of emission width one to bit symbols. -/
def preBitOf {A : ℕ} (x : Fin (A + 4)) : Fin (A + 4) := bitSymbol (decide (x = pairSym A true false))

section Prog

variable (g : RsbR ⊕ RsbX t₀ → Fin T) (ι : Fin 64 → Fin T) (hd : Fin 5 → Fin t₀)

/-- The counters from the fields. -/
def preNumB : Pr F T Q (prime + K) U :=
  .seq (preUMul (g (.inl .b1)) (g (.inl (.cm .wn))) (g (.inl .mwn)) (g (.inl .ac2)) (g (.inl .nv)))
  (.seq (umul 2 (g (.inl .mwn)) (g (.inl .m2wn)) (g (.inl .ac2)))
  (.seq (umul 2 (g (.inl .b1)) (g (.inl .m2n)) (g (.inl .ac2)))
  (.seq (ucopy (g (.inl .sn)) (g (.inl .tC)) (g (.inl .ac2)))
  (.seq (usub (g (.inl .b1)) (g (.inl .tC)) (g (.inl .ac2)))
  (.seq (preUMul (g (.inl .tC)) (g (.inl (.cm .wn))) (g (.inl .smwn)) (g (.inl .ac2))
    (g (.inl .nv)))
  (.seq (uclear (g (.inl .tC)))
  (.seq (ucopy (g (.inl .ya)) (g (.inl .tA)) (g (.inl .ac2)))
  (.seq (usub (g (.inl .sn)) (g (.inl .tA)) (g (.inl .ac2)))
  (.seq (preUMul (g (.inl .tA)) (g (.inl (.cm .wn))) (g (.inl .tswn)) (g (.inl .ac2))
    (g (.inl .nv)))
  (.seq (uclear (g (.inl .tA)))
  (.seq (ucopy (g (.inl .hc)) (g (.inl .tJ)) (g (.inl .ac2)))
  (.seq (preUMul (g (.inl .hc)) (g (.inl .tJ)) (g (.inl .kn)) (g (.inl .ac2)) (g (.inl .nv)))
    (uclear (g (.inl .tJ)))))))))))))))

/-- The five interchange headers. -/
def preHdrB : Pr F T Q (prime + K) U :=
  .seq (umul 3 (g (.inl (.cm .wn))) (g (.inl .tL)) (g (.inl .ac2)))
  (.seq (preHdr (g (.inl .xs)) (g (preHB hd 0)) (g (.inl .ac2)) (g (.inl .nv)))
  (.seq (preHdr (g (.inl .pr)) (g (preHB hd 1)) (g (.inl .ac2)) (g (.inl .nv)))
  (.seq (preHdr (g (.inl .tL)) (g (preHB hd 2)) (g (.inl .ac2)) (g (.inl .nv)))
  (.seq (preHdr (g (.inl .tb)) (g (preHB hd 3)) (g (.inl .ac2)) (g (.inl .nv)))
  (.seq (preHdr (g (.inl .xa)) (g (preHB hd 4)) (g (.inl .ac2)) (g (.inl .nv)))
    (uclear (g (.inl .tL))))))))

/-- The tables: `ef`, `df`, the halving constant `hf` and the row mask `msk`. -/
def preTabB : Pr F T Q (prime + K) U :=
  .seq (preVM (preLay g ι) (.inl .ac) (.inl (.cm .wn))
    [(.inl .sn, 34), (.inl .ya, 35), (.inl .hc, 36), (.inl .b1, 39), (.inl (.cm .pn), 19)]
    tblStreamECode (.inl .ef))
  (.seq (preVM (preLay g ι) (.inl .ac) (.inl (.cm .wn))
    [(.inl .sn, 34), (.inl .ya, 35), (.inl .hc, 36), (.inl (.cm .pn), 19)] tblStreamDCode (.inl .df))
  (.seq (preVM (preLay g ι) (.inl .ac) (.inl (.cm .wn)) [(.inl (.cm .pn), 19)] preHfCode
    (.inl .hf))
  (.seq (.act (.push (.rt (g (.inl .tK))) (fun _ => tick) .done))
  (.seq (preVM (preLay g ι) (.inl .ac) (.inl .tK) [(.inl .sn, 34), (.inl .ya, 35)] preMaskCode
    (.inl .sr))
  (.seq (moveR (g (.inl .sr)) (g (.inl .sel)) preBitOf)
  (.seq (moveR (g (.inl .sel)) (g (.inl .msk)) id)
    (uclear (g (.inl .tK)))))))))

/-- **The loader of `B̃₀`.** -/
def preBg : Pr F T Q (prime + K) U :=
  .seq (preClears ((preClrB hd).map g))
  (.seq (preTakes (g (.inl .bo)) (preDstB.map g))
  (.seq (preNumB g)
  (.seq (preHdrB g hd)
  (.seq (preTabB g ι)
    (preClears (preScrB.map g))))))

end Prog

/-- The loader of `B̃₀` on the stage layout `Sum.elim rg rgx`. -/
def preB (rg : RsbR → Fin T) (rgx : RsbX t₀ → Fin T) (ι : Fin 64 → Fin T) (hd : Fin 5 → Fin t₀) :
    Pr F T Q (prime + K) U :=
  preBg (Sum.elim rg rgx) ι hd

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

/-- The bank after clearing the headers. -/
def preClrXB (xr : RsbX t₀ → List (Fin (A + 4))) (hd : Fin 5 → Fin t₀) :
    RsbX t₀ → List (Fin (A + 4))
  | .sw j => if ∃ k, reg (hd k) = j then [] else xr (.sw j)
  | x => xr x

/-- After step 1. -/
def preF1 (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (hd : Fin 5 → Fin t₀) :
    RsbR ⊕ RsbX t₀ → List (Fin (A + 4))
  | .inl r => if r ∈ [RsbR.msk, .ef, .df, .hf, .sn, .mwn, .m2wn, .m2n, .smwn, .tswn, .kn, .cm .pn]
      then [] else σ (.inl r)
  | .inr x => preClrXB (fun x => σ (.inr x)) hd x

/-- After step 6. -/
def preF6 (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))
  | .inl r => if r ∈ [RsbR.ya, .b1, .tb, .xa, .xs, .pr, .hc, .ac] then [] else σ (.inl r)
  | .inr x => σ (.inr x)

/-- After step 3. -/
def preF3 (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (D : PreAxB) (w : ℕ) :
    RsbR ⊕ RsbX t₀ → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update σ (.inl .mwn) (List.replicate (D.m * w) tick))
    (.inl .m2wn) (List.replicate (2 * (D.m * w)) tick))
    (.inl .m2n) (List.replicate (2 * D.m) tick))
    (.inl .smwn) (List.replicate ((D.s - D.m) * w) tick))
    (.inl .tswn) (List.replicate ((D.t - D.s) * w) tick))
    (.inl .kn) (List.replicate (D.α * D.α) tick)

/-- The step bound of step 3. -/
def preNumCostB (D : PreAxB) (w : ℕ) : ℕ :=
  (D.m * (4 * w + 7) + 2 * D.m + 4) + (4 * (D.m * w) + 4) + (4 * D.m + 4) +
    (4 * D.s + 4) + (4 * D.m + 4) + ((D.s - D.m) * (4 * w + 7) + 2 * (D.s - D.m) + 4) +
    (2 * (D.s - D.m) + 2) + (4 * D.t + 4) + (4 * D.s + 4) +
    ((D.t - D.s) * (4 * w + 7) + 2 * (D.t - D.s) + 4) + (2 * (D.t - D.s) + 2) + (4 * D.α + 4) +
    (D.α * (4 * D.α + 7) + 2 * D.α + 4) + (2 * D.α + 2)

/-- The step bound of step 4. -/
def preHdrCostB (D : PreAxB) (w : ℕ) : ℕ :=
  (4 * w + 4) + (16 * D.P + 5) + (16 * D.G + 5) + (16 * (3 * w) + 5) + (16 * D.L + 5) +
    (16 * D.Ld + 5) + (2 * (3 * w) + 2)

/-- After step 5. -/
def preF5 (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (D : PreAxB) (w : ℕ) :
    RsbR ⊕ RsbX t₀ → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update σ
    (.inl .ef) (tblStreamE A w D.s D.t D.α D.p D.m))
    (.inl .df) (tblStreamD A w D.s D.t D.α D.p))
    (.inl .hf) (tblPairs A w (2 ^ (D.p - 1)) 0))
    (.inl .msk) ((preMaskE A D.s D.t D.t).map preBitOf)

/-- The atom bounds of the table programs. -/
def preKE (D : PreAxB) : ℕ := D.s * (2 * D.m) * (310 * D.p + 126) + 14 * D.s + (150 * D.p + 420)
def preKD (D : PreAxB) : ℕ := D.s * (310 * D.p + 123) + (160 * D.p + 450)
def preKH (D : PreAxB) : ℕ := 3 + ((4 * (D.p - 1) + 5) + 2)
def preKM (D : PreAxB) : ℕ := 7 + (1 + (D.t * (6 + 1 + 2) + 2))

/-- The step bound of step 5. -/
def preTabCostB (D : PreAxB) (w : ℕ) : ℕ :=
  preVMCost 48 D.W w [D.s, D.t, D.α, D.m, D.p] (preKE D) (D.s * (2 * D.m) * w) +
    preVMCost 48 D.W w [D.s, D.t, D.α, D.p] (preKD D) (D.s * w) +
    preVMCost 48 D.W w [D.p] (preKH D) w + 1 + preVMCost 48 D.W 1 [D.s, D.t] (preKM D) D.t +
    (2 * D.t + 2) + (2 * D.t + 2) + 4

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

/-- **The step bound of the loader of `B̃₀`**: clearing the previous axis, reading the record,
the counters, the headers, the four table runs, and clearing the fields. -/
def preCostB (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (hd : Fin 5 → Fin t₀) (w : ℕ)
    (D : PreAxB) : ℕ :=
  (((preClrB hd).map fun r => 2 * (σ r).length + 2).sum + 1) + (3 * D.fields.sum + 3 * 10 + 1) +
    preNumCostB D w + preHdrCostB D w + preTabCostB D w +
    (2 * (D.t + D.m + D.L + D.Ld + D.P + D.G + D.α + D.W) + 17)

end Files

/-! ### Steps -/

section Steps

variable {body : F → Pr F T Q (prime + K) U} {g : RsbR ⊕ RsbX t₀ → Fin T} {ι : Fin 64 → Fin T}

variable (hg : Function.Injective g) (hι : Function.Injective ι) (hdisj : ∀ r j, g r ≠ ι j)
include hg hι hdisj

lemma preLayB_map (l : List (RsbR ⊕ RsbX t₀)) :
    (l.map Sum.inl).map (preLay g ι) = l.map g := by
  simp [List.map_map, Function.comp_def, preLay]

omit hg hι hdisj in
lemma preHB_nodup {hd : Fin 5 → Fin t₀} (hdi : Function.Injective hd) :
    ((preClrB hd).map (Sum.inl : _ → (RsbR ⊕ RsbX t₀) ⊕ TblR 48)).Nodup := by
  have h : ∀ a b, reg (hd a) = reg (hd b) ↔ a = b := fun a b =>
    ⟨fun e => hdi (BinaryInterchangeRun.slot_injective e), fun e => e ▸ rfl⟩
  simp [preClrB, preHB, List.nodup_cons, h]

theorem preB_clr {hd : Fin 5 → Fin t₀} (hdi : Function.Injective hd)
    (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) :
    TwRuns body (preLay g ι) (preClears ((preClrB hd).map g)) (preStB σ) (preStB (preF1 σ hd))
      (((preClrB hd).map fun r => 2 * (σ r).length + 2).sum + 1) := by
  have h := preClears_runs (body := body) (preLay_inj hg hι hdisj) _ (preHB_nodup hdi) (preStB σ)
  rw [preLayB_map hg hι hdisj] at h
  refine twRuns_congr (twRuns_mono h (by simp [List.map_map, Function.comp_def, preStB])) ?_
  funext r
  rcases r with (r | x) | y
  · cases r <;> simp [preStB, preF1, preClrB, preHB]
  · cases x <;> simp [preStB, preF1, preClrB, preHB, preClrXB, preHA_iff]
  · simp [preStB, preClrB]

theorem preB_parse (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB)
    (rest : List (Fin (prime + K + 4))) (hout : σ (.inl .bo) = preRec D.fields ++ rest)
    (hd : ∀ r ∈ preDstB, σ r = []) :
    TwRuns body (preLay g ι) (preTakes (g (.inl .bo)) (preDstB.map g)) (preStB σ)
      (preStB (preTV (.inl .bo) preDstB D.fields rest σ)) (3 * D.fields.sum + 3 * 10 + 1) := by
  have h := preTakes_runs (body := body) (preLay_inj hg hι hdisj) (.inl (.inl .bo))
    (preDstB.map Sum.inl) D.fields (by simp [preDstB, PreAxB.fields]) (by simp [preDstB])
    (preStB σ) rest (by simp [preStB, hout]) (fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨r', hr', rfl⟩ := hr
      exact hd r' hr')
  rw [preLayB_map hg hι hdisj] at h
  simp only [PreAxB.fields, List.length_cons, List.length_nil] at h ⊢
  refine twRuns_congr h ?_
  simp only [preTV, preDstB, PreAxB.fields, List.map_cons, List.map_nil, List.zip_cons_cons,
    List.zip_nil_left, List.foldl_cons, List.foldl_nil, preStB, Sum.update_elim_inl]

set_option maxRecDepth 4000 in
theorem preB_num (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB) (w : ℕ)
    (hb1 : σ (.inl .b1) = List.replicate D.m tick) (hsn : σ (.inl .sn) = List.replicate D.s tick)
    (hya : σ (.inl .ya) = List.replicate D.t tick) (hhc : σ (.inl .hc) = List.replicate D.α tick)
    (hwn : (σ (.inl (.cm .wn))).length = w) (hmwn : σ (.inl .mwn) = [])
    (hm2wn : σ (.inl .m2wn) = []) (hm2n : σ (.inl .m2n) = []) (hsmwn : σ (.inl .smwn) = [])
    (htswn : σ (.inl .tswn) = []) (hkn : σ (.inl .kn) = []) (htC : σ (.inl .tC) = [])
    (htA : σ (.inl .tA) = []) (htJ : σ (.inl .tJ) = []) (hac2 : σ (.inl .ac2) = [])
    (hnv : σ (.inl .nv) = []) :
    TwRuns body (preLay g ι) (preNumB g) (preStB σ) (preStB (preF3 σ D w)) (preNumCostB D w) := by
  have htg := preLay_inj hg hι hdisj
  refine twRuns_congr (twRuns_mono
    (twRuns_seq (preUMul_runs (body := body) htg (a := .inl (.inl .b1)) (b := .inl (.inl (.cm .wn)))
      (c := .inl (.inl .mwn)) (t₁ := .inl (.inl .ac2)) (t₂ := .inl (.inl .nv)) (by simp)
      (preStB σ) ?_ ?_)
    (twRuns_seq (twRuns_umul (body := body) htg 2 (a := .inl (.inl .mwn)) (b := .inl (.inl .m2wn))
      (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) _ ?_)
    (twRuns_seq (twRuns_umul (body := body) htg 2 (a := .inl (.inl .b1)) (b := .inl (.inl .m2n))
      (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) _ ?_)
    (twRuns_seq (twRuns_ucopy (body := body) htg (a := .inl (.inl .sn)) (b := .inl (.inl .tC))
      (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) _ ?_)
    (twRuns_seq (twRuns_usub (body := body) htg (a := .inl (.inl .b1)) (b := .inl (.inl .tC))
      (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) _ ?_)
    (twRuns_seq (preUMul_runs (body := body) htg (a := .inl (.inl .tC)) (b := .inl (.inl (.cm .wn)))
      (c := .inl (.inl .smwn)) (t₁ := .inl (.inl .ac2)) (t₂ := .inl (.inl .nv)) (by simp) _ ?_ ?_)
    (twRuns_seq (twRuns_uclear (body := body) htg (.inl (.inl .tC)) _)
    (twRuns_seq (twRuns_ucopy (body := body) htg (a := .inl (.inl .ya)) (b := .inl (.inl .tA))
      (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) _ ?_)
    (twRuns_seq (twRuns_usub (body := body) htg (a := .inl (.inl .sn)) (b := .inl (.inl .tA))
      (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) _ ?_)
    (twRuns_seq (preUMul_runs (body := body) htg (a := .inl (.inl .tA)) (b := .inl (.inl (.cm .wn)))
      (c := .inl (.inl .tswn)) (t₁ := .inl (.inl .ac2)) (t₂ := .inl (.inl .nv)) (by simp) _ ?_ ?_)
    (twRuns_seq (twRuns_uclear (body := body) htg (.inl (.inl .tA)) _)
    (twRuns_seq (twRuns_ucopy (body := body) htg (a := .inl (.inl .hc)) (b := .inl (.inl .tJ))
      (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) _ ?_)
    (twRuns_seq (preUMul_runs (body := body) htg (a := .inl (.inl .hc)) (b := .inl (.inl .tJ))
      (c := .inl (.inl .kn)) (t₁ := .inl (.inl .ac2)) (t₂ := .inl (.inl .nv)) (by simp) _ ?_ ?_)
      (twRuns_uclear (body := body) htg (.inl (.inl .tJ)) _)))))))))))))) ?_) ?_
  all_goals try (simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq,
    reduceCtorEq, if_false, if_true, RsbR.cm.injEq, hb1, hsn, hya, hhc, hwn, hmwn, hm2wn, hm2n,
    hsmwn, htswn, hkn, htC, htA, htJ, hac2, hnv, List.append_nil, List.length_replicate]; done)
  · simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq,
      reduceCtorEq, if_false, if_true, RsbR.cm.injEq, hb1, hsn, hya, hhc, hwn, hmwn, hm2wn, hm2n,
      hsmwn, htswn, hkn, htC, htA, htJ, hac2, hnv, List.append_nil, List.length_replicate,
      List.length_drop]
    unfold preNumCostB
    exact le_of_eq (by ring)
  · funext r
    rcases r with (r | x) | y
    · cases r <;> simp only [Function.update_apply, preStB, preF3, Sum.elim_inl,
        Sum.inl.injEq, reduceCtorEq, if_false, if_true, RsbR.cm.injEq]
      all_goals simp [hb1, hsn, hya, hhc, hwn, hmwn, hm2wn, hm2n, hsmwn, htswn, hkn, htC, htA,
        htJ, hac2, hnv]
    · simp only [Function.update_apply, preStB, preF3, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq,
        if_false]
    · simp only [Function.update_apply, reduceCtorEq, if_false, preStB, Sum.elim_inr]

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
    ⟨fun e => hdi (BinaryInterchangeRun.slot_injective e), fun e => e ▸ rfl⟩
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
    Sum.elim_inl, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, if_true, RsbR.cm.injEq,
    RsbX.sw.injEq, hinj, hxs, hpr, htb, hxa, hwn, htL, hac2, hnv, hH, List.append_nil,
    List.length_replicate]; done)
  · simp (config := { decide := true }) only [preStB, preHB, Function.update_apply,
      Sum.elim_inl, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, if_true, RsbR.cm.injEq,
      RsbX.sw.injEq, hinj, hxs, hpr, htb, hxa, hwn, htL, hac2, hnv, hH, List.append_nil,
      List.length_replicate]
    unfold preHdrCostB
    exact le_of_eq (by ring)
  · funext r
    rcases r with (r | x) | y
    · cases r <;> simp only [Function.update_apply, preStB, preHB, preBankB, Sum.elim_inl,
        Sum.inl.injEq, reduceCtorEq, if_false, if_true, RsbR.cm.injEq]
      all_goals simp [htL]
    · simp only [Function.update_apply, preStB, preHB, Sum.elim_inl, Sum.inl.injEq,
        reduceCtorEq, if_false, if_true]
      rcases x with j | _ | _ | _ | _ | _
      · by_cases hj : ∃ k, reg (hd k) = j
        · obtain ⟨k, rfl⟩ := hj
          fin_cases k <;> simp (config := { decide := true }) [preBankB, hinj, rsbBank_hd hdi,
            PreAxB.hs, BinaryInterchangeRun.values, hxs, hpr, htb, hxa, hwn, htL]
        · have hne : ∀ k, j ≠ reg (hd k) := fun k h => hj ⟨k, h.symm⟩
          simp [preBankB, hj, hne]
      all_goals simp [preBankB]
    · simp only [Function.update_apply, reduceCtorEq, if_false, preStB, Sum.elim_inr]

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

theorem preB_vmE (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB) (w : ℕ)
    (hsn : σ (.inl .sn) = List.replicate D.s tick) (hya : σ (.inl .ya) = List.replicate D.t tick)
    (hhc : σ (.inl .hc) = List.replicate D.α tick) (hb1 : σ (.inl .b1) = List.replicate D.m tick)
    (hpn : σ (.inl (.cm .pn)) = List.replicate D.p tick)
    (hac : σ (.inl .ac) = List.replicate D.W tick) (hwn : (σ (.inl (.cm .wn))).length = w)
    (hef : σ (.inl .ef) = []) (hp : 13 ≤ D.p) (hα : 2 ≤ D.α) (hs : 0 < D.s) (hst : D.s < D.t)
    (hwW : w ≤ D.W)
    (hW : D.α ^ 2 * ((D.s + D.t) * (D.m + 1)) ^ 2 * 2 ^ (13 * D.p + 8) < 2 ^ D.W) :
    TwRuns body (preLay g ι) (preVM (preLay g ι) (.inl .ac) (.inl (.cm .wn))
      [(.inl .sn, 34), (.inl .ya, 35), (.inl .hc, 36), (.inl .b1, 39), (.inl (.cm .pn), 19)]
      tblStreamECode (.inl .ef)) (preStB σ)
      (preStB (Function.update σ (.inl .ef) (tblStreamE (prime + K) w D.s D.t D.α D.p D.m)))
      (preVMCost 48 D.W w [D.s, D.t, D.α, D.m, D.p] (preKE D) (D.s * (2 * D.m) * w)) := by
  have htg := preLay_inj hg hι hdisj
  obtain ⟨hs2, ht2, hα2, hm2, hpW, -, -⟩ := pre_W_facts hα hs hst hW
  have hp2 : D.p < 2 ^ D.W := lt_trans hpW Nat.lt_two_pow_self
  have hv : preLoadVal (preStB σ)
      [(.inl .sn, 34), (.inl .ya, 35), (.inl .hc, 36), (.inl .b1, 39), (.inl (.cm .pn), 19)]
      (fun _ : Fin 48 => 0) = Function.update (Function.update (Function.update (Function.update
        (Function.update (fun _ : Fin 48 => 0) 34 D.s) 35 D.t) 36 D.α) 39 D.m) 19 D.p := by
    simp [preLoadVal, preStB, hsn, hya, hhc, hb1, hpn]
  have h := preVM_runs (body := body) htg (.inl .ac) (.inl (.cm .wn))
    [(.inl .sn, 34), (.inl .ya, 35), (.inl .hc, 36), (.inl .b1, 39), (.inl (.cm .pn), 19)]
    tblStreamECode (.inl .ef) (preStB σ) (fun _ => rfl) (by simp [preStB, hac])
    (by simp [preStB, hwn]) hwW
    (fun j => by
      rw [hv]
      simp only [Function.update_apply]
      split_ifs <;> first | assumption | exact Nat.two_pow_pos _)
    (tblStreamE_do (A := prime + K) (W := D.W) (w := w) ⟨_, []⟩ (s := D.s) (t := D.t) (α := D.α)
      (m := D.m) (p := D.p)
      (by rw [hv]; simp (config := { decide := true }) [Function.update_apply])
      (by rw [hv]; simp (config := { decide := true }) [Function.update_apply])
      (by rw [hv]; simp (config := { decide := true }) [Function.update_apply])
      (by rw [hv]; simp (config := { decide := true }) [Function.update_apply])
      (by rw [hv]; simp (config := { decide := true }) [Function.update_apply]) hp hα hs hW)
    (tblStreamE (prime + K) w D.s D.t D.α D.p D.m) (fun s' hs' => by
      simp only at hs'; rw [hs', List.append_nil, List.reverse_reverse])
  rw [length_tblStreamE, preStB_upd, preStB_inl, hef, List.append_nil] at h
  refine twRuns_mono h (le_of_eq ?_)
  simp [preStB, hsn, hya, hhc, hb1, hpn, preKE]

theorem preB_vmD (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB) (w : ℕ)
    (hsn : σ (.inl .sn) = List.replicate D.s tick) (hya : σ (.inl .ya) = List.replicate D.t tick)
    (hhc : σ (.inl .hc) = List.replicate D.α tick)
    (hpn : σ (.inl (.cm .pn)) = List.replicate D.p tick)
    (hac : σ (.inl .ac) = List.replicate D.W tick) (hwn : (σ (.inl (.cm .wn))).length = w)
    (hdf : σ (.inl .df) = []) (hp : 13 ≤ D.p) (hα : 2 ≤ D.α) (hαp : D.α ^ 2 ≤ D.p) (hs : 0 < D.s)
    (hst : D.s < D.t) (hwW : w ≤ D.W)
    (hW : D.α ^ 2 * ((D.s + D.t) * (D.m + 1)) ^ 2 * 2 ^ (13 * D.p + 8) < 2 ^ D.W) :
    TwRuns body (preLay g ι) (preVM (preLay g ι) (.inl .ac) (.inl (.cm .wn))
      [(.inl .sn, 34), (.inl .ya, 35), (.inl .hc, 36), (.inl (.cm .pn), 19)]
      tblStreamDCode (.inl .df)) (preStB σ)
      (preStB (Function.update σ (.inl .df) (tblStreamD (prime + K) w D.s D.t D.α D.p)))
      (preVMCost 48 D.W w [D.s, D.t, D.α, D.p] (preKD D) (D.s * w)) := by
  have htg := preLay_inj hg hι hdisj
  obtain ⟨hs2, ht2, hα2, hm2, hpW, hWD, -⟩ := pre_W_facts hα hs hst hW
  have hp2 : D.p < 2 ^ D.W := lt_trans hpW Nat.lt_two_pow_self
  have hv : preLoadVal (preStB σ)
      [(.inl .sn, 34), (.inl .ya, 35), (.inl .hc, 36), (.inl (.cm .pn), 19)]
      (fun _ : Fin 48 => 0) = Function.update (Function.update (Function.update (Function.update
        (fun _ : Fin 48 => 0) 34 D.s) 35 D.t) 36 D.α) 19 D.p := by
    simp [preLoadVal, preStB, hsn, hya, hhc, hpn]
  have h := preVM_runs (body := body) htg (.inl .ac) (.inl (.cm .wn))
    [(.inl .sn, 34), (.inl .ya, 35), (.inl .hc, 36), (.inl (.cm .pn), 19)]
    tblStreamDCode (.inl .df) (preStB σ) (fun _ => rfl) (by simp [preStB, hac])
    (by simp [preStB, hwn]) hwW
    (fun j => by
      rw [hv]
      simp only [Function.update_apply]
      split_ifs <;> first | assumption | exact Nat.two_pow_pos _)
    (tblStreamD_do (A := prime + K) (W := D.W) (w := w) ⟨_, []⟩ (s := D.s) (t := D.t) (α := D.α)
      (p := D.p)
      (by rw [hv]; simp (config := { decide := true }) [Function.update_apply])
      (by rw [hv]; simp (config := { decide := true }) [Function.update_apply])
      (by rw [hv]; simp (config := { decide := true }) [Function.update_apply])
      (by rw [hv]; simp (config := { decide := true }) [Function.update_apply]) hp hα hαp hs hWD)
    (tblStreamD (prime + K) w D.s D.t D.α D.p) (fun s' hs' => by
      simp only at hs'; rw [hs', List.append_nil, List.reverse_reverse])
  rw [length_tblStreamD, preStB_upd, preStB_inl, hdf, List.append_nil] at h
  refine twRuns_mono h (le_of_eq ?_)
  simp [preStB, hsn, hya, hhc, hpn, preKD]

theorem preB_vmH (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB) (w : ℕ)
    (hpn : σ (.inl (.cm .pn)) = List.replicate D.p tick)
    (hac : σ (.inl .ac) = List.replicate D.W tick) (hwn : (σ (.inl (.cm .wn))).length = w)
    (hhf : σ (.inl .hf) = []) (hp : 1 ≤ D.p) (hpW : D.p < D.W) (hwW : w ≤ D.W) :
    TwRuns body (preLay g ι) (preVM (preLay g ι) (.inl .ac) (.inl (.cm .wn))
      [(.inl (.cm .pn), 19)] preHfCode (.inl .hf)) (preStB σ)
      (preStB (Function.update σ (.inl .hf) (tblPairs (prime + K) w (2 ^ (D.p - 1)) 0)))
      (preVMCost 48 D.W w [D.p] (preKH D) w) := by
  have htg := preLay_inj hg hι hdisj
  have hp2 : D.p < 2 ^ D.W := lt_trans hpW Nat.lt_two_pow_self
  have hv : preLoadVal (preStB σ) [(.inl (.cm .pn), 19)] (fun _ : Fin 48 => 0) =
      Function.update (fun _ : Fin 48 => 0) 19 D.p := by
    simp [preLoadVal, preStB, hpn]
  have h := preVM_runs (body := body) htg (.inl .ac) (.inl (.cm .wn)) [(.inl (.cm .pn), 19)]
    preHfCode (.inl .hf) (preStB σ) (fun _ => rfl) (by simp [preStB, hac])
    (by simp [preStB, hwn]) hwW
    (fun j => by
      rw [hv]
      simp only [Function.update_apply]
      split_ifs <;> first | assumption | exact Nat.two_pow_pos _)
    (preHfCode_do (A := prime + K) (W := D.W) (w := w) ⟨_, []⟩ (p := D.p)
      (by rw [hv]; simp) hp hpW rfl)
    (tblPairs (prime + K) w (2 ^ (D.p - 1)) 0) (fun s' hs' => by
      rw [hs', List.reverse_reverse])
  rw [preStB_upd, preStB_inl, hhf, List.append_nil] at h
  refine twRuns_mono h (le_of_eq ?_)
  simp [preStB, hpn, preKH, tblPairs, coeffSyms]

theorem preB_vmM (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB)
    (hsn : σ (.inl .sn) = List.replicate D.s tick) (hya : σ (.inl .ya) = List.replicate D.t tick)
    (hac : σ (.inl .ac) = List.replicate D.W tick) (htK : (σ (.inl .tK)).length = 1)
    (hsr : σ (.inl .sr) = []) (hs : 0 < D.s) (hst : D.s < D.t) (hW1 : 1 ≤ D.W)
    (hWM : 4 * D.t * (D.s + 1) < 2 ^ D.W) :
    TwRuns body (preLay g ι) (preVM (preLay g ι) (.inl .ac) (.inl .tK)
      [(.inl .sn, 34), (.inl .ya, 35)] preMaskCode (.inl .sr)) (preStB σ)
      (preStB (Function.update σ (.inl .sr) (preMaskE (prime + K) D.s D.t D.t)))
      (preVMCost 48 D.W 1 [D.s, D.t] (preKM D) D.t) := by
  have htg := preLay_inj hg hι hdisj
  have hs2 : D.s < 2 ^ D.W := by nlinarith
  have ht2 : D.t < 2 ^ D.W := by nlinarith
  have hv : preLoadVal (preStB σ) [(.inl .sn, 34), (.inl .ya, 35)] (fun _ : Fin 48 => 0) =
      Function.update (Function.update (fun _ : Fin 48 => 0) 34 D.s) 35 D.t := by
    simp [preLoadVal, preStB, hsn, hya]
  have h := preVM_runs (body := body) htg (.inl .ac) (.inl .tK) [(.inl .sn, 34), (.inl .ya, 35)]
    preMaskCode (.inl .sr) (preStB σ) (fun _ => rfl) (by simp [preStB, hac])
    (by simp [preStB, htK]) hW1
    (fun j => by
      rw [hv]
      simp only [Function.update_apply]
      split_ifs <;> first | assumption | exact Nat.two_pow_pos _)
    (preMaskCode_do (A := prime + K) (W := D.W) ⟨_, []⟩ (s := D.s) (t := D.t)
      (by rw [hv]; simp (config := { decide := true }) [Function.update_apply])
      (by rw [hv]; simp (config := { decide := true }) [Function.update_apply]) hs hst rfl hWM)
    (preMaskE (prime + K) D.s D.t D.t) (fun s' hs' => by
      rw [hs', List.reverse_reverse])
  rw [preStB_upd, preStB_inl, hsr, List.append_nil] at h
  refine twRuns_mono h (le_of_eq ?_)
  simp [preStB, hsn, hya, preKM, preMaskE, tblPairs, coeffSyms]

set_option maxRecDepth 4000 in
theorem preB_tab (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB) (w : ℕ)
    (hsn : σ (.inl .sn) = List.replicate D.s tick) (hya : σ (.inl .ya) = List.replicate D.t tick)
    (hhc : σ (.inl .hc) = List.replicate D.α tick) (hb1 : σ (.inl .b1) = List.replicate D.m tick)
    (hpn : σ (.inl (.cm .pn)) = List.replicate D.p tick)
    (hac : σ (.inl .ac) = List.replicate D.W tick) (hwn : (σ (.inl (.cm .wn))).length = w)
    (hef : σ (.inl .ef) = []) (hdf : σ (.inl .df) = []) (hhf : σ (.inl .hf) = [])
    (hmsk : σ (.inl .msk) = []) (hsr : σ (.inl .sr) = []) (hsel : σ (.inl .sel) = [])
    (htK : σ (.inl .tK) = []) (hp : 13 ≤ D.p) (hα : 2 ≤ D.α) (hαp : D.α ^ 2 ≤ D.p)
    (hs : 0 < D.s) (hst : D.s < D.t) (hwW : w ≤ D.W)
    (hW : D.α ^ 2 * ((D.s + D.t) * (D.m + 1)) ^ 2 * 2 ^ (13 * D.p + 8) < 2 ^ D.W) :
    TwRuns body (preLay g ι) (preTabB g ι) (preStB σ) (preStB (preF5 σ D w)) (preTabCostB D w) := by
  have htg := preLay_inj hg hι hdisj
  obtain ⟨-, -, -, -, hpW, -, hWM⟩ := pre_W_facts hα hs hst hW
  have s1 := preB_vmE (body := body) hg hι hdisj σ D w hsn hya hhc hb1 hpn hac hwn hef hp hα hs hst
    hwW hW
  set σ1 := Function.update σ (.inl .ef) (tblStreamE (prime + K) w D.s D.t D.α D.p D.m) with hσ1
  have s2 := preB_vmD (body := body) hg hι hdisj σ1 D w (by simp [hσ1, hsn]) (by simp [hσ1, hya])
    (by simp [hσ1, hhc]) (by simp [hσ1, hpn]) (by simp [hσ1, hac]) (by simp [hσ1, hwn])
    (by simp [hσ1, hdf]) hp hα hαp hs hst hwW hW
  set σ2 := Function.update σ1 (.inl .df) (tblStreamD (prime + K) w D.s D.t D.α D.p) with hσ2
  have s3 := preB_vmH (body := body) hg hι hdisj σ2 D w (by simp [hσ2, hσ1, hpn])
    (by simp [hσ2, hσ1, hac]) (by simp [hσ2, hσ1, hwn]) (by simp [hσ2, hσ1, hhf]) (by omega) hpW
    hwW
  set σ3 := Function.update σ2 (.inl .hf) (tblPairs (prime + K) w (2 ^ (D.p - 1)) 0) with hσ3
  have s4 := twRuns_congr (twRuns_push (body := body) htg (.inl (.inl .tK)) tick (preStB σ3))
    (preStB_upd σ3 (.inl .tK) _)
  rw [preStB_inl] at s4
  set σ4 := Function.update σ3 (.inl .tK) (tick :: σ3 (.inl .tK)) with hσ4
  have s5 := preB_vmM (body := body) hg hι hdisj σ4 D (by simp [hσ4, hσ3, hσ2, hσ1, hsn])
    (by simp [hσ4, hσ3, hσ2, hσ1, hya]) (by simp [hσ4, hσ3, hσ2, hσ1, hac])
    (by simp [hσ4, hσ3, hσ2, hσ1, htK]) (by simp [hσ4, hσ3, hσ2, hσ1, hsr]) hs hst (by omega) hWM
  refine twRuns_congr (twRuns_mono (twRuns_seq s1 (twRuns_seq s2 (twRuns_seq s3 (twRuns_seq s4
    (twRuns_seq s5
    (twRuns_seq (twRuns_moveRf (body := body) htg (a := .inl (.inl .sr)) (b := .inl (.inl .sel))
      (by simp) preBitOf _)
    (twRuns_seq (twRuns_moveR (body := body) htg (a := .inl (.inl .sel)) (b := .inl (.inl .msk))
      (by simp) _)
      (twRuns_uclear (body := body) htg (.inl (.inl .tK)) _)))))))) ?_) ?_
  · simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq,
      if_false, if_true, hσ4, hσ3, hσ2, hσ1, hsr, hsel, htK, List.length_cons, List.length_nil,
      List.length_reverse, List.length_map, List.append_nil, length_preMaskE]
    unfold preTabCostB
    omega
  · funext r
    rcases r with (r | x) | y
    · cases r <;> simp only [Function.update_apply, preStB, preF5, hσ4, hσ3, hσ2, hσ1,
        Sum.elim_inl, Sum.inl.injEq, reduceCtorEq, if_false, if_true, RsbR.cm.injEq]
      all_goals simp [hsr, hsel, htK, hmsk]
    · simp only [Function.update_apply, preStB, preF5, hσ4, hσ3, hσ2, hσ1, Sum.elim_inl,
        Sum.inl.injEq, reduceCtorEq, if_false]
    · simp only [Function.update_apply, reduceCtorEq, if_false, preStB, Sum.elim_inr]

theorem preB_end (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) :
    TwRuns body (preLay g ι) (preClears (preScrB.map g)) (preStB σ) (preStB (preF6 σ))
      ((preScrB.map fun r => 2 * (σ r).length + 2).sum + 1) := by
  have h := preClears_runs (body := body) (preLay_inj hg hι hdisj) (preScrB.map Sum.inl)
    (by simp [preScrB]) (preStB σ)
  rw [preLayB_map hg hι hdisj] at h
  refine twRuns_congr (twRuns_mono h (by simp [List.map_map, Function.comp_def, preStB])) ?_
  funext r
  rcases r with (r | x) | y
  · cases r <;> simp [preStB, preF6, preScrB]
  · simp [preStB, preF6, preScrB]
  · simp [preStB, preScrB]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
/-- **The loader of `B̃₀`.** From a register file `σ` whose loader scratch registers are empty,
with the record `D` on top of the parameter register `bo` and `w` symbols on `cm .wn`, `preBg`
loads the axis `D`: afterwards the register file is `preLoadB σ hd w D rest`, within
`preCostB σ hd w D` steps. Conditions of the table machine: `13 ≤ p`, `2 ≤ α`, `α² ≤ p`,
`0 < s < t`, `w ≤ W`, `α² ((s + t)(m + 1))² 2^(13p+8) < 2^W`. -/
theorem preB_runs {hd : Fin 5 → Fin t₀} (hdi : Function.Injective hd)
    (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB)
    (rest : List (Fin (prime + K + 4))) (w : ℕ) (hF : PreFreeB σ)
    (hout : σ (.inl .bo) = preRec D.fields ++ rest) (hwn : (σ (.inl (.cm .wn))).length = w)
    (hp : 13 ≤ D.p) (hα : 2 ≤ D.α) (hαp : D.α ^ 2 ≤ D.p) (hs : 0 < D.s) (hst : D.s < D.t)
    (hwW : w ≤ D.W)
    (hW : D.α ^ 2 * ((D.s + D.t) * (D.m + 1)) ^ 2 * 2 ^ (13 * D.p + 8) < 2 ^ D.W) :
    TwRuns body (preLay g ι) (preBg g ι hd) (preStB σ) (preStB (preLoadB σ hd w D rest))
      (preCostB σ hd w D) := by
  set σ1 := preF1 σ hd with hσ1
  set σ2 := preTV (.inl .bo) preDstB D.fields rest σ1 with hσ2
  set σ3 := preF3 σ2 D w with hσ3
  set σ4 := preBankB σ3 hd (D.hs w) with hσ4
  set σ5 := preF5 σ4 D w with hσ5
  have e2 : ∀ r, r ∉ preDstB → r ≠ .inl .bo → σ2 r = σ1 r := by
    intro r h1 h2
    simp only [hσ2, preTV, preDstB, PreAxB.fields, List.zip_cons_cons, List.zip_nil_left,
      List.foldl_cons, List.foldl_nil, List.mem_cons, not_or] at h1 ⊢
    simp only [Function.update_apply]
    simp [h1, h2]
  have h1 := preB_clr (body := body) hg hι hdisj hdi σ
  have h2 := preB_parse (body := body) hg hι hdisj σ1 D rest (by simp [hσ1, preF1, hout])
    (by simp [preDstB, hσ1, preF1, hF.ya, hF.b1, hF.tb, hF.xa, hF.xs, hF.pr, hF.hc, hF.ac])
  have hv2 : σ2 (.inl .ya) = List.replicate D.t tick ∧ σ2 (.inl .sn) = List.replicate D.s tick ∧
      σ2 (.inl .b1) = List.replicate D.m tick ∧ σ2 (.inl .tb) = List.replicate D.L tick ∧
      σ2 (.inl .xa) = List.replicate D.Ld tick ∧ σ2 (.inl .xs) = List.replicate D.P tick ∧
      σ2 (.inl .pr) = List.replicate D.G tick ∧ σ2 (.inl .hc) = List.replicate D.α tick ∧
      σ2 (.inl (.cm .pn)) = List.replicate D.p tick ∧ σ2 (.inl .ac) = List.replicate D.W tick := by
    simp [hσ2, preTV, preDstB, PreAxB.fields, Function.update_apply]
  obtain ⟨v2ya, v2sn, v2b1, v2tb, v2xa, v2xs, v2pr, v2hc, v2pn, v2ac⟩ := hv2
  have e2' : ∀ r : RsbR, r ≠ .ya → r ≠ .sn → r ≠ .b1 → r ≠ .tb → r ≠ .xa → r ≠ .xs → r ≠ .pr →
      r ≠ .hc → r ≠ .cm .pn → r ≠ .ac → r ≠ .bo → σ2 (.inl r) = σ1 (.inl r) := by
    intro r a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
    exact e2 _ (by simp [preDstB, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]) (by simp [a11])
  have h3 := preB_num (body := body) hg hι hdisj σ2 D w v2b1 v2sn v2ya v2hc
    (by rw [e2' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [hσ1, preF1, hwn])
    (by rw [e2' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [hσ1, preF1])
    (by rw [e2' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [hσ1, preF1])
    (by rw [e2' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [hσ1, preF1])
    (by rw [e2' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [hσ1, preF1])
    (by rw [e2' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [hσ1, preF1])
    (by rw [e2' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [hσ1, preF1])
    (by rw [e2' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [hσ1, preF1, hF.tC])
    (by rw [e2' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [hσ1, preF1, hF.tA])
    (by rw [e2' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [hσ1, preF1, hF.tJ])
    (by rw [e2' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [hσ1, preF1, hF.ac2])
    (by rw [e2' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [hσ1, preF1, hF.nv])
  have s1 : ∀ r : RsbR, r ≠ .ya → r ≠ .sn → r ≠ .b1 → r ≠ .tb → r ≠ .xa → r ≠ .xs → r ≠ .pr →
      r ≠ .hc → r ≠ .cm .pn → r ≠ .ac → r ≠ .bo →
      r ≠ .mwn → r ≠ .m2wn → r ≠ .m2n → r ≠ .smwn → r ≠ .tswn → r ≠ .kn →
      σ4 (.inl r) = σ1 (.inl r) := by
    intro r a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 b1 b2 b3 b4 b5 b6
    simp only [hσ4, preBankB, hσ3, preF3, Function.update_apply, Sum.inl.injEq, b1, b2, b3, b4, b5,
      b6, if_false]
    exact e2' r a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  have hH : ∀ k, σ3 (.inr (.sw (reg (hd k)))) = [] := by
    intro k
    simp only [hσ3, preF3, Function.update_apply, reduceCtorEq, if_false]
    rw [e2 _ (by simp [preDstB]) (by simp)]
    simp only [hσ1, preF1, preClrXB]
    simp
  have h4 := preB_hdr (body := body) hg hι hdisj hdi σ3 D w (by simp [hσ3, preF3, v2xs])
    (by simp [hσ3, preF3, v2pr]) (by simp [hσ3, preF3, v2tb]) (by simp [hσ3, preF3, v2xa])
    (by
      simp only [hσ3, preF3, Function.update_apply, Sum.inl.injEq, reduceCtorEq, if_false]
      rw [e2' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [hσ1, preF1, hwn])
    (by
      simp only [hσ3, preF3, Function.update_apply, Sum.inl.injEq, reduceCtorEq, if_false]
      rw [e2' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [hσ1, preF1, hF.tL])
    (by
      simp only [hσ3, preF3, Function.update_apply, Sum.inl.injEq, reduceCtorEq, if_false]
      rw [e2' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [hσ1, preF1, hF.ac2])
    (by
      simp only [hσ3, preF3, Function.update_apply, Sum.inl.injEq, reduceCtorEq, if_false]
      rw [e2' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [hσ1, preF1, hF.nv])
    hH
  have hσ4v : ∀ r : RsbR, σ4 (.inl r) = σ3 (.inl r) := fun r => by simp [hσ4, preBankB]
  have h5 := preB_tab (body := body) hg hι hdisj σ4 D w
    (by rw [hσ4v]; simp [hσ3, preF3, v2sn]) (by rw [hσ4v]; simp [hσ3, preF3, v2ya])
    (by rw [hσ4v]; simp [hσ3, preF3, v2hc]) (by rw [hσ4v]; simp [hσ3, preF3, v2b1])
    (by rw [hσ4v]; simp [hσ3, preF3, v2pn]) (by rw [hσ4v]; simp [hσ3, preF3, v2ac])
    (by
      rw [s1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]; simp [hσ1, preF1, hwn])
    (by
      rw [s1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]; simp [hσ1, preF1])
    (by
      rw [s1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]; simp [hσ1, preF1])
    (by
      rw [s1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]; simp [hσ1, preF1])
    (by
      rw [s1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]; simp [hσ1, preF1])
    (by
      rw [s1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]; simp [hσ1, preF1, hF.sr])
    (by
      rw [s1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]; simp [hσ1, preF1, hF.sel])
    (by
      rw [s1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]; simp [hσ1, preF1, hF.tK])
    hp hα hαp hs hst hwW hW
  have h6 := preB_end (body := body) hg hι hdisj σ5
  have hfin : preF6 σ5 = preLoadB σ hd w D rest := by
    funext r
    rcases r with r | x
    · cases r
      case cm c =>
        cases c <;> simp only [preF6, hσ5, preF5, hσ4, preBankB, hσ3, preF3, hσ2, preTV, preDstB,
          PreAxB.fields, List.zip_cons_cons, List.zip_nil_left, List.foldl_cons, List.foldl_nil,
          hσ1, preF1, preLoadB, Function.update_apply, Sum.inl.injEq, reduceCtorEq, if_false,
          if_true, RsbR.cm.injEq, List.mem_cons, List.not_mem_nil, or_false, or_true]
      all_goals simp only [preF6, hσ5, preF5, hσ4, preBankB, hσ3, preF3, hσ2, preTV, preDstB,
        PreAxB.fields, List.zip_cons_cons, List.zip_nil_left, List.foldl_cons, List.foldl_nil,
        hσ1, preF1, preLoadB, Function.update_apply, Sum.inl.injEq, reduceCtorEq, if_false,
        if_true, RsbR.cm.injEq, List.mem_cons, List.not_mem_nil, or_false, or_true]
      all_goals simp [hF.ya, hF.b1, hF.tb, hF.xa, hF.xs, hF.pr, hF.hc, hF.ac]
    · simp only [preF6, hσ5, preF5, hσ4, hσ3, preF3, hσ2, preTV, preDstB, PreAxB.fields,
        List.zip_cons_cons, List.zip_nil_left, List.foldl_cons, List.foldl_nil, preLoadB,
        Function.update_apply, reduceCtorEq, if_false]
      rcases x with j | _ | _ | _ | _ | _
      · simp only [preBankB]
        by_cases hj : ∃ k, reg (hd k) = j
        · simp only [hj, if_true]
        · simp only [hj, if_false, hσ1, preF1, preClrXB, preF3, preTV, preDstB, PreAxB.fields,
            List.zip_cons_cons, List.zip_nil_left, List.foldl_cons, List.foldl_nil,
            Function.update_apply, reduceCtorEq]
      all_goals simp [preBankB, hσ1, preF1, preClrXB]
  rw [hfin] at h6
  refine twRuns_mono (twRuns_seq h1 (twRuns_seq h2 (twRuns_seq h3 (twRuns_seq h4
    (twRuns_seq h5 h6))))) (le_of_eq ?_)
  have f5 : ∀ r : RsbR, r ≠ .ef → r ≠ .df → r ≠ .hf → r ≠ .msk → r ≠ .mwn → r ≠ .m2wn →
      r ≠ .m2n → r ≠ .smwn → r ≠ .tswn → r ≠ .kn → σ5 (.inl r) = σ2 (.inl r) := by
    intro r a1 a2 a3 a4 b1 b2 b3 b4 b5 b6
    simp only [hσ5, preF5, hσ4, preBankB, hσ3, preF3, Function.update_apply, Sum.inl.injEq, a1, a2,
      a3, a4, b1, b2, b3, b4, b5, b6, if_false]
  simp only [preScrB, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [f5 .ya (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    f5 .b1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    f5 .tb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    f5 .xa (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    f5 .xs (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    f5 .pr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    f5 .hc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    f5 .ac (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    v2ya, v2b1, v2tb, v2xa, v2xs, v2pr, v2hc, v2ac]
  simp only [List.length_replicate, preCostB, PreAxB.fields, List.sum_cons, List.sum_nil]
  ring

end Steps

/-! ### Consecutive loads -/

section Glue

open IntegerMultBounds.Schoenhage.Schedule (topN)
open IntegerMultBounds.Resampling.WeightTable (tableE tableD)

variable {A : ℕ}

/-- The register file before the stage: the loader scratch registers, the complex-product
registers other than `xs`, `ys`, `out`, `wn`, `pn`, `nn`, the line registers `dst`, `ms`, `sr`,
`sel`, `hv`, `vk`, `dout`, `tK` and the scratch of `RsbEnv`, the non-header bank registers,
`xt`, `e1`, `e2` are empty; `cm .wn` holds `w` symbols and `cm .nn` holds `topN w`. -/
structure PreBaseB (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (w : ℕ) (hd : Fin 5 → Fin t₀) :
    Prop where
  free : PreFreeB σ
  wn : (σ (.inl (.cm .wn))).length = w
  nn : (σ (.inl (.cm .nn))).length = topN w
  cm : ∀ c, c ≠ .xs → c ≠ .ys → c ≠ .out → c ≠ .wn → c ≠ .pn → c ≠ .nn → σ (.inl (.cm c)) = []
  dst : σ (.inl .dst) = []
  ms : σ (.inl .ms) = []
  hv : σ (.inl .hv) = []
  vk : σ (.inl .vk) = []
  dout : σ (.inl .dout) = []
  bank : ∀ j, (∀ k, reg (hd k) ≠ j) → σ (.inr (.sw j)) = []
  xt : σ (.inr .xt) = []
  e1 : σ (.inr .e1) = []
  e2 : σ (.inr .e2) = []

lemma rsbWith_inl_ne (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (l a a' : List (Fin (A + 4)))
    {r : RsbR} (hr : r ≠ .src) : rsbWith σ l a a' (.inl r) = σ (.inl r) := by
  simp only [rsbWith, Sum.elim_inl, Function.update_of_ne hr]

lemma rsbWith_sw (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (l a a' : List (Fin (A + 4)))
    (j : Fin (swapT t₀)) : rsbWith σ l a a' (.inr (.sw j)) = σ (.inr (.sw j)) := by
  simp only [rsbWith, Sum.elim_inr, Function.update_apply, reduceCtorEq, if_false]

lemma preLoadB_rsbWith (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (hd : Fin 5 → Fin t₀) (w : ℕ)
    (D : PreAxB) (r l a a' : List (Fin (A + 4))) :
    preLoadB (rsbWith σ l a a') hd w D r = rsbWith (preLoadB σ hd w D r) l a a' := by
  funext x
  rcases x with x | x
  · by_cases hx : x = .src
    · subst hx
      simp only [preLoadB, Function.update_apply, Sum.inl.injEq, reduceCtorEq, if_false,
        preBankB, rsbWith, Sum.elim_inl, Function.update_self]
    · rw [show rsbWith (preLoadB σ hd w D r) l a a' (.inl x) = preLoadB σ hd w D r (.inl x) from
        rsbWith_inl_ne _ _ _ _ hx]
      cases x <;> simp only [preLoadB, Function.update_apply, Sum.inl.injEq, reduceCtorEq,
        if_false, if_true, preBankB, RsbR.cm.injEq] <;> simp_all [rsbWith_inl_ne]
  · rcases x with j | _ | _ | _ | _ | _ <;>
      simp only [preLoadB, Function.update_apply, reduceCtorEq, if_false, preBankB, rsbWith,
        Sum.elim_inr, if_true]

lemma preLoadB_preLoadB (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (hd : Fin 5 → Fin t₀) (w : ℕ)
    (D D' : PreAxB) (r r' : List (Fin (A + 4))) :
    preLoadB (preLoadB σ hd w D r) hd w D' r' = preLoadB σ hd w D' r' := by
  funext x
  rcases x with x | x
  · cases x
    case cm c =>
      cases c <;> simp only [preLoadB, Function.update_apply, Sum.inl.injEq, reduceCtorEq,
        if_false, if_true, preBankB, RsbR.cm.injEq]
    all_goals simp only [preLoadB, Function.update_apply, Sum.inl.injEq, reduceCtorEq,
        if_false, if_true, preBankB]
  · rcases x with j | _ | _ | _ | _ | _ <;> simp only [preLoadB, Function.update_apply, preBankB,
      reduceCtorEq, if_false]
    split_ifs <;> rfl

lemma preLoadB_inl (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (hd : Fin 5 → Fin t₀) (w : ℕ)
    (D : PreAxB) (rest : List (Fin (A + 4))) {r : RsbR} (h1 : r ≠ .bo) (h2 : r ≠ .sn)
    (h3 : r ≠ .cm .pn) (h4 : r ≠ .mwn) (h5 : r ≠ .m2wn) (h6 : r ≠ .m2n) (h7 : r ≠ .smwn)
    (h8 : r ≠ .tswn) (h9 : r ≠ .kn) (h10 : r ≠ .ef) (h11 : r ≠ .df) (h12 : r ≠ .hf)
    (h13 : r ≠ .msk) : preLoadB σ hd w D rest (.inl r) = σ (.inl r) := by
  simp only [preLoadB, Function.update_apply, Sum.inl.injEq, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h13, if_false, preBankB]

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

lemma preCostB_rsbWith (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (hd : Fin 5 → Fin t₀) (w : ℕ)
    (D : PreAxB) (l a a' : List (Fin (A + 4))) :
    preCostB (rsbWith σ l a a') hd w D = preCostB σ hd w D := by
  unfold preCostB
  congr 5

/-- The stream of `tblStreamECode` is the off-diagonal table stream of the line machine. -/
theorem tblStreamE_cstream (w s t α p m : ℕ) :
    tblStreamE A w s t α p m = cstream A w (rsbETab s m (tableE s t α p)) := by
  have hw : tblWinE m = rsbHs m := by
    unfold tblWinE rsbHs
    congr 1
    · refine List.map_congr_left fun i hi => ?_
      have := List.mem_range.1 hi
      omega
  simp only [tblStreamE, rsbETab, cstream, List.flatMap_assoc, List.flatMap_map, hw]
  rfl

/-- The stream of `tblStreamDCode` is the diagonal table stream of the line machine. -/
theorem tblStreamD_cstream (w s t α p : ℕ) :
    tblStreamD A w s t α p = cstream A w (rsbArr fun ℓ => rsbReal (tableD s t α p ℓ)) := by
  simp only [tblStreamD, rsbArr, cstream, List.flatMap_map]
  rfl

/-- A loaded register file is configured for its axis. -/
theorem preLoadB_cfg {σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))} {w : ℕ} {hd : Fin 5 → Fin t₀}
    (h : PreBaseB σ w hd) (hA : 3 ≤ A) (D : PreAxB) (rest : List (Fin (A + 4))) :
    RsbAxisCfg (fun r => preLoadB σ hd w D rest (.inl r)) w D.p D.s D.t D.m (D.α ^ 2)
      (tableE D.s D.t D.α D.p) (tableD D.s D.t D.α D.p) := by
  have e : ∀ r : RsbR, r ≠ .bo → r ≠ .sn → r ≠ .cm .pn → r ≠ .mwn → r ≠ .m2wn → r ≠ .m2n →
      r ≠ .smwn → r ≠ .tswn → r ≠ .kn → r ≠ .ef → r ≠ .df → r ≠ .hf → r ≠ .msk →
      preLoadB σ hd w D rest (.inl r) = σ (.inl r) :=
    fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 =>
      preLoadB_inl σ hd w D rest h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  have v : ∀ r : RsbR, ∀ l : List (Fin (A + 4)), σ (.inl r) = l → r ≠ .bo → r ≠ .sn →
      r ≠ .cm .pn → r ≠ .mwn → r ≠ .m2wn → r ≠ .m2n → r ≠ .smwn → r ≠ .tswn → r ≠ .kn →
      r ≠ .ef → r ≠ .df → r ≠ .hf → r ≠ .msk → preLoadB σ hd w D rest (.inl r) = l :=
    fun r l hl h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 =>
      (e r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13).trans hl
  refine ⟨⟨⟨?_, ?_, ?_, fun c h1 h2 h3 h4 h5 h6 => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.wn
  · simp [preLoadB]
  · rw [e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.nn
  · rw [e _ (by simp) (by simp) (by simpa using h5) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]
    exact h.cm c h1 h2 h3 h4 h5 h6
  · simp [preLoadB]
  · simp [preLoadB]; ring
  · simp [preLoadB]
  · simp [preLoadB]
  · simp [preLoadB]
  all_goals first
    | (apply v _ _ h.free.ya <;> decide)
    | (apply v _ _ h.free.b1 <;> decide)
    | (apply v _ _ h.free.tb <;> decide)
    | (apply v _ _ h.free.xa <;> decide)
    | (apply v _ _ h.free.xs <;> decide)
    | (apply v _ _ h.free.pr <;> decide)
    | (apply v _ _ h.free.hc <;> decide)
    | (apply v _ _ h.free.ac <;> decide)
    | (apply v _ _ h.free.ac2 <;> decide)
    | (apply v _ _ h.free.nv <;> decide)
    | (apply v _ _ h.free.tC <;> decide)
    | (apply v _ _ h.free.tA <;> decide)
    | (apply v _ _ h.free.tJ <;> decide)
    | (apply v _ _ h.free.tL <;> decide)
    | (apply v _ _ h.free.tK <;> decide)
    | (apply v _ _ h.free.sr <;> decide)
    | (apply v _ _ h.free.sel <;> decide)
    | (apply v _ _ h.dst <;> decide)
    | (apply v _ _ h.ms <;> decide)
    | (apply v _ _ h.hv <;> decide)
    | (apply v _ _ h.vk <;> decide)
    | (apply v _ _ h.dout <;> decide)
    | skip
  · simp [preLoadB, preMaskE_map hA]
  · simp [preLoadB, tblStreamE_cstream]
  · simp [preLoadB, tblStreamD_cstream]
  · simp [preLoadB, tbl_pairs_red, rsbReal]
  · simp [preLoadB, sq]
  · simp [preLoadB]

end Glue

/-! ### The loader contract of `rsb_all_runs` -/

section Contract

variable {body : F → Pr F T Q (prime + K) U} {rg : RsbR → Fin T} {rgx : RsbX t₀ → Fin T}
  {ι : Fin 64 → Fin T}

/-- **The contract `hprep` of `rsb_all_runs`.** For every box stream `l` and axis counter `a`,
`a'`, `preB` takes `rsbWith σ l a a'` to `rsbWith (preLoadB σ hd w D rest) l a a'` within
`preCostB σ hd w D` steps (the record `D` on top of `bo`, `rest` below it). -/
theorem preB_rsbWith (hrg₂ : Function.Injective (Sum.elim rg rgx)) (hι : Function.Injective ι)
    (hdisj₂ : ∀ r j, Sum.elim rg rgx r ≠ ι j) {hd : Fin 5 → Fin t₀} (hdi : Function.Injective hd)
    (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB)
    (rest : List (Fin (prime + K + 4))) (w : ℕ) (hF : PreFreeB σ)
    (hout : σ (.inl .bo) = preRec D.fields ++ rest) (hwn : (σ (.inl (.cm .wn))).length = w)
    (hp : 13 ≤ D.p) (hα : 2 ≤ D.α) (hαp : D.α ^ 2 ≤ D.p) (hs : 0 < D.s) (hst : D.s < D.t)
    (hwW : w ≤ D.W)
    (hW : D.α ^ 2 * ((D.s + D.t) * (D.m + 1)) ^ 2 * 2 ^ (13 * D.p + 8) < 2 ^ D.W)
    (l a a' : List (Fin (prime + K + 4))) :
    RsbRuns body (Sum.elim rg rgx) ι (preB rg rgx ι hd) (rsbWith σ l a a')
      (rsbWith (preLoadB σ hd w D rest) l a a') (preCostB σ hd w D) := by
  have h := preB_runs (body := body) hrg₂ hι hdisj₂ hdi (rsbWith σ l a a') D rest w
    (hF.rsbWith l a a') (by rw [rsbWith_inl_ne _ _ _ _ (by decide), hout])
    (by rw [rsbWith_inl_ne _ _ _ _ (by decide)]; exact hwn) hp hα hαp hs hst hwW hW
  rw [preLoadB_rsbWith, preCostB_rsbWith] at h
  exact pre_rsbRuns h

end Contract

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
  sxBits (BinaryInterchangeRun.values (rsbPre (t n) i) (rsbMid (t n) i) (3 * w)
    (Nat.log 2 (t n i)) (Nat.log 2 (t n (rsbAx hd0 0))) k)

/-- The register file configured for step `k`. -/
def preCfgB {A : ℕ} (σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (hd : Fin 5 → Fin t₀)
    (n w W : ℕ) (hd0 : 0 < d n) (rest : List (Fin (A + 4))) (k : ℕ) :
    RsbR ⊕ RsbX t₀ → List (Fin (A + 4)) :=
  preLoadB σ₀ hd w (preDB n W hd0 k) (preRecsB n W hd0 (k + 1) ++ rest)

/-- The step bound of the loader at step `k`. -/
def preCpB {A : ℕ} (σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (hd : Fin 5 → Fin t₀)
    (n w W : ℕ) (hd0 : 0 < d n) (rest : List (Fin (A + 4))) : ℕ → ℕ
  | 0 => preCostB σ₀ hd w (preDB n W hd0 0)
  | k + 1 => preCostB (preCfgB σ₀ hd n w W hd0 rest k) hd w (preDB n W hd0 (k + 1))

variable {body : F → Pr F T Q (prime + K) U} {rg : RsbR → Fin T} {rgx : RsbX t₀ → Fin T}
  {ι : Fin 64 → Fin T}

set_option maxHeartbeats 4000000 in
/-- **The `B̃₀` stage with its loader.** At operand length `n` in the regime `Big n`, width
`w ≥ p n + 2` and table word size `W ≥ w` with `α² ((s_i + t_i)(m + 1))² 2^(13p+8) < 2^W` on every
axis (`m = fastWindow p α`): from a base register file `σ₀` (`PreBaseB`) whose parameter register
`bo` holds the records of the pipeline (`preRecsB`) followed by `rest`, with the box register
holding the padded stream of the numerators of `u` at scale `p n` (`‖u‖ ≤ 1`),
`rsbAllP (preB rg rgx ι hd)` ends with the box register holding the numerators of
`tensorZR (d n) (t n) (s n) (lineBN n) u` at scale `p n` (zero off the source box), the register
file configured for axis `0` and `rest` on `bo`. -/
theorem rsbStage_exec (n : ℕ) (hbig : Big n) (hd0 : 0 < d n)
    (hrg₂ : Function.Injective (Sum.elim rg rgx)) (hdisj₂ : ∀ r j, Sum.elim rg rgx r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ prime + K)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQs : swapStates hd pay hi ≤ Q) (hsw : Function.Injective fun j => rgx (.sw j))
    (hTs : swapT t₀ ≤ T) (hdpay : ∀ k, hd k ≠ pay) {w W : ℕ} (hw : p n + 2 ≤ w) (hwW : w ≤ W)
    (hW : ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) *
      (Mult.FastB0.fastWindow (p n) (alpha n) + 1)) ^ 2 * 2 ^ (13 * p n + 8) < 2 ^ W)
    (σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hσ₀ : PreBaseB σ₀ w hd)
    (rest : List (Fin (prime + K + 4))) (hout : σ₀ (.inl .bo) = preRecsB n W hd0 0 ++ rest)
    (u : ((i : Fin (d n)) → ZMod (t n i)) → ℂ)
    (Fn : ((i : Fin (d n)) → Fin (t n i)) → GaussianInt)
    (hF : ∀ x : (i : Fin (d n)) → Fin (t n i),
      u (fun i => ((x i : ℕ) : ZMod (t n i))) = GaussianInt.toComplex (Fn x) / 2 ^ p n)
    (hu : ∀ x : (i : Fin (d n)) → Fin (t n i), ‖u (fun i => ((x i : ℕ) : ZMod (t n i)))‖ ≤ 1)
    (axs : List (Fin (prime + K + 4))) (haxs : axs.length = d n - 1) :
    ∃ G : ((i : Fin (d n)) → Fin (t n i)) → GaussianInt,
      (∀ x : (i : Fin (d n)) → Fin (t n i), (∀ i, (x i : ℕ) < s n i) →
        tensorZR (d n) (t n) (s n) (lineBN n) u (fun i => ((x i : ℕ) : ZMod (s n i))) =
          GaussianInt.toComplex (G x) / 2 ^ p n) ∧
      (∀ x : (i : Fin (d n)) → Fin (t n i), (∃ i, s n i ≤ x i) → G x = 0) ∧
      RsbRuns body (Sum.elim rg rgx) ι (rsbAllP (preB rg rgx ι hd) rg rgx hι hT hQ hd pay hi hQs
        hsw hTs)
        (rsbWith σ₀ (cstream (prime + K) w (rsbBox (d n) (t n) Fn)) axs [])
        (rsbWith (preCfgB σ₀ hd n w W hd0 rest (d n - 1))
          (cstream (prime + K) w (rsbBox (d n) (t n) G)) axs [])
        (rsbAllCost T t₀ w (Mult.FastB0.fastWindow (p n) (alpha n)) (alpha n ^ 2) (d n) (t n) hd0
          (rsbLineBData n (fun i => Nat.log 2 (t n i)) (preHsB n w hd0)) (prime + K) hd
          (preCpB σ₀ hd n w W hd0 rest) (∏ i, t n i)) := by
  have hp13 := hbig.thirteen_le_p
  have hα2 := two_le_alpha hbig.1
  have hαp := hbig.alpha_sq_le_p
  have hspos : ∀ i, 0 < s n i := fun i => Nat.pos_of_ne_zero (NeZero.ne (s n i))
  set cfg := preCfgB σ₀ hd n w W hd0 rest with hcfg
  have hprep₀ : ∀ l a a', RsbRuns body (Sum.elim rg rgx) ι (preB rg rgx ι hd) (rsbWith σ₀ l a a')
      (rsbWith (cfg 0) l a a') (preCpB σ₀ hd n w W hd0 rest 0) := by
    intro l a a'
    exact preB_rsbWith hrg₂ hι hdisj₂ hi σ₀ (preDB n W hd0 0) (preRecsB n W hd0 1 ++ rest) w
      hσ₀.free (by rw [hout, preRecsB_succ n W hd0 hd0, List.append_assoc]) hσ₀.wn hp13 hα2 hαp
      (hspos _) (hbig.good.lt _) hwW (hW _) l a a'
  have hprep : ∀ k, k + 1 < d n → ∀ l a a', RsbRuns body (Sum.elim rg rgx) ι (preB rg rgx ι hd)
      (rsbWith (cfg k) l a a') (rsbWith (cfg (k + 1)) l a a')
      (preCpB σ₀ hd n w W hd0 rest (k + 1)) := by
    intro k hk l a a'
    have h := preB_rsbWith (body := body) hrg₂ hι hdisj₂ hi (cfg k) (preDB n W hd0 (k + 1))
      (preRecsB n W hd0 (k + 2) ++ rest) w (hσ₀.free.load hd w _ _)
      (by
        rw [hcfg, preCfgB, preLoadB]
        simp only [Function.update_apply, Sum.inl.injEq, reduceCtorEq, if_false, if_true]
        rw [preRecsB_succ n W hd0 hk, List.append_assoc])
      (by
        rw [hcfg, preCfgB, preLoadB_inl _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)]
        exact hσ₀.wn)
      hp13 hα2 hαp (hspos _) (hbig.good.lt _) hwW (hW _) l a a'
    rwa [hcfg, preCfgB, preLoadB_preLoadB] at h
  have hlast : rsbAx hd0 0 = ResampA.rsaStepAx hd0 0 := rfl
  refine rsb_all_lineB_disk n hbig (fun i => Nat.log 2 (t n i)) (preHsB n w hd0)
    (preB rg rgx ι hd) hrg₂ hdisj₂ hι hT hQ hA hd pay hi hQs hsw hTs hdpay hd0 hw (t_pow_log n)
    (fun i => by
      have h3 := Mult.FastB0.fastWindow_le_third hα2 hp13
      have := pre_p_le_s hbig i
      omega)
    (fun i hi1 => ?_) σ₀ cfg (fun k hk => ?_) (preCpB σ₀ hd n w W hd0 rest) hprep₀ hprep u Fn hF
    hu axs haxs
  · have hl := pre_log_last hbig hd0
    rw [← hlast] at hl
    refine ⟨?_, ?_, fun k => ?_, fun k => canonical_sxBits _⟩
    · rw [hl]; rcases pre_log_t (n := n) i with e | e <;> omega
    · rw [hl]
      rcases pre_log_t (n := n) i with e | e <;> rw [e] <;> have := hbig.two_le_ℓ <;> omega
    · simp only [preHsB, value_sxBits]
  · refine ⟨preLoadB_cfg hσ₀ (by omega) _ _, fun _ => ⟨fun j => ?_, ?_, ?_, ?_⟩⟩
    · simp only [hcfg, preCfgB, preLoadB, Function.update_apply, reduceCtorEq, if_false, preBankB]
      split_ifs with hj
      · rfl
      · rw [rsbBank_other _ (fun k e => hj ⟨k, e⟩)]
        exact hσ₀.bank j (fun k e => hj ⟨k, e⟩)
    · simp only [hcfg, preCfgB, preLoadB, Function.update_apply, reduceCtorEq, if_false, preBankB]
      exact hσ₀.xt
    · simp only [hcfg, preCfgB, preLoadB, Function.update_apply, reduceCtorEq, if_false, preBankB]
      exact hσ₀.e1
    · simp only [hcfg, preCfgB, preLoadB, Function.update_apply, reduceCtorEq, if_false, preBankB]
      exact hσ₀.e2

end Stage

end

end IntegerMultBounds.MathlibTM2.Fast
