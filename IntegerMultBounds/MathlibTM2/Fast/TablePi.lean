module

public import IntegerMultBounds.MathlibTM2.Fast.TableProg
public import IntegerMultBounds.Resampling.PiNat

/-!
# Machin's `π` on the table machine

`tblPiCode` computes `piN P = (piQ P).toNat`, the integer approximation of `2^(5P) π` of
`Resampling.WeightTable.piQ`, from `P` in variable `0` into variable `15` (`tblPiOut`):

* `q := 5 P`, `pw := 2^q` (`tblPow2`);
* for `m = 5` and `m = 239` (`tblAtanCode m`): `D := ⌊pw / m⌋`, then for `k < q` the term
  `⌊D / (2k + 1)⌋` goes to the even or the odd sum by the parity of `k`, and `D := ⌊D / m²⌋`;
  the result is `even − odd = atanN m q q` (`Resampling.PiNat`);
* `piN P = 16 atanN 5 q q − 4 atanN 239 q q` (`PiNat.piN_eq`).

`tblPi_do`: for `2 ≤ P` and words of `W ≥ 5 P + 16` bits, the program ends with
`piN P` in `tblPiOut` and `acc` unchanged, within `120 P + 400` atoms. `tblPi_eq_piQ`:
`(piN P : ℤ) = piQ P`. The host cost is at most `(120 P + 400) · tblC W w` steps
(`tblCompile_runs`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds.Resampling IntegerMultBounds.Resampling.PiNat


/-! ### Variables -/

/-- Input variable: `P`. -/
abbrev tblPiIn : Fin 18 := 0
local notation "vQ" => (1 : Fin 18)
local notation "vPw" => (2 : Fin 18)
local notation "vM" => (3 : Fin 18)
local notation "vMM" => (4 : Fin 18)
local notation "vD" => (5 : Fin 18)
local notation "vT" => (6 : Fin 18)
local notation "vK" => (7 : Fin 18)
local notation "vEv" => (8 : Fin 18)
local notation "vOd" => (9 : Fin 18)
local notation "vTm" => (10 : Fin 18)
local notation "vPar" => (11 : Fin 18)
local notation "vOne" => (12 : Fin 18)
local notation "vA5" => (13 : Fin 18)
local notation "vA239" => (14 : Fin 18)
/-- Output variable: `piN P`. -/
abbrev tblPiOut : Fin 18 := 15
local notation "vX" => (16 : Fin 18)
local notation "vI" => (17 : Fin 18)

/-! ### The program -/

/-- `out := atanN m q q`, from `pw = 2^q` in `vPw`, `q` in `vQ` and `1` in `vOne`. -/
def tblAtanCode (m : ℕ) (out : Fin 18) : TblCode 18 :=
  tblBlock 18 (tblConstL vM m ++ [.mul vM vM vMM, .div vPw vM vD, .zero vEv, .zero vOd, .zero vPar,
      .zero vT]) (.inc vT) ;;
    tblFor vK vQ (tblBlock 18 [.div vD vT vTm, .sub vOne vPar vX, .mul vTm vX vI, .add vEv vI vEv,
      .mul vTm vPar vI, .add vOd vI vOd, .div vD vMM vD, .inc vT, .inc vT] (.sub vOne vPar vPar)) ;;
    .ins (.sub vEv vOd out)

/-- `tblPiOut := piN P` from `P` in `tblPiIn`. -/
def tblPiCode : TblCode 18 :=
  tblBlock 18 (tblConstL vOne 1 ++ tblConstL vX 5) (.mul tblPiIn vX vQ) ;; tblPow2 vPw vQ vI ;;
    tblAtanCode 5 vA5 ;; tblAtanCode 239 vA239 ;;
    tblBlock 18 (tblConstL vX 16 ++ tblConstL vI 4 ++ [.mul vA5 vX tblPiOut, .mul vA239 vI vX])
      (.sub tblPiOut vX tblPiOut)

/-! ### Arithmetic facts -/

theorem tbl_ev_od_bound (m q : ℕ) (hm : 2 ≤ m) :
    ∀ j, evA m q j + odA m q j + 2 * dSeq m q j ≤ 2 * dSeq m q 0 := by
  intro j
  induction j with
  | zero => simp [evA, odA]
  | succ j ih =>
    have ht : term m q j ≤ dSeq m q j := Nat.div_le_self _ _
    have hd : 2 * dSeq m q (j + 1) ≤ dSeq m q j := by
      rw [dSeq]
      have h4 : 4 ≤ m * m := by nlinarith
      calc 2 * (dSeq m q j / (m * m)) ≤ 2 * (dSeq m q j / 4) :=
            Nat.mul_le_mul_left _ (Nat.div_le_div_left h4 (by norm_num))
        _ ≤ dSeq m q j := by omega
    have hsplit : evA m q (j + 1) + odA m q (j + 1) = evA m q j + odA m q j + term m q j := by
      simp only [evA, odA]
      rcases Nat.mod_two_eq_zero_or_one j with h | h <;> simp [h] <;> omega
    omega

theorem tbl_dSeq0_le (m q : ℕ) : dSeq m q 0 ≤ 2 ^ q := Nat.div_le_self _ _

/-! ### Correctness -/

/-- The variables written by `tblAtanCode` besides its output. -/
def tblAtanTouched : List (Fin 18) := [vM, vMM, vD, vT, vK, vEv, vOd, vTm, vPar, vX, vI]

theorem tblAtan_do {A W w : ℕ} (m : ℕ) (out : Fin 18) (hm : 5 ≤ m) (hmW : m * m < 2 ^ W) (st : TblSt 18 A) {q : ℕ} (hq : st.val vQ = q)
    (hpw : st.val vPw = 2 ^ q) (hone : st.val vOne = 1) (hqW : q + 3 ≤ W) :
    TblDo A W w (tblAtanCode m out) st (fun s => s.val out = atanN m q q ∧
      (∀ x, x ∉ tblAtanTouched → x ≠ out → s.val x = st.val x) ∧ s.acc = st.acc)
      (13 * q + m + 12) := by
  have hpq : 2 ^ (q + 3) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hqW
  have hq3 : 2 ^ (q + 3) = 8 * 2 ^ q := by rw [pow_add]; ring
  have hqlt : q < 2 ^ q := Nat.lt_two_pow_self
  have hmm : m ≤ m * m := Nat.le_mul_self m
  have hmW' : m < 2 ^ W := lt_of_le_of_lt hmm hmW
  have hdq : 2 ^ q / m ≤ 2 ^ q := Nat.div_le_self _ _
  -- the initial block
  set l₁ : List (TblIns 18) := tblConstL vM m ++ [.mul vM vM vMM, .div vPw vM vD, .zero vEv,
    .zero vOd, .zero vPar, .zero vT] with hl₁
  have hf₁ : tblFitsList A W w (l₁ ++ [.inc vT]) st := by
    rw [hl₁, List.append_assoc]
    refine tblFitsList_append _ _ _ (tblFitsList_const _ _ _ hmW') ?_
    rw [tblExactList_const]
    simp [tblFitsList, TblIns.fits, TblIns.exact]
    omega
  set s₁ := tblExactList A w (l₁ ++ [.inc vT]) st with hs₁
  have hv₁ : s₁.val vMM = m * m ∧ s₁.val vD = 2 ^ q / m ∧ s₁.val vEv = 0 ∧ s₁.val vOd = 0 ∧
      s₁.val vPar = 0 ∧ s₁.val vT = 1 ∧ s₁.val vQ = q ∧
      (∀ x, x ∉ tblAtanTouched → s₁.val x = st.val x) ∧ s₁.acc = st.acc := by
    rw [hs₁, hl₁, List.append_assoc, tblExactList_append, tblExactList_const]
    simp [tblExactList, TblIns.exact, Function.update_apply, hpw, hq]
    intro x hx
    simp only [tblAtanTouched, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp [hx]
  obtain ⟨hMM, hD, hEv, hOd, hPar, hT, hQ, hfr, hacc⟩ := hv₁
  have hD0 : dSeq m q 0 = 2 ^ q / m := rfl
  have hbd := fun j => tbl_ev_od_bound m q (by omega) j
  have hDle : ∀ j, dSeq m q j ≤ 2 ^ q := fun j => by
    have := hbd j; rw [hD0] at this; omega
  have hEvle : ∀ j, evA m q j ≤ 2 * 2 ^ q := fun j => by
    have := hbd j; rw [hD0] at this; omega
  have hOdle : ∀ j, odA m q j ≤ 2 * 2 ^ q := fun j => by
    have := hbd j; rw [hD0] at this; omega
  let Inv : ℕ → TblSt 18 A → Prop := fun j s => s.val vD = dSeq m q j ∧ s.val vEv = evA m q j ∧
    s.val vOd = odA m q j ∧ s.val vT = 2 * j + 1 ∧ s.val vPar = j % 2 ∧ s.val vMM = m * m ∧
    (∀ x, x ∉ tblAtanTouched → s.val x = st.val x) ∧ s.acc = st.acc
  have hloop : TblDo A W w (tblFor vK vQ (tblBlock 18 [.div vD vT vTm, .sub vOne vPar vX,
      .mul vTm vX vI, .add vEv vI vEv, .mul vTm vPar vI, .add vOd vI vOd, .div vD vMM vD, .inc vT,
      .inc vT] (.sub vOne vPar vPar))) s₁ (fun s => s.val vEv = evA m q q ∧
        s.val vOd = odA m q q ∧ (∀ x, x ∉ tblAtanTouched → s.val x = st.val x) ∧ s.acc = st.acc)
      (1 + (q * (10 + 1 + 2) + 2)) := by
    refine TblDo.for q 10 hQ (by omega) (by decide) Inv ?_ ?_ ?_
    · refine ⟨by simp [hD, hD0], by simp [hEv, evA], by simp [hOd, odA], by simp [hT],
        by simp [hPar], by simp [hMM], fun x hx => ?_, hacc⟩
      have : x ≠ vK := by intro h; subst h; simp [tblAtanTouched] at hx
      simp [Function.update_of_ne this, hfr x hx]
    · intro j hj s ⟨hD', hEv', hOd', hT', hPar', hMM', hfr', hacc'⟩ hK' hQ'
      have hone' : s.val vOne = 1 := by rw [hfr' vOne (by simp [tblAtanTouched]), hone]
      have hpar1 : j % 2 ≤ 1 := by omega
      have htm : dSeq m q j / (2 * j + 1) ≤ 2 ^ q := (Nat.div_le_self _ _).trans (hDle j)
      have hevs : evA m q (j + 1) = evA m q j + dSeq m q j / (2 * j + 1) * (1 - j % 2) := by
        simp only [evA, term]
        rcases Nat.mod_two_eq_zero_or_one j with h | h <;> simp [h]
      have hods : odA m q (j + 1) = odA m q j + dSeq m q j / (2 * j + 1) * (j % 2) := by
        simp only [odA, term]
        rcases Nat.mod_two_eq_zero_or_one j with h | h <;> simp [h]
      have hev1 := hEvle (j + 1)
      have hod1 := hOdle (j + 1)
      refine TblDo.block _ _ ?_ ?_
      · simp [tblFitsList, TblIns.fits, TblIns.exact, hD', hEv', hOd', hT',
          hPar', hMM', hone']
        have h1 : dSeq m q j / (2 * j + 1) * (1 - j % 2) ≤ 2 ^ q :=
          (Nat.mul_le_mul_left _ (by omega : 1 - j % 2 ≤ 1)).trans (by simpa using htm)
        have h2 : dSeq m q j / (2 * j + 1) * (j % 2) ≤ 2 ^ q :=
          (Nat.mul_le_mul_left _ hpar1).trans (by simpa using htm)
        refine ⟨⟨hpar1, by omega⟩, by omega, by rw [← hevs]; omega, by omega, by rw [← hods]; omega,
          by omega, by omega, hpar1, by omega⟩
      · simp only [Inv]
        simp [tblExactList, TblIns.exact, Function.update_apply, hD', hEv', hOd', hT',
          hPar', hMM', hone', hK', hQ']
        refine ⟨rfl, hevs.symm, hods.symm, by omega, by omega, fun x hx => ?_, hacc'⟩
        simp only [tblAtanTouched, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        simp [hx, hfr' x (by simp [tblAtanTouched, hx])]
    · intro s ⟨hD', hEv', hOd', hT', hPar', hMM', hfr', hacc'⟩ _ _
      exact ⟨hEv', hOd', hfr', hacc'⟩
  have hfin : ∀ s : TblSt 18 A, (s.val vEv = evA m q q ∧ s.val vOd = odA m q q ∧
      (∀ x, x ∉ tblAtanTouched → s.val x = st.val x) ∧ s.acc = st.acc) →
      TblDo A W w (.ins (.sub vEv vOd out)) s (fun s => s.val out = atanN m q q ∧
        (∀ x, x ∉ tblAtanTouched → x ≠ out → s.val x = st.val x) ∧ s.acc = st.acc) 1 := by
    intro s ⟨h1, h2, h3, h4⟩
    have hle := od_le_ev' m q q
    have hlt := hEvle q
    refine TblDo.insX _ ⟨by rw [h1, h2]; exact hle, by rw [h1]; omega⟩ ⟨?_, fun x hx hxo => ?_, h4⟩
    · simp [TblIns.exact, h1, h2, atanN]
    · simp [TblIns.exact, Function.update_of_ne hxo, h3 x hx]
  exact ((TblDo.block l₁ (.inc vT) hf₁ (P := fun s => s = s₁) rfl).seq
    (fun s hs => hs ▸ hloop.seq hfin)).mono (fun _ h => h) (by simp [hl₁]; omega)

theorem tbl_atanN_le (m q : ℕ) (hm : 2 ≤ m) : atanN m q q ≤ 2 * 2 ^ q := by
  have h := tbl_ev_od_bound m q hm q
  have h0 : dSeq m q 0 ≤ 2 ^ q := Nat.div_le_self _ _
  unfold atanN
  omega

theorem tbl_atan_le (p : ℕ) (hp : 2 ≤ p) :
    4 * atanN 239 (5 * p) (5 * p) ≤ 16 * atanN 5 (5 * p) (5 * p) := by
  have h0 := WeightTable.piQ_nonneg p hp
  rw [WeightTable.piQ, PiApprox.piApprox, atanSum_eq_atanN, atanSum_eq_atanN] at h0
  omega

/-- **Machin's `π`.** From `P ≥ 2` in `tblPiIn` and words of `W ≥ 5 P + 16` bits, `tblPiCode`
ends with `piN P` in `tblPiOut` and `acc` unchanged, within `150 P + 400` atoms. -/
theorem tblPi_do {A W w : ℕ} (st : TblSt 18 A) {P : ℕ} (hP : 2 ≤ P) (hin : st.val tblPiIn = P)
    (hW : 5 * P + 16 ≤ W) :
    TblDo A W w tblPiCode st (fun s => s.val tblPiOut = WeightNat.piN P ∧ s.acc = st.acc)
      (150 * P + 400) := by
  have hin0 : st.val 0 = P := hin
  obtain ⟨q, hq⟩ : ∃ q, q = 5 * P := ⟨_, rfl⟩
  have hqW : 2 ^ (q + 16) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h16 : 2 ^ (q + 16) = 2 ^ q * 65536 := by rw [pow_add]; norm_num
  have hqlt : q < 2 ^ q := Nat.lt_two_pow_self
  -- `one := 1`, `x := 5`, `q := 5 P`
  have hf₁ : tblFitsList A W w (tblConstL vOne 1 ++ tblConstL vX 5 ++ [.mul tblPiIn vX vQ]) st := by
    refine tblFitsList_append _ _ _ (tblFitsList_append _ _ _ (tblFitsList_const _ _ _ (by omega))
      (tblFitsList_const _ _ _ (by omega))) ?_
    rw [tblExactList_append, tblExactList_const, tblExactList_const]
    simp [tblFitsList, TblIns.fits, tblPiIn, hin0]
    omega
  set s₁ := tblExactList A w (tblConstL vOne 1 ++ tblConstL vX 5 ++ [.mul tblPiIn vX vQ]) st
    with hs₁
  have hv₁ : s₁.val vOne = 1 ∧ s₁.val vQ = q ∧ s₁.acc = st.acc := by
    rw [hs₁, tblExactList_append, tblExactList_append, tblExactList_const, tblExactList_const]
    simp [tblExactList, TblIns.exact, tblPiIn, hin0, hq]
    ring
  obtain ⟨hone₁, hq₁, hacc₁⟩ := hv₁
  have hpow := tblPow2_do (A := A) (W := W) (w := w) (c := vPw) (e := vQ) (i := vI) (by decide)
    (by decide) (by decide) s₁ (by rw [hq₁]; omega)
  have h5 := tbl_atanN_le 5 q (by norm_num)
  have h239 := tbl_atanN_le 239 q (by norm_num)
  have hle := tbl_atan_le P hP
  rw [← hq] at hle
  have hfin : ∀ s₄ : TblSt 18 A, s₄.val vA5 = atanN 5 q q → s₄.val vA239 = atanN 239 q q →
      TblDo A W w (tblBlock 18 (tblConstL vX 16 ++ tblConstL vI 4 ++
        [.mul vA5 vX tblPiOut, .mul vA239 vI vX]) (.sub tblPiOut vX tblPiOut)) s₄
        (fun s => s.val tblPiOut = WeightNat.piN P ∧ s.acc = s₄.acc) (17 + 5 + 2 + 1) := by
    intro s₄ ha5 ha239
    refine TblDo.block _ _ ?_ ?_
    · rw [List.append_assoc, List.append_assoc]
      refine tblFitsList_append _ _ _ (tblFitsList_const _ _ _ (by omega)) ?_
      rw [tblExactList_const]
      refine tblFitsList_append _ _ _ (tblFitsList_const _ _ _ (by omega)) ?_
      rw [tblExactList_const]
      simp [tblFitsList, TblIns.fits, TblIns.exact, tblPiOut, ha5, ha239]
      omega
    · rw [List.append_assoc, List.append_assoc, tblExactList_append, tblExactList_const,
        tblExactList_append, tblExactList_const]
      simp [tblExactList, TblIns.exact, tblPiOut, ha5, ha239, PiNat.piN_eq P hP, ← hq]
      ring_nf
  refine ((TblDo.block _ _ hf₁ (P := fun s => s = s₁) rfl).seq
    (K₂ := (4 * q + 5) + ((13 * q + 5 + 12) + ((13 * q + 239 + 12) + (17 + 5 + 2 + 1))))
    (fun s hs => ?_)).mono (fun _ h => h) ?_
  · subst hs
    rw [hq₁] at hpow
    refine hpow.seq (fun s₂ ⟨hpw₂, _, hfr₂, hacc₂⟩ => ?_)
    have hq₂ : s₂.val vQ = q := by rw [hfr₂ vQ (by decide) (by decide), hq₁]
    have hone₂ : s₂.val vOne = 1 := by rw [hfr₂ vOne (by decide) (by decide), hone₁]
    refine (tblAtan_do 5 vA5 (by norm_num) (by omega) s₂ hq₂ hpw₂ hone₂ (by omega)).seq
      (fun s₃ ⟨ha5, hfr₃, hacc₃⟩ => ?_)
    have hq₃ : s₃.val vQ = q := by rw [hfr₃ vQ (by decide) (by decide), hq₂]
    have hpw₃ : s₃.val vPw = 2 ^ q := by rw [hfr₃ vPw (by decide) (by decide), hpw₂]
    have hone₃ : s₃.val vOne = 1 := by rw [hfr₃ vOne (by decide) (by decide), hone₂]
    refine (tblAtan_do 239 vA239 (by norm_num) (by omega) s₃ hq₃ hpw₃ hone₃
      (by omega)).seq (fun s₄ ⟨ha239, hfr₄, hacc₄⟩ => ?_)
    refine (hfin s₄ (by rw [hfr₄ vA5 (by decide) (by decide), ha5]) ha239).mono
      (fun s ⟨h1, h2⟩ => ⟨h1, by rw [h2, hacc₄, hacc₃, hacc₂, hacc₁]⟩) le_rfl
  · simp only [List.length_append, length_tblConstL]
    omega

/-- `piN P` is `piQ P` for `P ≥ 2`. -/
theorem tblPi_eq_piQ (P : ℕ) (hP : 2 ≤ P) : (WeightNat.piN P : ℤ) = WeightTable.piQ P :=
  Int.toNat_of_nonneg (WeightTable.piQ_nonneg P hP)

section Host

variable {T Q A : ℕ} {U : Type} {P' : Type} {body : P' → IntegerMultBounds.MathlibTM2.Host.Pr P' T Q A U}
  {rg : TblR 18 → Fin T}

/-- **The `π` machine on the host.** From registers carrying a state with `P ≥ 2` in `tblPiIn`
and all values below `2 ^ W`, `W = 5 P + 16`, the host program `tblCompile rg tblPiCode` reaches
registers carrying a state with `piQ P` in `tblPiOut` (as a natural number, `tblPi_eq_piQ`) and
`acc` unchanged, in at most `(150 P + 400) (32 (5 P + 20)² + 8 w)` steps, every register
outside the layout unchanged. -/
theorem tblPi_host (hrg : Function.Injective rg) {P w : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = 5 * P + 16) (hnl : nl.length = w) (hw : w ≤ 5 * P + 16)
    (st : TblSt 18 A) (hst : ∀ j, st.val j < 2 ^ (5 * P + 16)) (hP : 2 ≤ P)
    (hin : st.val tblPiIn = P) :
    ∃ st', (st'.val tblPiOut : ℤ) = WeightTable.piQ P ∧ st'.acc = st.acc ∧
      tblRuns body rg (tblCompile rg tblPiCode) (tblRho (5 * P + 16) wl nl st)
        (tblRho (5 * P + 16) wl nl st') ((150 * P + 400) * (32 * (5 * P + 20) ^ 2 + 8 * w)) := by
  obtain ⟨st', ⟨h1, h2⟩, hr⟩ := (tblPi_do (A := A) (W := 5 * P + 16) (w := w) st hP hin le_rfl).host
    (body := body) hrg wl nl hwl hnl hw hst
  refine ⟨st', by rw [h1, tblPi_eq_piQ P hP], h2, hr.mono (le_of_eq ?_)⟩
  simp only [tblC]

end Host

end IntegerMultBounds.MathlibTM2.Fast.TableVM
