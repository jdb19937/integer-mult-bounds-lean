module

public import IntegerMultBounds.MathlibTM2.Fast.TablePi
public import IntegerMultBounds.MathlibTM2.Fast.TableNum

/-!
# Taylor magnitudes and the weight routine on the table machine

## The magnitude loop

`tblMagCode` (18 variables) computes the four residue-class sums
`tblSum Y q Q r N = ∑_{m < N, m ≡ r (4)} M_m` of the Taylor magnitudes
`M_0 = 2^q`, `M_{m+1} = ⌊M_m Y / (2^Q (m+1))⌋` (`TableNum.tblMag`), from `Y`, `2^q`, `2^Q`, `N`
in variables `0 … 3` into variables `4 … 7`. Each iteration adds `M_m` to the class of `m`
through the indicators `[m ≡ r] = 1 − ⌊((m mod 4 + 4 − r) mod 4 + 3) / 4⌋`, then updates
`M`. `tblMag_do`: the sums, the inputs unchanged, `39 N + 30` atoms, under no-overflow bounds.

The same loop serves the weight tables (`WeightNat.mag Y q = tblMag Y q q`, `tbl_wmag_eq`) and
the Taylor sums of the phase tables (`TableNum.tblCre`, `TableNum.tblCim`).

## The weight routine

`tblExpCode` (34 variables) computes `WeightNat.expPiNat neg p a b` from `piN p`, `p`, `a`, `b`
and `neg ∈ {0, 1}` in variables `18 … 22` into variable `23`: `Y = ⌊piN · a / b⌋`, `q = 5 p`,
`2^q` and `2^(4p)` by doublings, the shortcut `p 2^q ≤ Y ↦ 0`, otherwise the magnitude loop
(embedded on variables `0 … 17`) with `Q = q`, `N = 7 p`, the even and odd sums
(`tbl_evenSum_eq`, `tbl_oddSum_eq`, `tbl_allSum_eq`) and the division by `2^(4p)`.
`tblExp_do`: the result, the inputs unchanged, at most `310 p + 100` atoms, for `13 ≤ p`,
`13 p + 8 ≤ W`, `a 2^(5p+2) < 2^W` and, in the positive case, `Y < p 2^(5p)`;
`tblExp_do_expPi`: the result is `WeightTable.expPi neg p a b`. `tbl_expApprox_neg`,
`tbl_expApprox_pos`: the Taylor sums `ExpApprox.expApprox (∓Y) q N` in terms of the residue-class
sums. `tbl_piN_lt`: `piN p < 4 · 2^(5p)`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds.MathlibTM2.Fast.TableNum


/-! ### The magnitude loop -/

/-- Input `Y`. -/
abbrev tblMagY : Fin 18 := 0
/-- Input `2 ^ q`. -/
abbrev tblMagPq : Fin 18 := 1
/-- Input `2 ^ Q`. -/
abbrev tblMagPQ : Fin 18 := 2
/-- Input `N`. -/
abbrev tblMagN : Fin 18 := 3
/-- Output `S_r`, `r < 4`, in variable `4 + r`. -/
def tblMagS (r : Fin 4) : Fin 18 := ⟨4 + r.val, by omega⟩

local notation "vS0" => (4 : Fin 18)
local notation "vS1" => (5 : Fin 18)
local notation "vS2" => (6 : Fin 18)
local notation "vS3" => (7 : Fin 18)
local notation "vM" => (8 : Fin 18)
local notation "vJ" => (9 : Fin 18)
local notation "vA" => (10 : Fin 18)
local notation "vT" => (11 : Fin 18)
local notation "vNum" => (12 : Fin 18)
local notation "vDen" => (13 : Fin 18)
local notation "vC1" => (14 : Fin 18)
local notation "vC2" => (15 : Fin 18)
local notation "vC3" => (16 : Fin 18)
local notation "vC4" => (17 : Fin 18)

/-- Add `M` to the sum `s` when `m mod 4` (in `vA`) is the class with offset `k = 4 − r`. -/
def tblMagAcc (k s : Fin 18) : List (TblIns 18) :=
  [.add vA k vT, .mod vT vC4 vT, .add vT vC3 vT, .div vT vC4 vT, .sub vC1 vT vT, .mul vT vM vT,
    .add s vT s]

/-- The loop body: the four class sums, then `M := ⌊M Y / (2^Q (j+1))⌋`. -/
def tblMagBody : List (TblIns 18) :=
  [.mod vJ vC4 vA] ++ tblMagAcc vC4 vS0 ++ tblMagAcc vC3 vS1 ++ tblMagAcc vC2 vS2 ++
    tblMagAcc vC1 vS3 ++ [.mul vM tblMagY vNum, .copy vJ vT, .inc vT, .mul tblMagPQ vT vDen]

/-- The magnitude loop program. -/
def tblMagCode : TblCode 18 :=
  tblBlock 18 (tblConstL vC1 1 ++ tblConstL vC2 2 ++ tblConstL vC3 3 ++ tblConstL vC4 4 ++
      [.zero vS0, .zero vS1, .zero vS2]) (.zero vS3) ;;
    tblBlock 18 [] (.copy tblMagPq vM) ;;
    tblFor vJ tblMagN (tblBlock 18 tblMagBody (.div vNum vDen vM))

/-! ### Arithmetic of the indicators -/

theorem tbl_ind (a r : ℕ) (ha : a < 4) (hr : r < 4) :
    1 - ((a + (4 - r)) % 4 + 3) / 4 = if a = r then 1 else 0 := by
  interval_cases a <;> interval_cases r <;> simp

theorem tbl_sum_succ (Y q Q r j : ℕ) (hr : r < 4) :
    tblSum Y q Q r (j + 1) = tblSum Y q Q r j + (1 - ((j % 4 + (4 - r)) % 4 + 3) / 4) * tblMag Y q Q j := by
  rw [tbl_ind _ _ (Nat.mod_lt _ (by norm_num)) hr]
  simp only [tblSum]
  split_ifs <;> simp

theorem tblMag_do {A W w : ℕ} (st : TblSt 18 A) {Y q Q N : ℕ} (hY : st.val tblMagY = Y)
    (hpq : st.val tblMagPq = 2 ^ q) (hpQ : st.val tblMagPQ = 2 ^ Q) (hN : st.val tblMagN = N)
    (hW : 3 ≤ W) (hNW : N < 2 ^ W) (hMl : ∀ m < N, tblMag Y q Q m < 2 ^ W)
    (hM : ∀ m < N, tblMag Y q Q m * Y < 2 ^ W) (hD : 2 ^ Q * N < 2 ^ W)
    (hS : ∀ r < 4, ∀ m ≤ N, tblSum Y q Q r m < 2 ^ W) :
    TblDo A W w tblMagCode st (fun s => (∀ r : Fin 4, s.val (tblMagS r) = tblSum Y q Q r N) ∧
      s.val tblMagY = Y ∧ s.val tblMagPq = 2 ^ q ∧ s.val tblMagPQ = 2 ^ Q ∧ s.val tblMagN = N ∧
      s.acc = st.acc) (39 * N + 30) := by
  have h8 : 8 ≤ 2 ^ W := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW
  have hY0 : st.val 0 = Y := hY
  have hpq0 : st.val 1 = 2 ^ q := hpq
  have hpQ0 : st.val 2 = 2 ^ Q := hpQ
  have hN0 : st.val 3 = N := hN
  -- constants and zero sums
  set l₁ : List (TblIns 18) := tblConstL vC1 1 ++ tblConstL vC2 2 ++ tblConstL vC3 3 ++
    tblConstL vC4 4 ++ [.zero vS0, .zero vS1, .zero vS2] with hl₁
  have hf₁ : tblFitsList A W w (l₁ ++ [.zero vS3]) st := by
    rw [hl₁]
    simp only [List.append_assoc]
    refine tblFitsList_append _ _ _ (tblFitsList_const _ _ _ (by omega)) ?_
    rw [tblExactList_const]
    refine tblFitsList_append _ _ _ (tblFitsList_const _ _ _ (by omega)) ?_
    rw [tblExactList_const]
    refine tblFitsList_append _ _ _ (tblFitsList_const _ _ _ (by omega)) ?_
    rw [tblExactList_const]
    refine tblFitsList_append _ _ _ (tblFitsList_const _ _ _ (by omega)) ?_
    simp [tblFitsList, TblIns.fits]
  set s₁ := tblExactList A w (l₁ ++ [.zero vS3]) st with hs₁
  have hv₁ : s₁.val vC1 = 1 ∧ s₁.val vC2 = 2 ∧ s₁.val vC3 = 3 ∧ s₁.val vC4 = 4 ∧ s₁.val vS0 = 0 ∧
      s₁.val vS1 = 0 ∧ s₁.val vS2 = 0 ∧ s₁.val vS3 = 0 ∧ s₁.val 0 = Y ∧ s₁.val 1 = 2 ^ q ∧
      s₁.val 2 = 2 ^ Q ∧ s₁.val 3 = N ∧ s₁.acc = st.acc := by
    rw [hs₁, hl₁]
    simp only [List.append_assoc]
    rw [tblExactList_append, tblExactList_const, tblExactList_append, tblExactList_const,
      tblExactList_append, tblExactList_const, tblExactList_append, tblExactList_const]
    simp [tblExactList, TblIns.exact, hY0, hpq0, hpQ0, hN0]
  obtain ⟨hc1, hc2, hc3, hc4, hs0, hs1, hs2, hs3, hy1, hpq1, hpQ1, hn1, hacc1⟩ := hv₁
  let Inv : ℕ → TblSt 18 A → Prop := fun j s => s.val vS0 = tblSum Y q Q 0 j ∧
    s.val vS1 = tblSum Y q Q 1 j ∧ s.val vS2 = tblSum Y q Q 2 j ∧ s.val vS3 = tblSum Y q Q 3 j ∧
    s.val vM = tblMag Y q Q j ∧ s.val vC1 = 1 ∧ s.val vC2 = 2 ∧ s.val vC3 = 3 ∧ s.val vC4 = 4 ∧
    s.val 0 = Y ∧ s.val 1 = 2 ^ q ∧ s.val 2 = 2 ^ Q ∧ s.acc = st.acc
  have hloop : TblDo A W w (tblFor vJ tblMagN (tblBlock 18 tblMagBody (.div vNum vDen vM)))
      (TblIns.exact A w (.copy tblMagPq vM) s₁) (fun s => (∀ r : Fin 4, s.val (tblMagS r) =
        tblSum Y q Q r N) ∧ s.val tblMagY = Y ∧ s.val tblMagPq = 2 ^ q ∧ s.val tblMagPQ = 2 ^ Q ∧
        s.val tblMagN = N ∧ s.acc = st.acc) (1 + (N * (35 + 1 + 1 + 2) + 2)) := by
    refine TblDo.for N (35 + 1) (by simp [TblIns.exact, tblMagN, hn1]) hNW (by decide) Inv ?_ ?_ ?_
    · simp [Inv, TblIns.exact, hs0, hs1, hs2, hs3, hc1, hc2, hc3, hc4, hy1, hpq1, hpQ1, hacc1,
        tblSum, tblMag]
    · intro j hj s ⟨h0, h1, h2, h3, hm, hk1, hk2, hk3, hk4, hy, hpq', hpQ', hacc⟩ hj' hn'
      have hml := hMl j hj
      have hmy := hM j hj
      have hd : 2 ^ Q * (j + 1) < 2 ^ W :=
        lt_of_le_of_lt (Nat.mul_le_mul_left _ (by omega)) hD
      have hs0' := hS 0 (by norm_num) (j + 1) (by omega)
      have hs1' := hS 1 (by norm_num) (j + 1) (by omega)
      have hs2' := hS 2 (by norm_num) (j + 1) (by omega)
      have hs3' := hS 3 (by norm_num) (j + 1) (by omega)
      have e0 : tblSum Y q Q 0 j + (1 - (j % 4 + 3) / 4) * tblMag Y q Q j = tblSum Y q Q 0 (j + 1) := by
        simp only [tblSum]
        split_ifs with h
        · rw [show 1 - (j % 4 + 3) / 4 = 1 by omega]; simp
        · rw [show 1 - (j % 4 + 3) / 4 = 0 by omega]; simp
      have e1 : tblSum Y q Q 1 j + (1 - ((j + 3) % 4 + 3) / 4) * tblMag Y q Q j =
          tblSum Y q Q 1 (j + 1) := by
        simp only [tblSum]
        split_ifs with h
        · rw [show 1 - ((j + 3) % 4 + 3) / 4 = 1 by omega]; simp
        · rw [show 1 - ((j + 3) % 4 + 3) / 4 = 0 by omega]; simp
      have e2 : tblSum Y q Q 2 j + (1 - ((j + 2) % 4 + 3) / 4) * tblMag Y q Q j =
          tblSum Y q Q 2 (j + 1) := by
        simp only [tblSum]
        split_ifs with h
        · rw [show 1 - ((j + 2) % 4 + 3) / 4 = 1 by omega]; simp
        · rw [show 1 - ((j + 2) % 4 + 3) / 4 = 0 by omega]; simp
      have e3 : tblSum Y q Q 3 j + (1 - ((j + 1) % 4 + 3) / 4) * tblMag Y q Q j =
          tblSum Y q Q 3 (j + 1) := by
        simp only [tblSum]
        split_ifs with h
        · rw [show 1 - ((j + 1) % 4 + 3) / 4 = 1 by omega]; simp
        · rw [show 1 - ((j + 1) % 4 + 3) / 4 = 0 by omega]; simp
      refine (TblDo.block _ _ ?_ ?_).mono (fun _ h => h) (by simp [tblMagBody, tblMagAcc])
      · simp [tblMagBody, tblMagAcc, tblFitsList, TblIns.fits, TblIns.exact, 
          h0, h1, h2, h3, hm, hk1, hk2, hk3, hk4, hy, hpQ', hj', tblMagY, tblMagPQ, 
          ]
        rw [e0, e1, e2, e3]
        and_intros <;> omega
      · simp [Inv, tblMagBody, tblMagAcc, tblExactList, TblIns.exact, 
          h0, h1, h2, h3, hm, hk1, hk2, hk3, hk4, hy, hpq', hpQ', hj', hn', hacc, tblMagY, tblMagPQ,
          tblMagN]
        exact ⟨e0, e1, e2, e3, rfl⟩
    · intro s ⟨h0, h1, h2, h3, hm, hk1, hk2, hk3, hk4, hy, hpq', hpQ', hacc⟩ hj' hn'
      refine ⟨fun r => ?_, hy, hpq', hpQ', hn', hacc⟩
      fin_cases r
      · exact h0
      · exact h1
      · exact h2
      · exact h3
  refine ((TblDo.block l₁ (.zero vS3) hf₁ (P := fun s => s = s₁) rfl).seq
    (K₂ := 1 + (1 + (N * (35 + 1 + 1 + 2) + 2))) (fun s hs => ?_)).mono (fun _ h => h) ?_
  · subst hs
    exact (TblDo.block (P := fun s => s = TblIns.exact A w (.copy tblMagPq vM) s₁) []
      (.copy tblMagPq vM) ⟨trivial, trivial⟩ rfl).seq (fun s hs => hs ▸ hloop)
  · simp [hl₁]
    omega

section WeightRoutine

open IntegerMultBounds.Resampling IntegerMultBounds.Resampling.WeightNat

/-! ### Sums of the weight routine -/

theorem tbl_evenSum_eq (Y q N : ℕ) :
    evenSum Y q N = tblSum Y q q 0 N + tblSum Y q q 2 N := by
  induction N with
  | zero => rfl
  | succ n ih =>
    simp only [evenSum, tblSum, ih, tbl_wmag_eq]
    have h := Nat.mod_lt n (show 0 < 4 by norm_num)
    have h2 : n % 2 = n % 4 % 2 := (Nat.mod_mod_of_dvd n (by norm_num)).symm
    interval_cases hn : n % 4 <;> simp_all <;> omega

theorem tbl_oddSum_eq (Y q N : ℕ) :
    oddSum Y q N = tblSum Y q q 1 N + tblSum Y q q 3 N := by
  induction N with
  | zero => rfl
  | succ n ih =>
    simp only [oddSum, tblSum, ih, tbl_wmag_eq]
    have h := Nat.mod_lt n (show 0 < 4 by norm_num)
    have h2 : n % 2 = n % 4 % 2 := (Nat.mod_mod_of_dvd n (by norm_num)).symm
    interval_cases hn : n % 4 <;> simp_all <;> omega

theorem tbl_allSum_eq (Y q N : ℕ) : allSum Y q N = evenSum Y q N + oddSum Y q N := by
  induction N with
  | zero => rfl
  | succ n ih =>
    simp only [allSum, evenSum, oddSum, ih]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> omega

/-- `piN p < 4 · 2^(5p)`. -/
theorem tbl_piN_lt (p : ℕ) (hp : 2 ≤ p) : piN p < 4 * 2 ^ (5 * p) := by
  have h := WeightTable.piQ_err p (by omega)
  have hpi := Real.pi_lt_d2
  have hl := WeightTable.lin100 p hp
  have h45 : 2 * 2 ^ (4 * p) ≤ 2 ^ (5 * p) := by
    rw [show 5 * p = 4 * p + p by ring, pow_add, mul_comm 2]
    exact Nat.mul_le_mul_left _ (by calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega))
  have he : ((piN p : ℤ) : ℝ) = (WeightTable.piQ p : ℝ) := by rw [tblPi_eq_piQ p hp]
  have hl' : (100 * (p : ℝ) + 1) ≤ 2 ^ (4 * p) := by exact_mod_cast hl
  have h45' : 2 * (2 : ℝ) ^ (4 * p) ≤ 2 ^ (5 * p) := by exact_mod_cast h45
  have hX : (0 : ℝ) < 2 ^ (5 * p) := by positivity
  have hup : (WeightTable.piQ p : ℝ) ≤ 2 ^ (5 * p) * Real.pi + (20 * (5 * p) + 1) :=
    by linarith [(abs_le.mp h).2]
  have : ((piN p : ℕ) : ℝ) < 4 * 2 ^ (5 * p) := by
    push_cast at he
    rw [he]
    nlinarith
  exact_mod_cast this

/-! ### The weight routine -/

local notation "eY" => (0 : Fin 34)
local notation "ePq" => (1 : Fin 34)
local notation "ePQ" => (2 : Fin 34)
local notation "eN" => (3 : Fin 34)
local notation "eS0" => (4 : Fin 34)
local notation "eS1" => (5 : Fin 34)
local notation "eS2" => (6 : Fin 34)
local notation "eS3" => (7 : Fin 34)
local notation "ePiN" => (18 : Fin 34)
local notation "eP" => (19 : Fin 34)
local notation "eA" => (20 : Fin 34)
local notation "eB" => (21 : Fin 34)
local notation "eNeg" => (22 : Fin 34)
local notation "eRes" => (23 : Fin 34)
local notation "eQ" => (24 : Fin 34)
local notation "eT" => (25 : Fin 34)
local notation "eI" => (27 : Fin 34)
local notation "eD" => (28 : Fin 34)
local notation "eThr" => (29 : Fin 34)
local notation "eOne" => (30 : Fin 34)
local notation "eE4" => (31 : Fin 34)
local notation "eEv" => (32 : Fin 34)
local notation "eOd" => (33 : Fin 34)

/-- The magnitude loop inside the weight routine: its variables are the first 18. -/
def tblExpMagMap : Fin 18 → Fin 34 := Fin.castLE (by norm_num)

/-- The weight routine `expPiNat neg p a b`, from `piN p`, `p`, `a`, `b` and `neg ∈ {0, 1}` in
variables `18 … 22`, into variable `23`. -/
def tblExpCode : TblCode 34 :=
  tblBlock 34 [.mul ePiN eA eT, .div eT eB eY, .add eP eP eQ, .add eQ eP eQ, .add eQ eP eQ,
      .add eQ eP eQ, .add eQ eP eN, .add eN eP eN, .add eP eP eE4, .add eE4 eP eE4,
      .add eE4 eP eE4, .zero eOne, .inc eOne] (.zero eRes) ;;
    tblPow2 ePq eQ eI ;;
    tblBlock 34 [.copy ePq ePQ] (.mul eP ePq eThr) ;;
    tblPow2 eD eE4 eI ;;
    .ite eY eThr
      (tblMagCode.rename tblExpMagMap ;;
        tblBlock 34 [.add eS0 eS2 eEv, .add eS1 eS3 eOd] (.add eEv eOd eT) ;;
        .ite eNeg eOne (.ins (.div eT eD eRes)) (tblBlock 34 [.sub eEv eOd eT] (.div eT eD eRes)))
      (.ins (.zero eRes))

theorem tbl_sum_le_of (Y q Q r B : ℕ) (hB : ∀ i, tblMag Y q Q i ≤ B) (m : ℕ) :
    tblSum Y q Q r m ≤ m * B := by
  induction m with
  | zero => simp [tblSum]
  | succ m ih =>
    simp only [tblSum]
    have := hB m
    split_ifs <;> nlinarith

theorem tblExp_do {A W w : ℕ} (st : TblSt 34 A) {p a b : ℕ} (neg : Bool)
    (hpiN : st.val 18 = piN p) (hp' : st.val 19 = p) (ha : st.val 20 = a) (hb : st.val 21 = b)
    (hneg : st.val 22 = if neg then 1 else 0) (hp : 13 ≤ p) (hW : 13 * p + 8 ≤ W)
    (haW : a * 2 ^ (5 * p + 2) < 2 ^ W)
    (hpos : neg = false → piN p * a / b < p * 2 ^ (5 * p)) :
    TblDo A W w tblExpCode st (fun s => s.val 23 = expPiNat neg p a b ∧
      s.val 18 = st.val 18 ∧ s.val 19 = st.val 19 ∧ s.val 20 = st.val 20 ∧ s.val 21 = st.val 21 ∧
      s.val 22 = st.val 22 ∧ s.acc = st.acc) (310 * p + 100) := by
  obtain ⟨q, hq⟩ : ∃ q, q = 5 * p := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = piN p * a / b := ⟨_, rfl⟩
  have hpi := tbl_piN_lt p (by omega)
  rw [← hq] at hpi haW
  have hp2 : p < 2 ^ p := Nat.lt_two_pow_self
  have hWq : 2 ^ (13 * p + 8) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW
  have hsplit : 2 ^ (13 * p + 8) = 2 ^ q * 2 ^ q * 2 ^ p * 2 ^ p * 2 ^ p * 256 := by
    rw [hq, show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_add, ← pow_add, ← pow_add, ← pow_add,
      ← pow_add]
    ring_nf
  have hq1 : 1 ≤ 2 ^ q := Nat.one_le_two_pow
  have hp1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  have hpa : piN p * a < 2 ^ W := by
    calc piN p * a ≤ 4 * 2 ^ q * a := Nat.mul_le_mul_right _ hpi.le
      _ = a * 2 ^ (q + 2) := by rw [pow_add]; ring
      _ < 2 ^ W := haW
  have hp3 : 2 ^ (p + 3) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h7p : 7 * p < 2 ^ W := by
    have : 7 * p < 2 ^ (p + 3) := by rw [pow_add]; omega
    omega
  -- the first block
  set l₁ : List (TblIns 34) := [.mul ePiN eA eT, .div eT eB eY, .add eP eP eQ, .add eQ eP eQ,
    .add eQ eP eQ, .add eQ eP eQ, .add eQ eP eN, .add eN eP eN, .add eP eP eE4, .add eE4 eP eE4,
    .add eE4 eP eE4, .zero eOne, .inc eOne] with hl₁
  have hf₁ : tblFitsList A W w (l₁ ++ [.zero eRes]) st := by
    simp [hl₁, tblFitsList, TblIns.fits, TblIns.exact, hpiN, ha, hp']
    omega
  set s₁ := tblExactList A w (l₁ ++ [.zero eRes]) st with hs₁
  have hv₁ : s₁.val eY = Y ∧ s₁.val eQ = q ∧ s₁.val eN = 7 * p ∧ s₁.val eE4 = 4 * p ∧
      s₁.val eOne = 1 ∧ s₁.val 18 = st.val 18 ∧ s₁.val 19 = st.val 19 ∧ s₁.val 20 = st.val 20 ∧
      s₁.val 21 = st.val 21 ∧ s₁.val 22 = st.val 22 ∧ s₁.acc = st.acc := by
    simp [hs₁, hl₁, tblExactList, TblIns.exact, hpiN, ha, hp', hb, hY]
    omega
  obtain ⟨hY₁, hQ₁, hN₁, hE₁, hO₁, h18₁, h19₁, h20₁, h21₁, h22₁, hacc₁⟩ := hv₁
  have hqW : q < W := by omega
  have h4W : 4 * p < W := by omega
  -- the state before the branch
  let R : TblSt 34 A → Prop := fun s => s.val eY = Y ∧ s.val ePq = 2 ^ q ∧ s.val ePQ = 2 ^ q ∧
    s.val eN = 7 * p ∧ s.val eD = 2 ^ (4 * p) ∧ s.val eThr = p * 2 ^ q ∧ s.val eOne = 1 ∧
    s.val 18 = st.val 18 ∧ s.val 19 = st.val 19 ∧ s.val 20 = st.val 20 ∧ s.val 21 = st.val 21 ∧
    s.val 22 = st.val 22 ∧ s.acc = st.acc
  have hpq : p * 2 ^ q < 2 ^ W := by
    calc p * 2 ^ q < 2 ^ p * 2 ^ q := Nat.mul_lt_mul_of_pos_right hp2 (by positivity)
      _ ≤ 2 ^ W := by rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  -- the value of the routine
  have hval : expPiNat neg p a b = if neg then (if p * 2 ^ q ≤ Y then 0 else
      (evenSum Y q (7 * p) - oddSum Y q (7 * p)) / 2 ^ (4 * p)) else allSum Y q (7 * p) / 2 ^ (4 * p) := by
    simp only [expPiNat, hY, hq]
  have hfx : ∀ x : Fin 34, 18 ≤ x.val → ∀ y : Fin 18, tblExpMagMap y ≠ x := fun x hx y h => by
    have := congrArg Fin.val h; simp [tblExpMagMap] at this; omega
  have hbranch : ∀ s, R s → TblDo A W w (.ite eY eThr
      (tblMagCode.rename tblExpMagMap ;;
        tblBlock 34 [.add eS0 eS2 eEv, .add eS1 eS3 eOd] (.add eEv eOd eT) ;;
        .ite eNeg eOne (.ins (.div eT eD eRes)) (tblBlock 34 [.sub eEv eOd eT] (.div eT eD eRes)))
      (.ins (.zero eRes))) s (fun s => s.val 23 = expPiNat neg p a b ∧
        s.val 18 = st.val 18 ∧ s.val 19 = st.val 19 ∧ s.val 20 = st.val 20 ∧
        s.val 21 = st.val 21 ∧ s.val 22 = st.val 22 ∧ s.acc = st.acc) (273 * p + 40) := by
    intro s ⟨hYs, hPqs, hPQs, hNs, hDs, hThrs, hOnes, h18s, h19s, h20s, h21s, h22s, haccs⟩
    by_cases hlt : Y < p * 2 ^ q
    · have hYle : Y ≤ p * 2 ^ q := hlt.le
      have hB : ∀ i, tblMag Y q q i < 2 ^ (q + 2 * p) := fun i => by
        rw [← tbl_wmag_eq]; exact tbl_wmag_lt p Y q i (by omega) hYle
      have hqp : 2 ^ (q + 2 * p) * 2 ^ (p + 3) ≤ 2 ^ W := by
        rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hBW : 2 ^ (q + 2 * p) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h7 : 7 * p < 2 ^ (p + 3) := by rw [pow_add]; omega
      have hsum : ∀ r m, m ≤ 7 * p → tblSum Y q q r m < 2 ^ W := fun r m hm => by
        have h1 := tbl_sum_le_of Y q q r _ (fun i => (hB i).le) m
        have h2 : m * 2 ^ (q + 2 * p) < 2 ^ (p + 3) * 2 ^ (q + 2 * p) :=
          Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
        rw [mul_comm] at hqp
        omega
      have hYp : Y < 2 ^ (p + q) := by
        rw [pow_add]; exact lt_of_lt_of_le hlt (Nat.mul_le_mul_right _ hp2.le)
      have hMY : ∀ m < 7 * p, tblMag Y q q m * Y < 2 ^ W := fun m _ =>
        calc tblMag Y q q m * Y < 2 ^ (q + 2 * p) * 2 ^ (p + q) := Nat.mul_lt_mul'' (hB m) hYp
          _ ≤ 2 ^ W := by rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hDW : 2 ^ q * (7 * p) < 2 ^ W :=
        calc 2 ^ q * (7 * p) < 2 ^ q * 2 ^ (p + 3) := Nat.mul_lt_mul_of_pos_left h7 (by positivity)
          _ ≤ 2 ^ W := by rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hmag := (tblMag_do (A := A) (W := W) (w := w) (s.restrict tblExpMagMap) (Y := Y) (q := q)
        (Q := q) (N := 7 * p) hYs hPqs hPQs hNs (by omega) h7p (fun m _ => lt_of_lt_of_le (hB m) hBW)
        hMY hDW (fun r _ m hm => hsum r m hm)).rename (Fin.castLE_injective _)
      refine (TblDo.iteT (by rw [hYs, hThrs]; exact hlt) (hmag.seq (K₂ := 3 + 3)
        (fun s' ⟨⟨hS, _, _, _, _, hacc'⟩, hfr'⟩ => ?_))).mono (fun _ h => h) (by omega)
      have hS0 : s'.val eS0 = tblSum Y q q 0 (7 * p) := hS 0
      have hS1 : s'.val eS1 = tblSum Y q q 1 (7 * p) := hS 1
      have hS2 : s'.val eS2 = tblSum Y q q 2 (7 * p) := hS 2
      have hS3 : s'.val eS3 = tblSum Y q q 3 (7 * p) := hS 3
      have hev := tbl_evenSum_eq Y q (7 * p)
      have hod := tbl_oddSum_eq Y q (7 * p)
      have hall := tbl_allSum_eq Y q (7 * p)
      have hevl := tbl_evenSum_le p Y q (7 * p) (by omega) hYle
      have hodl := tbl_oddSum_le p Y q (7 * p) (by omega) hYle
      have hall' := tbl_allSum_le p Y q (7 * p) (by omega) hYle
      have hAW : 7 * p * 2 ^ (q + 2 * p) < 2 ^ W := by
        have : 7 * p * 2 ^ (q + 2 * p) < 2 ^ (p + 3) * 2 ^ (q + 2 * p) :=
          Nat.mul_lt_mul_of_pos_right h7 (by positivity)
        rw [mul_comm (2 ^ (p + 3))] at this
        omega
      have hk : ∀ x : Fin 34, 18 ≤ x.val → s'.val x = s.val x := fun x hx => hfr' x (hfx x hx)
      refine (TblDo.block _ _ ?_ rfl).seq (fun s'' hs'' => ?_)
      · simp [tblFitsList, TblIns.fits, TblIns.exact, hS0, hS1, hS2, hS3]
        omega
      subst hs''
      have hT : (tblExactList A w ([.add eS0 eS2 eEv, .add eS1 eS3 eOd] ++ [.add eEv eOd eT]) s').val
          eT = allSum Y q (7 * p) := by
        simp [tblExactList, TblIns.exact, hS0, hS1, hS2, hS3]; omega
      set s₂ := tblExactList A w ([.add eS0 eS2 eEv, .add eS1 eS3 eOd] ++ [.add eEv eOd eT]) s'
        with hs₂
      have hk2 : ∀ x : Fin 34, x ≠ eEv → x ≠ eOd → x ≠ eT → s₂.val x = s'.val x := by
        intro x h1 h2 h3
        simp [hs₂, tblExactList, TblIns.exact, Function.update_of_ne h1, Function.update_of_ne h2,
          Function.update_of_ne h3]
      have hEv2 : s₂.val eEv = evenSum Y q (7 * p) := by simp [hs₂, tblExactList, TblIns.exact, hS0, hS2, hev]
      have hOd2 : s₂.val eOd = oddSum Y q (7 * p) := by simp [hs₂, tblExactList, TblIns.exact, hS1, hS3, hod]
      have hin : s₂.val 18 = st.val 18 ∧ s₂.val 19 = st.val 19 ∧ s₂.val 20 = st.val 20 ∧
          s₂.val 21 = st.val 21 ∧ s₂.val 22 = st.val 22 := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
          (rwa [hk2 _ (by decide) (by decide) (by decide), hk _ (by decide)])
      have hNeg2 : s₂.val eNeg = if neg then 1 else 0 := by
        rw [hin.2.2.2.2, hneg]
      have hOne2 : s₂.val eOne = 1 := by
        rw [hk2 _ (by decide) (by decide) (by decide), hk _ (by decide), hOnes]
      have hD2 : s₂.val eD = 2 ^ (4 * p) := by
        rw [hk2 _ (by decide) (by decide) (by decide), hk _ (by decide), hDs]
      have hacc2 : s₂.acc = st.acc := by
        have : s'.acc = s.acc := hacc'
        simp [hs₂, tblExactList, TblIns.exact, this, haccs]
      have hfin : ∀ v : ℕ, v = expPiNat neg p a b →
          (fun s : TblSt 34 A => s.val 23 = expPiNat neg p a b ∧ s.val 18 = st.val 18 ∧
            s.val 19 = st.val 19 ∧ s.val 20 = st.val 20 ∧ s.val 21 = st.val 21 ∧
            s.val 22 = st.val 22 ∧ s.acc = st.acc) ⟨Function.update s₂.val eRes v, s₂.acc⟩ := by
        intro v hv
        obtain ⟨i1, i2, i3, i4, i5⟩ := hin
        refine ⟨by simp [hv], ?_, ?_, ?_, ?_, ?_, hacc2⟩ <;>
          (dsimp only; rwa [Function.update_of_ne (by decide)])
      cases neg with
      | false =>
        refine (TblDo.iteT (by rw [hNeg2, hOne2]; decide) (TblDo.insX _ (by trivial) ?_)).mono
          (fun _ h => h) (by norm_num)
        refine hfin _ ?_
        simp [hT, hD2, hval]
      | true =>
        have hle := odd_le_even p Y hp (by rw [← hq]; exact hlt)
        rw [← hq] at hle
        refine (TblDo.iteF (by rw [hNeg2, hOne2]; decide) (TblDo.block _ _ ?_ ?_)).mono
          (fun _ h => h) (by norm_num)
        · simp [tblFitsList, TblIns.fits, hEv2, hOd2]
          exact ⟨hle, by omega⟩
        · refine hfin _ ?_
          simp [TblIns.exact, hEv2, hOd2, hD2, hval, hlt.not_ge]
    · refine (TblDo.iteF (by rw [hYs, hThrs]; exact hlt) (TblDo.insX _ (by trivial) ?_)).mono
        (fun _ h => h) (by omega)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by simp [TblIns.exact, haccs]⟩
      · cases neg with
        | false => exact absurd (by rw [hY, hq]; exact hpos rfl) hlt
        | true => simp [TblIns.exact, hval, not_lt.mp hlt]
      all_goals (simp only [TblIns.exact]; rwa [Function.update_of_ne (by decide)])
  have hpre : TblDo A W w (tblPow2 ePq eQ eI ;; tblBlock 34 [.copy ePq ePQ] (.mul eP ePq eThr) ;;
      tblPow2 eD eE4 eI ;; .ite eY eThr
        (tblMagCode.rename tblExpMagMap ;;
          tblBlock 34 [.add eS0 eS2 eEv, .add eS1 eS3 eOd] (.add eEv eOd eT) ;;
          .ite eNeg eOne (.ins (.div eT eD eRes)) (tblBlock 34 [.sub eEv eOd eT] (.div eT eD eRes)))
        (.ins (.zero eRes))) s₁ (fun s => s.val 23 = expPiNat neg p a b ∧
          s.val 18 = st.val 18 ∧ s.val 19 = st.val 19 ∧ s.val 20 = st.val 20 ∧
          s.val 21 = st.val 21 ∧ s.val 22 = st.val 22 ∧ s.acc = st.acc)
      (4 * q + 5 + (2 + (4 * (4 * p) + 5 + (273 * p + 40)))) := by
    have hpow₁ := tblPow2_do (A := A) (W := W) (w := w) (c := ePq) (e := eQ) (i := eI) (by decide)
      (by decide) (by decide) s₁ (by rw [hQ₁]; exact hqW)
    rw [hQ₁] at hpow₁
    refine hpow₁.seq (fun s₂ ⟨hpq₂, _, hfr₂, hacc₂⟩ => ?_)
    have hP₂ : s₂.val eP = p := by rw [hfr₂ _ (by decide) (by decide), h19₁, hp']
    refine (TblDo.block (P := fun s => s = tblExactList A w ([.copy ePq ePQ] ++ [.mul eP ePq eThr]) s₂)
      _ _ ?_ rfl).seq (fun s₃ hs₃ => ?_)
    · simp [tblFitsList, TblIns.fits, TblIns.exact, hP₂, hpq₂]; exact hpq
    subst hs₃
    have hpow₂ := tblPow2_do (A := A) (W := W) (w := w) (c := eD) (e := eE4) (i := eI) (by decide)
      (by decide) (by decide) (tblExactList A w ([.copy ePq ePQ] ++ [.mul eP ePq eThr]) s₂) (by
        simp [tblExactList, TblIns.exact, hfr₂ eE4 (by decide) (by decide), hE₁]; exact h4W)
    have he4 : (tblExactList A w ([.copy ePq ePQ] ++ [.mul eP ePq eThr]) s₂).val eE4 = 4 * p := by
      simp [tblExactList, TblIns.exact, hfr₂ eE4 (by decide) (by decide), hE₁]
    rw [he4] at hpow₂
    refine hpow₂.seq (fun s ⟨hd, _, hfr, hacc⟩ => hbranch s ?_)
    have k : ∀ x : Fin 34, x ≠ eD → x ≠ eI → x ≠ ePQ → x ≠ eThr → x ≠ ePq → s.val x = s₁.val x := by
      intro x h1 h2 h3 h4 h5
      rw [hfr x h1 h2]
      simp only [tblExactList, TblIns.exact, List.singleton_append]
      rw [Function.update_of_ne h4, Function.update_of_ne h3]
      exact hfr₂ x h5 h2
    have k3 : s.val ePQ = 2 ^ q ∧ s.val eThr = p * 2 ^ q ∧ s.val ePq = 2 ^ q := by
      rw [hfr _ (by decide) (by decide), hfr _ (by decide) (by decide), hfr _ (by decide) (by decide)]
      simp [tblExactList, TblIns.exact, hpq₂, hP₂]
    simp only [tblExactList, TblIns.exact, List.singleton_append] at hacc
    exact ⟨by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide), hY₁], k3.2.2, k3.1,
      by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide), hN₁], hd, k3.2.1,
      by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide), hO₁],
      by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide), h18₁],
      by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide), h19₁],
      by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide), h20₁],
      by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide), h21₁],
      by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide), h22₁],
      by rw [hacc, hacc₂, hacc₁]⟩
  refine ((TblDo.block l₁ (.zero eRes) hf₁ (P := fun s => s = s₁) rfl).seq
    (fun s hs => hs ▸ hpre)).mono (fun _ h => h) ?_
  simp [hl₁]
  omega

/-- The weight routine computes `WeightTable.expPi` for `13 ≤ p`. -/
theorem tblExp_do_expPi {A W w : ℕ} (st : TblSt 34 A) {p a b : ℕ} (neg : Bool)
    (hpiN : st.val 18 = piN p) (hp' : st.val 19 = p) (ha : st.val 20 = a) (hb : st.val 21 = b)
    (hneg : st.val 22 = if neg then 1 else 0) (hp : 13 ≤ p) (hW : 13 * p + 8 ≤ W)
    (haW : a * 2 ^ (5 * p + 2) < 2 ^ W)
    (hpos : neg = false → piN p * a / b < p * 2 ^ (5 * p)) :
    TblDo A W w tblExpCode st (fun s => (s.val 23 : ℤ) = WeightTable.expPi neg p a b ∧
      s.acc = st.acc) (310 * p + 100) :=
  (tblExp_do st neg hpiN hp' ha hb hneg hp hW haW hpos).mono
    (fun s h => ⟨by rw [h.1, expPi_eq_nat neg p a b hp], h.2.2.2.2.2.2⟩) le_rfl

/-- The Taylor sum of `exp (−Y / 2^q)` with `N` terms (`ExpApprox.expApprox`) from the four
residue-class sums of the magnitude loop. -/
theorem tbl_expApprox_neg (Y q N : ℕ) :
    ExpApprox.expApprox (-(Y : ℤ)) q N =
      ((tblSum Y q q 0 N + tblSum Y q q 2 N : ℕ) : ℤ) - (tblSum Y q q 1 N + tblSum Y q q 3 N : ℕ) := by
  rw [expApprox_neg, tbl_evenSum_eq, tbl_oddSum_eq]

/-- The Taylor sum of `exp (Y / 2^q)` with `N` terms from the four residue-class sums. -/
theorem tbl_expApprox_pos (Y q N : ℕ) :
    ExpApprox.expApprox (Y : ℤ) q N =
      ((tblSum Y q q 0 N + tblSum Y q q 1 N + tblSum Y q q 2 N + tblSum Y q q 3 N : ℕ) : ℤ) := by
  rw [expApprox_pos, tbl_allSum_eq, tbl_evenSum_eq, tbl_oddSum_eq]
  push_cast; ring

end WeightRoutine

end IntegerMultBounds.MathlibTM2.Fast.TableVM
