module

public import IntegerMultBounds.MathlibTM2.Fast.TablePhase

/-!
# Shared initialisation of the phase streams

The chirp axis streams and the twist streams run on 84 variables: Machin's `π` (`tblPiCode`) on
variables `0 … 17`, the Taylor machine (`tblTaylorCode`) on `18 … 53`, the stream variables on
`54 … 83`, with the inputs `p, g, N, s, w` in `54 … 58`.

`tblPhaseInit` computes, from the inputs (`tblPhaseInit_do`, `200 (p + g) + 4 w + 1500` atoms for
`1 ≤ N`, `2 N < 2^W`, `w < W`, `5 (p + g) + 40 ≤ W`), the values `tblPhaseEnv p g N s w`:

* `piN (p + g + 4)` (variable `15`), the angle precision `P = p + g + 4`;
* `2^q` with `q = tblPhq p g = p + g + 2 + gT`, `gT = tblPhG p g = ⌈log₂ (p + g + 14)⌉ + 4`
  (`taylorGuard p g`, `tblPhG_eq`; the ceiling logarithm by `tblClogCode`), `2^Q` with
  `Q = tblPhQ p g = 5 (p + g + 4)`, and `n = p + g + 14` Taylor terms, in the Taylor inputs
  `19, 20, 21`, and `1` in `37`;
* the inputs, `1`, `2N`, `N − 1`, the rounding constants `2^(gT+1)`, `2^(gT+2)`, the residue
  modulus `2^w`, and the `diskPhase` constants `2^(p+2) − 1`, `2^(q+2)`.

Values are tracked as lists of known values (`tblKV`); `tblKV_block` turns a block of exact
instructions into new known values while keeping the known values off the written variables.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds.MathlibTM2.Fast.TableNum


local notation "wP" => (0 : Fin 84)
local notation "wPq" => (19 : Fin 84)
local notation "wPQ" => (20 : Fin 84)
local notation "wn" => (21 : Fin 84)
local notation "wX" => (36 : Fin 84)
local notation "wC1" => (37 : Fin 84)
local notation "wp" => (54 : Fin 84)
local notation "wg" => (55 : Fin 84)
local notation "wN" => (56 : Fin 84)
local notation "ww" => (58 : Fin 84)
local notation "wOne" => (59 : Fin 84)
local notation "w2N" => (61 : Fin 84)
local notation "wH" => (62 : Fin 84)
local notation "wHH" => (63 : Fin 84)
local notation "wPw" => (64 : Fin 84)
local notation "wE" => (65 : Fin 84)
local notation "wI" => (66 : Fin 84)
local notation "wGT" => (67 : Fin 84)
local notation "wC" => (68 : Fin 84)
local notation "wPc" => (69 : Fin 84)
local notation "wNm1" => (70 : Fin 84)
local notation "wT1" => (74 : Fin 84)
local notation "wT2" => (75 : Fin 84)
local notation "wCC" => (80 : Fin 84)
local notation "wDen" => (81 : Fin 84)

theorem tblKV_block {n A W w : ℕ} {l : List (TblIns n)} {i : TblIns n} {st : TblSt n A}
    {L : List (Fin n × ℕ)} (M : List (Fin n)) (hL : tblKV st L) (hd : ∀ e ∈ L, e.1 ∉ M)
    (hf : tblFitsList A W w (l ++ [i]) st)
    (hfr : ∀ x, x ∉ M → (tblExactList A w (l ++ [i]) st).val x = st.val x)
    (hacc : (tblExactList A w (l ++ [i]) st).acc = st.acc) {New : List (Fin n × ℕ)}
    (hnew : tblKV (tblExactList A w (l ++ [i]) st) New) :
    TblDo A W w (tblBlock n l i) st (fun s' => tblKV s' (New ++ L) ∧ s'.acc = st.acc)
      (l.length + 1) := by
  refine TblDo.block _ _ hf ⟨fun e he => ?_, hacc⟩
  rcases List.mem_append.1 he with he | he
  · exact hnew e he
  · exact (hfr e.1 (hd e he)).trans (hL e he)

/-- The first block of the shared initialisation. -/
def tblPhB1 : List (TblIns 84) := tblConstL wT1 4 ++ tblConstL wT2 14 ++ tblConstL wOne 1 ++
  [.add wp wg wP, .add wP wT1 wP, .add wp wg wn, .add wn wT2 wn, .add wN wN w2N, .sub wN wOne wNm1,
    .copy wOne wC1]

theorem tblPhB1_do {A W w : ℕ} (st : TblSt 84 A) {p g N s : ℕ}
    (L0 : tblKV st [(wp, p), (wg, g), (wN, N), ((57 : Fin 84), s), (ww, w)])
    (hN : 1 ≤ N) (hN2 : 2 * N < 2 ^ W) (hW : p + g + 20 ≤ W) :
    TblDo A W w (tblBlock 84 tblPhB1 (.zero wX)) st (fun s' =>
      tblKV s' [(wP, p + g + 4), (wn, p + g + 14), (wOne, 1), (w2N, N + N), (wNm1, N - 1), (wC1, 1),
        (wp, p), (wg, g), (wN, N), ((57 : Fin 84), s), (ww, w)] ∧ s'.acc = st.acc) (29 + 1) := by
  have hp : st.val wp = p := L0.get (by simp)
  have hg : st.val wg = g := L0.get (by simp)
  have hNv : st.val wN = N := L0.get (by simp)
  have hs : st.val 57 = s := L0.get (by simp)
  have hw : st.val ww = w := L0.get (by simp)
  have hW2 : p + g + 20 < 2 ^ W := lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) hW)
  refine (TblDo.block _ _ ?_ ?_).mono (fun _ h => h) (by simp [tblPhB1])
  · simp only [tblPhB1, List.append_assoc]
    refine tblFitsList_append _ _ _ (tblFitsList_const _ _ _ (by omega)) ?_
    rw [tblExactList_const]
    refine tblFitsList_append _ _ _ (tblFitsList_const _ _ _ (by omega)) ?_
    rw [tblExactList_const]
    refine tblFitsList_append _ _ _ (tblFitsList_const _ _ _ (by omega)) ?_
    rw [tblExactList_const]
    simp [tblFitsList, TblIns.fits, TblIns.exact, hp, hg, hNv]
    omega
  · simp only [tblPhB1, List.append_assoc]
    rw [tblExactList_append, tblExactList_const, tblExactList_append, tblExactList_const,
      tblExactList_append, tblExactList_const]
    refine ⟨fun e he => ?_, by simp [tblExactList, TblIns.exact]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [tblExactList, TblIns.exact, hp, hg, hNv, hs, hw]

theorem tbl_sub_skip {α : Type} (c a : α) (L : List α) : ∀ e ∈ c :: L, e ∈ c :: a :: L :=
  fun _ he => (List.Sublist.cons_cons c (List.sublist_cons_self a L)).subset he

/-- The guard `gT = ⌈log₂ (p + g + 14)⌉ + 4` (`taylorGuard p g`). -/
def tblPhG (p g : ℕ) : ℕ := Nat.clog 2 (p + g + 14) + 4

/-- The Taylor precision `q = p + g + 2 + gT`. -/
def tblPhq (p g : ℕ) : ℕ := p + g + 2 + tblPhG p g

/-- The angle precision `Q = 5 (p + g + 4)`. -/
def tblPhQ (p g : ℕ) : ℕ := (p + g + 4) * 5

theorem tblPhG_eq (p g : ℕ) : tblPhG p g = IntegerMultBounds.MathlibTM2.Mult.Chirp.taylorGuard p g := rfl

theorem tblPhG_le (p g : ℕ) : tblPhG p g ≤ p + g + 18 := by
  have := Nat.clog_le_of_le_pow (b := 2) (x := p + g + 14) (y := p + g + 14) Nat.lt_two_pow_self.le
  unfold tblPhG; omega

/-- The second block: `gT := c + 4`, `e := p + g + 2 + gT`. -/
def tblPhB2 : List (TblIns 84) := tblConstL wT1 4 ++ tblConstL wT2 2 ++
  [.add wC wT1 wGT, .add wp wg wE, .add wE wT2 wE]

theorem tblPhB2_do {A W w : ℕ} (st : TblSt 84 A) {L : List (Fin 84 × ℕ)} (hL : tblKV st L)
    (hd : ∀ e ∈ L, e.1 ∉ [wT1, wT2, wGT, wE]) {p g : ℕ} (hp : (wp, p) ∈ L) (hg : (wg, g) ∈ L)
    (hc : (wC, Nat.clog 2 (p + g + 14)) ∈ L) (hW : 3 * (p + g) + 40 ≤ W) :
    TblDo A W w (tblBlock 84 tblPhB2 (.add wE wGT wE)) st (fun s' =>
      tblKV s' ([(wE, tblPhq p g), (wGT, tblPhG p g)] ++ L) ∧ s'.acc = st.acc) (11 + 1) := by
  have hpv : st.val wp = p := hL.get hp
  have hgv : st.val wg = g := hL.get hg
  have hcv : st.val wC = Nat.clog 2 (p + g + 14) := hL.get hc
  have hG := tblPhG_le p g
  have hW2 : 3 * (p + g) + 40 < 2 ^ W :=
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) hW)
  have e : ∀ st' : TblSt 84 A, tblExactList A w (tblPhB2 ++ [.add wE wGT wE]) st' =
      tblExactList A w [.add wC wT1 wGT, .add wp wg wE, .add wE wT2 wE, .add wE wGT wE]
        ⟨Function.update (Function.update st'.val wT1 4) wT2 2, st'.acc⟩ := by
    intro st'
    simp only [tblPhB2, List.append_assoc]
    rw [tblExactList_append, tblExactList_const, tblExactList_append, tblExactList_const]
    rfl
  refine (tblKV_block [wT1, wT2, wGT, wE] hL hd ?_ ?_ ?_ ?_).mono (fun _ h => h) (by simp [tblPhB2])
  · simp only [tblPhB2, List.append_assoc]
    refine tblFitsList_append _ _ _ (tblFitsList_const _ _ _ (by omega)) ?_
    rw [tblExactList_const]
    refine tblFitsList_append _ _ _ (tblFitsList_const _ _ _ (by omega)) ?_
    rw [tblExactList_const]
    simp [tblFitsList, TblIns.fits, TblIns.exact, hpv, hgv, hcv]
    unfold tblPhG at hG
    omega
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rw [e]
    simp [tblExactList, TblIns.exact, hx]
  · rw [e]; simp [tblExactList, TblIns.exact]
  · rw [e]
    intro e' he'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
    rcases he' with rfl | rfl <;> simp [tblExactList, TblIns.exact, hpv, hgv, hcv, tblPhq, tblPhG]

/-- The third block: `den := 2^q · 4`, `e := 5 (p + g + 4)`. -/
def tblPhB3 : List (TblIns 84) := tblConstL wT1 4 ++ tblConstL wT2 5 ++
  [.mul wPq wT1 wDen, .add wp wg wE, .add wE wT1 wE]

theorem tblPhB3_do {A W w : ℕ} (st : TblSt 84 A) {L : List (Fin 84 × ℕ)} (hL : tblKV st L)
    (hd : ∀ e ∈ L, e.1 ∉ [wT1, wT2, wDen, wE]) {p g : ℕ} (hpv : st.val wp = p)
    (hgv : st.val wg = g) (hqv : st.val wPq = 2 ^ tblPhq p g) (hW : 5 * (p + g) + 40 ≤ W) :
    TblDo A W w (tblBlock 84 tblPhB3 (.mul wE wT2 wE)) st (fun s' =>
      tblKV s' ([(wE, tblPhQ p g), (wDen, 2 ^ tblPhq p g * 4)] ++ L) ∧ s'.acc = st.acc)
      (14 + 1) := by
  have hG := tblPhG_le p g
  have hW2 : 5 * (p + g) + 40 < 2 ^ W :=
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) hW)
  have hq4 : 2 ^ tblPhq p g * 4 < 2 ^ W := by
    rw [show 2 ^ tblPhq p g * 4 = 2 ^ (tblPhq p g + 2) by rw [pow_add]; norm_num]
    exact Nat.pow_lt_pow_right (by norm_num) (by unfold tblPhq; omega)
  have e : ∀ st' : TblSt 84 A, tblExactList A w (tblPhB3 ++ [.mul wE wT2 wE]) st' =
      tblExactList A w [.mul wPq wT1 wDen, .add wp wg wE, .add wE wT1 wE, .mul wE wT2 wE]
        ⟨Function.update (Function.update st'.val wT1 4) wT2 5, st'.acc⟩ := by
    intro st'
    simp only [tblPhB3, List.append_assoc]
    rw [tblExactList_append, tblExactList_const, tblExactList_append, tblExactList_const]
    rfl
  refine (tblKV_block [wT1, wT2, wDen, wE] hL hd ?_ ?_ ?_ ?_).mono (fun _ h => h) (by simp [tblPhB3])
  · simp only [tblPhB3, List.append_assoc]
    refine tblFitsList_append _ _ _ (tblFitsList_const _ _ _ (by omega)) ?_
    rw [tblExactList_const]
    refine tblFitsList_append _ _ _ (tblFitsList_const _ _ _ (by omega)) ?_
    rw [tblExactList_const]
    simp [tblFitsList, TblIns.fits, TblIns.exact, hpv, hgv, hqv]
    omega
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rw [e]
    simp [tblExactList, TblIns.exact, hx]
  · rw [e]; simp [tblExactList, TblIns.exact]
  · rw [e]
    intro e' he'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
    rcases he' with rfl | rfl <;> simp [tblExactList, TblIns.exact, hpv, hgv, hqv, tblPhQ]

theorem tblPhB4_do {A W w : ℕ} (st : TblSt 84 A) {L : List (Fin 84 × ℕ)} (hL : tblKV st L)
    (hd : ∀ e ∈ L, e.1 ∉ [wE]) {G : ℕ} (hGv : st.val wGT = G) (hW : G + 1 < 2 ^ W) :
    TblDo A W w (tblBlock 84 [.copy wGT wE] (.inc wE)) st (fun s' =>
      tblKV s' ([(wE, G + 1)] ++ L) ∧ s'.acc = st.acc) (1 + 1) := by
  refine tblKV_block [wE] hL hd ?_ ?_ ?_ ?_
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hGv]; exact hW
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simp [tblExactList, TblIns.exact, hx]
  · simp [tblExactList, TblIns.exact]
  · intro e' he'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
    rcases he' with rfl
    simp [tblExactList, TblIns.exact, hGv]

/-- The fifth block: `hh := h · 2`, `e := p + 2`. -/
def tblPhB5 : List (TblIns 84) := tblConstL wT1 2 ++ [.mul wH wT1 wHH, .copy wp wE, .inc wE]

theorem tblPhB5_do {A W w : ℕ} (st : TblSt 84 A) {L : List (Fin 84 × ℕ)} (hL : tblKV st L)
    (hd : ∀ e ∈ L, e.1 ∉ [wT1, wHH, wE]) {p h : ℕ} (hpv : st.val wp = p) (hhv : st.val wH = h)
    (hW : h * 2 < 2 ^ W) (hpW : p + 2 < 2 ^ W) :
    TblDo A W w (tblBlock 84 tblPhB5 (.inc wE)) st (fun s' =>
      tblKV s' ([(wE, p + 2), (wHH, h * 2)] ++ L) ∧ s'.acc = st.acc) (6 + 1) := by
  have e : ∀ st' : TblSt 84 A, tblExactList A w (tblPhB5 ++ [.inc wE]) st' =
      tblExactList A w [.mul wH wT1 wHH, .copy wp wE, .inc wE, .inc wE]
        ⟨Function.update st'.val wT1 2, st'.acc⟩ := by
    intro st'
    simp only [tblPhB5, List.append_assoc]
    rw [tblExactList_append, tblExactList_const]
    rfl
  refine (tblKV_block [wT1, wHH, wE] hL hd ?_ ?_ ?_ ?_).mono (fun _ h => h) (by simp [tblPhB5])
  · simp only [tblPhB5, List.append_assoc]
    refine tblFitsList_append _ _ _ (tblFitsList_const _ _ _ (by omega)) ?_
    rw [tblExactList_const]
    simp [tblFitsList, TblIns.fits, TblIns.exact, hpv, hhv]
    omega
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rw [e]
    simp [tblExactList, TblIns.exact, hx]
  · rw [e]; simp [tblExactList, TblIns.exact]
  · rw [e]
    intro e' he'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
    rcases he' with rfl | rfl <;> simp [tblExactList, TblIns.exact, hpv, hhv]

theorem tblPhB6_do {A W w : ℕ} (st : TblSt 84 A) {L : List (Fin 84 × ℕ)} (hL : tblKV st L)
    (hd : ∀ e ∈ L, e.1 ∉ [wCC]) {c : ℕ} (hcv : st.val wCC = c) (hc1 : 1 ≤ c) (hcW : c < 2 ^ W)
    (hone : st.val wOne = 1) :
    TblDo A W w (tblBlock 84 [] (.sub wCC wOne wCC)) st (fun s' =>
      tblKV s' ([(wCC, c - 1)] ++ L) ∧ s'.acc = st.acc) (0 + 1) := by
  refine tblKV_block [wCC] hL hd ?_ ?_ ?_ ?_
  · simp [tblFitsList, TblIns.fits, hcv, hone]; omega
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simp [tblExactList, TblIns.exact, hx]
  · simp [tblExactList, TblIns.exact]
  · intro e' he'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
    rcases he' with rfl
    simp [tblExactList, TblIns.exact, hcv, hone]

theorem tblPhPi_do {A W w : ℕ} (st : TblSt 84 A) {L : List (Fin 84 × ℕ)} (hL : tblKV st L)
    (hd : ∀ e ∈ L, 18 ≤ e.1.val) {P : ℕ} (hP : 2 ≤ P) (h0 : st.val wP = P)
    (hW : 5 * P + 16 ≤ W) :
    TblDo A W w (tblPiCode.rename (Fin.castLE (by norm_num : 18 ≤ 84))) st (fun s' =>
      tblKV s' (((15 : Fin 84), IntegerMultBounds.Resampling.WeightNat.piN P) :: L) ∧ s'.acc = st.acc) (150 * P + 400) := by
  refine (TblDo.rename (Fin.castLE_injective _) (tblPi_do (st.restrict _) hP h0 hW)).mono
    (fun s' ⟨⟨h1, h2⟩, hfr⟩ => ⟨tblKV.cons h1 (fun e he => (hfr e.1 (fun y hy => ?_)).trans (hL e he)),
      h2⟩) le_rfl
  have := congrArg Fin.val hy
  have h18 := hd e he
  simp at this
  omega

/-- The shared initialisation of the phase streams on 84 variables, from `p`, `g`, `N`, `s`,
`w` in variables `54 … 58`. -/
def tblPhaseInit : TblCode 84 :=
  tblBlock 84 tblPhB1 (.zero wX) ;;
  tblPiCode.rename (Fin.castLE (by norm_num : 18 ≤ 84)) ;;
  tblClogCode wPc wC wn ;;
  tblBlock 84 tblPhB2 (.add wE wGT wE) ;;
  tblPow2 wPq wE wI ;;
  tblBlock 84 tblPhB3 (.mul wE wT2 wE) ;;
  tblPow2 wPQ wE wI ;;
  tblBlock 84 [.copy wGT wE] (.inc wE) ;;
  tblPow2 wH wE wI ;;
  tblBlock 84 tblPhB5 (.inc wE) ;;
  tblPow2 wCC wE wI ;;
  tblBlock 84 [] (.sub wCC wOne wCC) ;;
  tblPow2 wPw ww wI

/-- The values established by `tblPhaseInit`. -/
def tblPhaseEnv (p g N s w : ℕ) : List (Fin 84 × ℕ) :=
  [(15, IntegerMultBounds.Resampling.WeightNat.piN (p + g + 4)), (wPq, 2 ^ tblPhq p g),
    (wPQ, 2 ^ tblPhQ p g), (wn, p + g + 14), (wC1, 1), (wp, p), (wg, g), (wN, N),
    ((57 : Fin 84), s), (ww, w), (wOne, 1), (w2N, N + N), (wH, 2 ^ (tblPhG p g + 1)),
    (wHH, 2 ^ (tblPhG p g + 1) * 2), (wPw, 2 ^ w), (wNm1, N - 1), (wCC, 2 ^ (p + 2) - 1),
    ((81 : Fin 84), 2 ^ tblPhq p g * 4)]

/-- The known values after the first block, off variable `0`. -/
private def tblPhL1t (p g N s w : ℕ) : List (Fin 84 × ℕ) :=
  [(wn, p + g + 14), (wOne, 1), (w2N, N + N), (wNm1, N - 1), (wC1, 1), (wp, p), (wg, g), (wN, N),
    ((57 : Fin 84), s), (ww, w)]

/-- The known values after the ceiling logarithm. -/
private def tblPhL3 (p g N s w : ℕ) : List (Fin 84 × ℕ) :=
  [(wC, Nat.clog 2 (p + g + 14)), (wPc, 2 ^ Nat.clog 2 (p + g + 14)),
    (15, IntegerMultBounds.Resampling.WeightNat.piN (p + g + 4)),
    (wn, p + g + 14), (wOne, 1), (w2N, N + N), (wNm1, N - 1), (wC1, 1), (wp, p), (wg, g), (wN, N),
    ((57 : Fin 84), s), (ww, w)]

/-- The known values after `2^q`. -/
private def tblPhL5 (p g N s w : ℕ) : List (Fin 84 × ℕ) :=
  (wPq, 2 ^ tblPhq p g) :: (wGT, tblPhG p g) :: tblPhL3 p g N s w

/-- The known values after `2^Q`. -/
private def tblPhL7 (p g N s w : ℕ) : List (Fin 84 × ℕ) :=
  (wPQ, 2 ^ tblPhQ p g) :: ((81 : Fin 84), 2 ^ tblPhq p g * 4) :: tblPhL5 p g N s w

/-- The known values after `hh`. -/
private def tblPhL10 (p g N s w : ℕ) : List (Fin 84 × ℕ) :=
  [(wE, p + 2), (wHH, 2 ^ (tblPhG p g + 1) * 2), (wH, 2 ^ (tblPhG p g + 1))] ++ tblPhL7 p g N s w

theorem tblPhaseInit_do {A W w : ℕ} (st : TblSt 84 A) {p g N s : ℕ}
    (hin : tblKV st [(wp, p), (wg, g), (wN, N), ((57 : Fin 84), s), (ww, w)])
    (hN : 1 ≤ N) (hN2 : 2 * N < 2 ^ W) (hw : w < W) (hW : 5 * (p + g) + 40 ≤ W) :
    TblDo A W w tblPhaseInit st (fun s' => tblKV s' (tblPhaseEnv p g N s w) ∧ s'.acc = st.acc)
      (200 * (p + g) + 4 * w + 1500) := by
  have hG := tblPhG_le p g
  have hWp : ∀ k, k < W → 2 ^ k < 2 ^ W := fun k hk => Nat.pow_lt_pow_right (by norm_num) hk
  have hpq : tblPhq p g < W := by unfold tblPhq; omega
  have hpQ : tblPhQ p g < W := by unfold tblPhQ; omega
  have hpv : st.val wp = p := hin.get (by simp)
  have hgv : st.val wg = g := hin.get (by simp)
  -- the last steps, from the known values after `hh`
  have c11 : ∀ s₁ : TblSt 84 A, tblKV s₁ (tblPhL10 p g N s w) ∧ s₁.acc = st.acc →
      TblDo A W w (tblPow2 wCC wE wI ;; tblBlock 84 [] (.sub wCC wOne wCC) ;; tblPow2 wPw ww wI) s₁
        (fun s' => tblKV s' (tblPhaseEnv p g N s w) ∧ s'.acc = st.acc)
        ((4 * (p + 2) + 5) + ((0 + 1) + (4 * w + 5))) := by
    intro s₁ ⟨h₁, ha₁⟩
    refine (tblPow2_kv (by decide) (by decide) (by decide) (by simp [tblPhL10, tblPhL7, tblPhL5,
      tblPhL3]) (E := p + 2) (by simp [tblPhL10]) (by omega) s₁ h₁).seq (fun s₂ ⟨h₂, ha₂⟩ => ?_)
    refine (tblPhB6_do s₂ (L := tblPhL10 p g N s w) (h₂.sub (fun e he => List.mem_cons_of_mem _ he))
      (by simp [tblPhL10, tblPhL7, tblPhL5, tblPhL3]) (c := 2 ^ (p + 2)) (h₂.get (by simp))
      Nat.one_le_two_pow (hWp _ (by omega)) (h₂.get (by simp [tblPhL10, tblPhL7, tblPhL5,
        tblPhL3]))).seq (fun s₃ ⟨h₃, ha₃⟩ => ?_)
    refine (tblPow2_kv (by decide) (by decide) (by decide) (L := [(wCC, 2 ^ (p + 2) - 1)] ++
      tblPhL10 p g N s w) (by simp [tblPhL10, tblPhL7, tblPhL5, tblPhL3]) (E := w)
      (by simp [tblPhL10, tblPhL7, tblPhL5, tblPhL3]) hw s₃ h₃).mono
      (fun s' ⟨h', ha'⟩ => ⟨h'.sub (by simp [tblPhaseEnv, tblPhL10, tblPhL7, tblPhL5, tblPhL3]),
        by rw [ha', ha₃, ha₂, ha₁]⟩) le_rfl
  -- `hh := h · 2`, `e := p + 2`
  have c10 : ∀ s₁ : TblSt 84 A, tblKV s₁ ((wH, 2 ^ (tblPhG p g + 1)) :: tblPhL7 p g N s w) ∧
      s₁.acc = st.acc →
      TblDo A W w (tblBlock 84 tblPhB5 (.inc wE) ;; tblPow2 wCC wE wI ;;
        tblBlock 84 [] (.sub wCC wOne wCC) ;; tblPow2 wPw ww wI) s₁
        (fun s' => tblKV s' (tblPhaseEnv p g N s w) ∧ s'.acc = st.acc)
        ((6 + 1) + ((4 * (p + 2) + 5) + ((0 + 1) + (4 * w + 5)))) := by
    intro s₁ ⟨h₁, ha₁⟩
    have hgt : tblPhG p g + 1 < W := by unfold tblPhq at hpq; omega
    refine (tblPhB5_do s₁ h₁ (by simp [tblPhL7, tblPhL5, tblPhL3]) (p := p)
      (h := 2 ^ (tblPhG p g + 1)) (h₁.get (by simp [tblPhL7, tblPhL5, tblPhL3])) (h₁.get (by simp))
      (by rw [← pow_succ]; exact hWp _ (by unfold tblPhq at hpq; omega))
      (lt_of_lt_of_le (by omega : p + 2 < W) Nat.lt_two_pow_self.le)).seq
      (fun s₂ h₂ => c11 s₂ ⟨h₂.1, by rw [h₂.2, ha₁]⟩)
  -- `h := 2^(gT + 1)`
  have c9 : ∀ s₁ : TblSt 84 A, tblKV s₁ ([(wE, tblPhG p g + 1)] ++ tblPhL7 p g N s w) ∧
      s₁.acc = st.acc →
      TblDo A W w (tblPow2 wH wE wI ;; tblBlock 84 tblPhB5 (.inc wE) ;; tblPow2 wCC wE wI ;;
        tblBlock 84 [] (.sub wCC wOne wCC) ;; tblPow2 wPw ww wI) s₁
        (fun s' => tblKV s' (tblPhaseEnv p g N s w) ∧ s'.acc = st.acc)
        ((4 * (tblPhG p g + 1) + 5) +
          ((6 + 1) + ((4 * (p + 2) + 5) + ((0 + 1) + (4 * w + 5))))) := by
    intro s₁ ⟨h₁, ha₁⟩
    refine (tblPow2_kv (by decide) (by decide) (by decide) (by simp [tblPhL7, tblPhL5, tblPhL3])
      (E := tblPhG p g + 1) (by simp) (by unfold tblPhq at hpq; omega) s₁ h₁).seq
      (fun s₂ ⟨h₂, ha₂⟩ => c10 s₂ ⟨h₂.sub (tbl_sub_skip _ _ _), by rw [ha₂, ha₁]⟩)
  -- `e := gT + 1`
  have c8 : ∀ s₁ : TblSt 84 A, tblKV s₁ ((wPQ, 2 ^ tblPhQ p g) :: [(wE, tblPhQ p g),
      ((81 : Fin 84), 2 ^ tblPhq p g * 4)] ++ tblPhL5 p g N s w) ∧ s₁.acc = st.acc →
      TblDo A W w (tblBlock 84 [.copy wGT wE] (.inc wE) ;; tblPow2 wH wE wI ;;
        tblBlock 84 tblPhB5 (.inc wE) ;; tblPow2 wCC wE wI ;;
        tblBlock 84 [] (.sub wCC wOne wCC) ;; tblPow2 wPw ww wI) s₁
        (fun s' => tblKV s' (tblPhaseEnv p g N s w) ∧ s'.acc = st.acc)
        ((1 + 1) + ((4 * (tblPhG p g + 1) + 5) +
          ((6 + 1) + ((4 * (p + 2) + 5) + ((0 + 1) + (4 * w + 5)))))) := by
    intro s₁ ⟨h₁, ha₁⟩
    refine (tblPhB4_do s₁ (L := tblPhL7 p g N s w) (h₁.sub (tbl_sub_skip _ _ _))
      (by simp [tblPhL7, tblPhL5, tblPhL3]) (h₁.get (by simp [tblPhL5]))
      (lt_of_lt_of_le (by unfold tblPhq at hpq; omega : tblPhG p g + 1 < W)
        Nat.lt_two_pow_self.le)).seq (fun s₂ ⟨h₂, ha₂⟩ => c9 s₂ ⟨h₂, by rw [ha₂, ha₁]⟩)
  -- `2^Q`
  have c7 : ∀ s₁ : TblSt 84 A, tblKV s₁ ([(wE, tblPhQ p g),
      ((81 : Fin 84), 2 ^ tblPhq p g * 4)] ++ tblPhL5 p g N s w) ∧ s₁.acc = st.acc →
      TblDo A W w (tblPow2 wPQ wE wI ;; tblBlock 84 [.copy wGT wE] (.inc wE) ;; tblPow2 wH wE wI ;;
        tblBlock 84 tblPhB5 (.inc wE) ;; tblPow2 wCC wE wI ;;
        tblBlock 84 [] (.sub wCC wOne wCC) ;; tblPow2 wPw ww wI) s₁
        (fun s' => tblKV s' (tblPhaseEnv p g N s w) ∧ s'.acc = st.acc)
        ((4 * tblPhQ p g + 5) + ((1 + 1) + ((4 * (tblPhG p g + 1) + 5) +
          ((6 + 1) + ((4 * (p + 2) + 5) + ((0 + 1) + (4 * w + 5))))))) := by
    intro s₁ ⟨h₁, ha₁⟩
    refine (tblPow2_kv (by decide) (by decide) (by decide) (by simp [tblPhL5, tblPhL3])
      (E := tblPhQ p g) (by simp) hpQ s₁ h₁).seq
      (fun s₂ ⟨h₂, ha₂⟩ => c8 s₂ ⟨h₂, by rw [ha₂, ha₁]⟩)
  -- `den`, `e := Q`
  have c6 : ∀ s₁ : TblSt 84 A, tblKV s₁ ((wPq, 2 ^ tblPhq p g) :: [(wE, tblPhq p g),
      (wGT, tblPhG p g)] ++ tblPhL3 p g N s w) ∧ s₁.acc = st.acc →
      TblDo A W w (tblBlock 84 tblPhB3 (.mul wE wT2 wE) ;; tblPow2 wPQ wE wI ;;
        tblBlock 84 [.copy wGT wE] (.inc wE) ;; tblPow2 wH wE wI ;;
        tblBlock 84 tblPhB5 (.inc wE) ;; tblPow2 wCC wE wI ;;
        tblBlock 84 [] (.sub wCC wOne wCC) ;; tblPow2 wPw ww wI) s₁
        (fun s' => tblKV s' (tblPhaseEnv p g N s w) ∧ s'.acc = st.acc)
        ((14 + 1) + ((4 * tblPhQ p g + 5) + ((1 + 1) + ((4 * (tblPhG p g + 1) + 5) +
          ((6 + 1) + ((4 * (p + 2) + 5) + ((0 + 1) + (4 * w + 5)))))))) := by
    intro s₁ ⟨h₁, ha₁⟩
    refine (tblPhB3_do s₁ (L := tblPhL5 p g N s w) (h₁.sub (tbl_sub_skip _ _ _))
      (by simp [tblPhL5, tblPhL3]) (h₁.get (by simp [tblPhL3])) (h₁.get (by simp [tblPhL3]))
      (h₁.get (by simp)) hW).seq (fun s₂ ⟨h₂, ha₂⟩ => c7 s₂ ⟨h₂, by rw [ha₂, ha₁]⟩)
  -- `2^q`
  have c5 : ∀ s₁ : TblSt 84 A, tblKV s₁ ([(wE, tblPhq p g), (wGT, tblPhG p g)] ++
      tblPhL3 p g N s w) ∧ s₁.acc = st.acc →
      TblDo A W w (tblPow2 wPq wE wI ;; tblBlock 84 tblPhB3 (.mul wE wT2 wE) ;; tblPow2 wPQ wE wI ;;
        tblBlock 84 [.copy wGT wE] (.inc wE) ;; tblPow2 wH wE wI ;;
        tblBlock 84 tblPhB5 (.inc wE) ;; tblPow2 wCC wE wI ;;
        tblBlock 84 [] (.sub wCC wOne wCC) ;; tblPow2 wPw ww wI) s₁
        (fun s' => tblKV s' (tblPhaseEnv p g N s w) ∧ s'.acc = st.acc)
        ((4 * tblPhq p g + 5) + ((14 + 1) + ((4 * tblPhQ p g + 5) + ((1 + 1) +
          ((4 * (tblPhG p g + 1) + 5) +
          ((6 + 1) + ((4 * (p + 2) + 5) + ((0 + 1) + (4 * w + 5))))))))) := by
    intro s₁ ⟨h₁, ha₁⟩
    refine (tblPow2_kv (by decide) (by decide) (by decide) (by simp [tblPhL3])
      (E := tblPhq p g) (by simp) hpq s₁ h₁).seq
      (fun s₂ ⟨h₂, ha₂⟩ => c6 s₂ ⟨h₂, by rw [ha₂, ha₁]⟩)
  -- `gT`, `e := q`
  have c4 : ∀ s₁ : TblSt 84 A, tblKV s₁ (tblPhL3 p g N s w) ∧ s₁.acc = st.acc →
      TblDo A W w (tblBlock 84 tblPhB2 (.add wE wGT wE) ;; tblPow2 wPq wE wI ;;
        tblBlock 84 tblPhB3 (.mul wE wT2 wE) ;; tblPow2 wPQ wE wI ;;
        tblBlock 84 [.copy wGT wE] (.inc wE) ;; tblPow2 wH wE wI ;;
        tblBlock 84 tblPhB5 (.inc wE) ;; tblPow2 wCC wE wI ;;
        tblBlock 84 [] (.sub wCC wOne wCC) ;; tblPow2 wPw ww wI) s₁
        (fun s' => tblKV s' (tblPhaseEnv p g N s w) ∧ s'.acc = st.acc)
        ((11 + 1) + ((4 * tblPhq p g + 5) + ((14 + 1) + ((4 * tblPhQ p g + 5) + ((1 + 1) +
          ((4 * (tblPhG p g + 1) + 5) +
          ((6 + 1) + ((4 * (p + 2) + 5) + ((0 + 1) + (4 * w + 5)))))))))) := by
    intro s₁ ⟨h₁, ha₁⟩
    refine (tblPhB2_do s₁ h₁ (by simp [tblPhL3]) (p := p) (g := g) (by simp [tblPhL3])
      (by simp [tblPhL3]) (by simp [tblPhL3]) (by omega)).seq
      (fun s₂ ⟨h₂, ha₂⟩ => c5 s₂ ⟨h₂, by rw [ha₂, ha₁]⟩)
  -- the ceiling logarithm
  have c3 : ∀ s₁ : TblSt 84 A, tblKV s₁ (((15 : Fin 84),
      IntegerMultBounds.Resampling.WeightNat.piN (p + g + 4)) :: tblPhL1t p g N s w) ∧
      s₁.acc = st.acc →
      TblDo A W w (tblClogCode wPc wC wn ;; tblBlock 84 tblPhB2 (.add wE wGT wE) ;;
        tblPow2 wPq wE wI ;;
        tblBlock 84 tblPhB3 (.mul wE wT2 wE) ;; tblPow2 wPQ wE wI ;;
        tblBlock 84 [.copy wGT wE] (.inc wE) ;; tblPow2 wH wE wI ;;
        tblBlock 84 tblPhB5 (.inc wE) ;; tblPow2 wCC wE wI ;;
        tblBlock 84 [] (.sub wCC wOne wCC) ;; tblPow2 wPw ww wI) s₁
        (fun s' => tblKV s' (tblPhaseEnv p g N s w) ∧ s'.acc = st.acc)
        ((3 + (Nat.clog 2 (p + g + 14) * (1 + 1 + 2) + 2)) +
          ((11 + 1) + ((4 * tblPhq p g + 5) + ((14 + 1) + ((4 * tblPhQ p g + 5) + ((1 + 1) +
          ((4 * (tblPhG p g + 1) + 5) +
          ((6 + 1) + ((4 * (p + 2) + 5) + ((0 + 1) + (4 * w + 5))))))))))) := by
    intro s₁ ⟨h₁, ha₁⟩
    have h2n : 2 * (p + g + 14) < 2 ^ W :=
      lt_of_lt_of_le (by omega : 2 * (p + g + 14) < W) Nat.lt_two_pow_self.le
    refine (tblClog_kv (pw := wPc) (c := wC) (nv := wn) (by decide) (by decide) (by decide)
      (by simp [tblPhL1t]) (N := p + g + 14) (by simp [tblPhL1t]) (by omega) h2n s₁ h₁).seq
      (fun s₂ ⟨h₂, ha₂⟩ => c4 s₂ ⟨h₂, by rw [ha₂, ha₁]⟩)
  -- `π`
  have c2 : ∀ s₁ : TblSt 84 A, tblKV s₁ ((wP, p + g + 4) :: tblPhL1t p g N s w) ∧
      s₁.acc = st.acc →
      TblDo A W w (tblPiCode.rename (Fin.castLE (by norm_num : 18 ≤ 84)) ;;
        tblClogCode wPc wC wn ;; tblBlock 84 tblPhB2 (.add wE wGT wE) ;;
        tblPow2 wPq wE wI ;;
        tblBlock 84 tblPhB3 (.mul wE wT2 wE) ;; tblPow2 wPQ wE wI ;;
        tblBlock 84 [.copy wGT wE] (.inc wE) ;; tblPow2 wH wE wI ;;
        tblBlock 84 tblPhB5 (.inc wE) ;; tblPow2 wCC wE wI ;;
        tblBlock 84 [] (.sub wCC wOne wCC) ;; tblPow2 wPw ww wI) s₁
        (fun s' => tblKV s' (tblPhaseEnv p g N s w) ∧ s'.acc = st.acc)
        ((150 * (p + g + 4) + 400) + ((3 + (Nat.clog 2 (p + g + 14) * (1 + 1 + 2) + 2)) +
          ((11 + 1) + ((4 * tblPhq p g + 5) + ((14 + 1) + ((4 * tblPhQ p g + 5) + ((1 + 1) +
          ((4 * (tblPhG p g + 1) + 5) +
          ((6 + 1) + ((4 * (p + 2) + 5) + ((0 + 1) + (4 * w + 5)))))))))))) := by
    intro s₁ ⟨h₁, ha₁⟩
    refine (tblPhPi_do s₁ (L := tblPhL1t p g N s w) (h₁.sub (fun e he => List.mem_cons_of_mem _ he))
      (by simp [tblPhL1t]) (by omega) (h₁.get (by simp)) (by omega)).seq
      (fun s₂ ⟨h₂, ha₂⟩ => c3 s₂ ⟨h₂, by rw [ha₂, ha₁]⟩)
  refine ((tblPhB1_do st hin hN hN2 (by omega)).seq (fun s₁ ⟨h₁, ha₁⟩ => c2 s₁ ⟨h₁, ha₁⟩)).mono
    (fun _ h => h) ?_
  unfold tblPhq tblPhQ at *
  unfold tblPhG at hG ⊢
  omega

end IntegerMultBounds.MathlibTM2.Fast.TableVM
