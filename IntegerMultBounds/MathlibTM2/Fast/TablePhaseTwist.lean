module

public import IntegerMultBounds.MathlibTM2.Fast.TablePhaseChirp

/-!
# The twist streams on the table machine

The twist tables of the coefficient twist (`Pipeline.twistPlus`, `Pipeline.twistMinus`) for the
polynomial length `r`: the entries `k = 0 … r − 1`, in this order, each written as the `w` pair
symbols `coeffSyms A w (red w ⟨tblTwRe p r k, ±tblTwIm p r k⟩)` of its numerators at `p` bits
(`TableNum.tbl_twistPlus`, `TableNum.tbl_twistMinus`).

## Program

`tblTwistCode conj = tblPhaseInit ;; for k < r do tblTwistBody conj` on 84 variables, with
`g = 0` in the shared initialisation (`taylorGuard p 0`, `taylorTerms p 0 = p + 14`,
`Q = 5 (p + 4)`). The body:

1. `tblTwistAL`: the angle numerator `twistAngleNum p r k = ⌊piN (p + 4) · k / r⌋ ≥ 0`
   (`tbl_twistAngleNum_eq`) and the Taylor sign `0`.
2. The Taylor machine on variables `18 … 53` (`tblCore_do`).
3. `tblTwistBL conj`: the `diskPhase` truncations `⌊(2^(p+2) − 1) D / 2^(q+2)⌋` with the signs of
   the Taylor sums (`tbl_disk_machine`, `tbl_twRe_eq`, `tbl_twIm_eq`), the imaginary sign flipped
   for `conj = true` (`tbl_sgn_flip`), the residues `tblSignedL` and one emission.

## Results

* `tblTwistBody_do`: one entry, `(2 + 1) + (39 (p + 14) + 56) + (17 + 1)` atoms.
* `tblTwist_do`: the stream `tblTwistStream A w p r conj`, within
  `r (39 p + 626) + 200 p + 4 w + 1503` atoms, for `0 < r`, `8 p + size r + 80 ≤ W`, `w < W`.
* `tblTwist_host`: the host program `tblHost rg (tblTwistCode conj) out` pushes the stream onto
  `out` within `(r (39 p + 626) + 200 p + 4 w + 1503) · tblC W w + 2 r w + 2` steps.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds.MathlibTM2.Fast.TableNum IntegerMultBounds.MathlibTM2.Mult.Chirp IntegerMultBounds.MathlibTM2.Mult.Pipeline IntegerMultBounds.MathlibTM2.Layer

set_option linter.unusedSimpArgs false

local notation "wPi" => (15 : Fin 84)
local notation "wY" => (18 : Fin 84)
local notation "wPq" => (19 : Fin 84)
local notation "wPQ" => (20 : Fin 84)
local notation "wn" => (21 : Fin 84)
local notation "wX" => (36 : Fin 84)
local notation "wC1" => (37 : Fin 84)
local notation "wRN" => (38 : Fin 84)
local notation "wRM" => (39 : Fin 84)
local notation "wIN" => (40 : Fin 84)
local notation "wIM" => (41 : Fin 84)
local notation "wp" => (54 : Fin 84)
local notation "wg" => (55 : Fin 84)
local notation "wN" => (56 : Fin 84)
local notation "ws" => (57 : Fin 84)
local notation "ww" => (58 : Fin 84)
local notation "wOne" => (59 : Fin 84)
local notation "wJ" => (60 : Fin 84)
local notation "wPw" => (64 : Fin 84)
local notation "wT1" => (74 : Fin 84)
local notation "wT2" => (75 : Fin 84)
local notation "wXs" => (76 : Fin 84)
local notation "wYs" => (77 : Fin 84)
local notation "wT3" => (78 : Fin 84)
local notation "wF" => (79 : Fin 84)
local notation "wCC" => (80 : Fin 84)
local notation "wDen" => (81 : Fin 84)

theorem tbl_twistAngleNum_eq (p r k : ℕ) :
    twistAngleNum p r k =
      ((IntegerMultBounds.Resampling.WeightNat.piN (p + 4) * k / r : ℕ) : ℤ) := by
  unfold twistAngleNum
  rw [← tblPi_eq_piQ (p + 4) (by omega)]
  push_cast
  rfl

theorem tbl_tw_q (p : ℕ) : p + 2 + taylorGuard p 0 = tblPhq p 0 := by
  simp [tblPhq, tblPhG_eq]

theorem tbl_tw_Q (p : ℕ) : 5 * (p + 4) = tblPhQ p 0 := by unfold tblPhQ; ring

theorem tbl_twRe_eq (p r k : ℕ) :
    tblTwRe p r k = (((2 ^ (p + 2) - 1 : ℕ) : ℤ) *
      tblCre (IntegerMultBounds.Resampling.WeightNat.piN (p + 4) * k / r) (tblPhq p 0)
        (tblPhQ p 0) (p + 14)).tdiv ((2 ^ tblPhq p 0 * 4 : ℕ) : ℤ) := by
  unfold tblTwRe
  rw [tbl_twistAngleNum_eq, Int.natAbs_natCast, tbl_tw_q, tbl_tw_Q]
  push_cast [Nat.cast_sub (Nat.one_le_two_pow)]
  rw [show taylorTerms p 0 = p + 14 from rfl,
    show (2 : ℤ) ^ (tblPhq p 0 + 2) = 2 ^ tblPhq p 0 * 4 by rw [pow_add]; norm_num]

theorem tbl_twIm_eq (p r k : ℕ) :
    tblTwIm p r k = (((2 ^ (p + 2) - 1 : ℕ) : ℤ) *
      tblCim false (IntegerMultBounds.Resampling.WeightNat.piN (p + 4) * k / r) (tblPhq p 0)
        (tblPhQ p 0) (p + 14)).tdiv ((2 ^ tblPhq p 0 * 4 : ℕ) : ℤ) := by
  unfold tblTwIm
  rw [tbl_twistAngleNum_eq, Int.natAbs_natCast, tbl_tw_q, tbl_tw_Q]
  have : decide ((((IntegerMultBounds.Resampling.WeightNat.piN (p + 4) * k / r : ℕ) : ℤ)) < 0) =
      false := decide_eq_false (not_lt.2 (Int.natCast_nonneg _))
  rw [this]
  push_cast [Nat.cast_sub (Nat.one_le_two_pow)]
  rw [show taylorTerms p 0 = p + 14 from rfl,
    show (2 : ℤ) ^ (tblPhq p 0 + 2) = 2 ^ tblPhq p 0 * 4 by rw [pow_add]; norm_num]

theorem tbl_disk_machine (rn rm c den : ℕ) (C : ℤ)
    (hC : tblSgn (decide (rn = 1)) * (rm : ℤ) = C) :
    tblSgn (decide (rn = 1)) * ((c * rm / den : ℕ) : ℤ) = ((c : ℤ) * C).tdiv den := by
  rw [← hC, tbl_disk_signed]

theorem tbl_sgn_flip (i_n : ℕ) (hin : i_n ≤ 1) (M : ℤ) :
    tblSgn (decide (1 - i_n = 1)) * M = -(tblSgn (decide (i_n = 1)) * M) := by
  interval_cases i_n <;> simp [tblSgn]

/-- The angle block of a twist entry: `|X| = ⌊piN (p + 4) · k / r⌋` into variable `18` and the
Taylor sign `0` into `36`. -/
def tblTwistAL : List (TblIns 84) := [.mul wPi wJ wT1, .div wT1 wN wY]

theorem tblTwistA_do {A W w : ℕ} (st : TblSt 84 A) {L : List (Fin 84 × ℕ)} (hL : tblKV st L)
    (hd : ∀ e ∈ L, e.1 ∉ [wT1, wY, wX]) {pi r k : ℕ} (hpi : st.val wPi = pi)
    (hr : st.val wN = r) (hk : st.val wJ = k) (hb : pi * k < 2 ^ W) :
    TblDo A W w (tblBlock 84 tblTwistAL (.zero wX)) st (fun s' =>
      tblKV s' ([(wY, pi * k / r), (wX, 0)] ++ L) ∧ s'.acc = st.acc) (2 + 1) := by
  refine tblKV_block [wT1, wY, wX] hL hd ?_ ?_ ?_ ?_
  · simp [tblTwistAL, tblFitsList, TblIns.fits, TblIns.exact, hpi, hk]; exact hb
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp [tblTwistAL, tblExactList, TblIns.exact, Function.update_apply, hx]
  · simp [tblTwistAL, tblExactList, TblIns.exact]
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp [tblTwistAL, tblExactList, TblIns.exact, hpi, hk, hr]

/-- The `diskPhase` and emission block of a twist entry; `conj` negates the imaginary part. -/
def tblTwistBL (conj : Bool) : List (TblIns 84) :=
  [.mul wCC wRM wT1, .div wT1 wDen wT1, .mul wCC wIM wT2, .div wT2 wDen wT2, .sub wOne wIN wF] ++
  tblSignedL wRN wT1 wPw wOne wT3 wXs ++ tblSignedL (if conj then wF else wIN) wT2 wPw wOne wT3 wYs

theorem tblTwistB_do {A W w : ℕ} (conj : Bool) (st : TblSt 84 A) {L : List (Fin 84 × ℕ)}
    (hL : tblKV st L) (hd : ∀ e ∈ L, e.1 ∉ [wT1, wT2, wT3, wXs, wYs, wF]) {c den rn rm i_n im : ℕ}
    (hCC : st.val wCC = c) (hDen : st.val wDen = den) (hPw : st.val wPw = 2 ^ w)
    (hone : st.val wOne = 1) (h38 : st.val wRN = rn) (h39 : st.val wRM = rm)
    (h40 : st.val wIN = i_n) (h41 : st.val wIM = im) (hrn : rn ≤ 1) (hin : i_n ≤ 1)
    (hb : c * rm < 2 ^ W) (hb' : c * im < 2 ^ W) (hw : w < W) :
    TblDo A W w (tblBlock 84 (tblTwistBL conj) (.emit wXs wYs)) st (fun s' => tblKV s' L ∧
      s'.acc = (tblPairs A w (tblSignedVal w (decide (rn = 1)) (c * rm / den))
        (tblSignedVal w (decide ((if conj then 1 - i_n else i_n) = 1)) (c * im / den))).reverse ++
        st.acc) (17 + 1) := by
  have hwW : 2 ^ w < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) hw
  have hR1l : c * rm / den ≤ c * rm := Nat.div_le_self _ _
  have hR2l : c * im / den ≤ c * im := Nat.div_le_self _ _
  have hsg : (if conj then 1 - i_n else i_n) ≤ 1 := by split_ifs <;> omega
  obtain ⟨f1, f2, f3⟩ := tbl_signed_facts w rn (c * rm / den) hrn
  obtain ⟨g1, g2, g3⟩ := tbl_signed_facts w (if conj then 1 - i_n else i_n) (c * im / den) hsg
  have m1 := tbl_signedM_le w rn (c * rm / den) hrn
  have m2 := tbl_signedM_le w (if conj then 1 - i_n else i_n) (c * im / den) hsg
  cases conj
  · simp only [Bool.false_eq_true, ite_false] at g1 g2 g3 m2 hsg ⊢
    refine TblDo.block _ _ ?_ ⟨fun e he => ?_, ?_⟩
    · simp [tblTwistBL, tblSignedL, tblFitsList, TblIns.fits, TblIns.exact, Function.update_apply,
        hCC, hDen, hPw, hone, h38, h39, h40, h41, tbl_signedM_fold]
      and_intros <;> omega
    · rw [← hL e he]
      have hx := hd e he
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp [tblTwistBL, tblSignedL, tblExactList, TblIns.exact, Function.update_apply, hx]
    · simp [tblTwistBL, tblSignedL, tblExactList, TblIns.exact, Function.update_apply,
        hCC, hDen, hPw, hone, h38, h39, h40, h41, tbl_signedM_fold,
        tbl_signedM_eq w rn _ hrn, tbl_signedM_eq w i_n _ hin]
  · simp only [ite_true] at g1 g2 g3 m2 hsg ⊢
    refine TblDo.block _ _ ?_ ⟨fun e he => ?_, ?_⟩
    · simp [tblTwistBL, tblSignedL, tblFitsList, TblIns.fits, TblIns.exact, Function.update_apply,
        hCC, hDen, hPw, hone, h38, h39, h40, h41, tbl_signedM_fold]
      and_intros <;> omega
    · rw [← hL e he]
      have hx := hd e he
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp [tblTwistBL, tblSignedL, tblExactList, TblIns.exact, Function.update_apply, hx]
    · simp [tblTwistBL, tblSignedL, tblExactList, TblIns.exact, Function.update_apply,
        hCC, hDen, hPw, hone, h38, h39, h40, h41, tbl_signedM_fold,
        tbl_signedM_eq w rn _ hrn, tbl_signedM_eq w (1 - i_n) _ hsg]

/-- The body of the twist stream: angle block, Taylor machine, `diskPhase` and emission. -/
def tblTwistBody (conj : Bool) : TblCode 84 :=
  tblBlock 84 tblTwistAL (.zero wX) ;; tblTaylorCode.rename tblCoreMap ;;
    tblBlock 84 (tblTwistBL conj) (.emit wXs wYs)

/-- The emitted symbols of twist entry `k`: the numerators of `twistPlus p r k` (`conj = false`)
or `twistMinus p r k` (`conj = true`) at `p` bits. -/
def tblTwistEntry (A w p r : ℕ) (conj : Bool) (k : ℕ) : List (Fin (A + 4)) :=
  coeffSyms A w (red w ⟨tblTwRe p r k, if conj then -tblTwIm p r k else tblTwIm p r k⟩)

theorem tblTwistBody_do {A W w : ℕ} (conj : Bool) (st : TblSt 84 A) {p r s k : ℕ}
    (henv : tblKV st (tblPhaseEnv p 0 r s w)) (hkv : st.val wJ = k) (hk : k < r)
    (hW : 8 * p + Nat.size r + 80 ≤ W) (hw : w < W) :
    TblDo A W w (tblTwistBody conj) st (fun s' => tblKV s' (tblPhaseEnv p 0 r s w) ∧
      s'.val wJ = k ∧ s'.acc = (tblTwistEntry A w p r conj k).reverse ++ st.acc)
      ((2 + 1) + ((39 * (p + 14) + 56) + (17 + 1))) := by
  have hG := tblPhG_le p 0
  have hpi : st.val 15 = IntegerMultBounds.Resampling.WeightNat.piN (p + 4) :=
    henv.get (by simp [tblPhaseEnv])
  have hrv : st.val wN = r := henv.get (by simp [tblPhaseEnv])
  have hpib := tbl_piN_le (p + 4) (by omega)
  have hpk : IntegerMultBounds.Resampling.WeightNat.piN (p + 4) * k < 2 ^ W := by
    have h1 : r * 2 ^ (5 * (p + 4) + 5) < 2 ^ W := tbl_pow_bound (by omega)
    have h2 : IntegerMultBounds.Resampling.WeightNat.piN (p + 4) * k ≤ 2 ^ (5 * (p + 4) + 5) * r :=
      Nat.mul_le_mul hpib hk.le
    rw [mul_comm] at h1
    omega
  refine (tblTwistA_do st (L := (wJ, k) :: tblPhaseEnv p 0 r s w) (tblKV.cons hkv henv)
    (by simp [tblPhaseEnv]) hpi hrv hkv hpk).seq (fun s₁ ⟨h₁, ha₁⟩ => ?_)
  have h₁E : tblKV s₁ (tblPhaseEnv p 0 r s w) :=
    h₁.sub (fun e he => List.mem_append_right _ (List.mem_cons_of_mem _ he))
  obtain ⟨h₁O, hq₁, hQ₁, hn₁, hc₁⟩ := (tblPhaseEnv_iff s₁ p 0 r s w).1 h₁E
  have hY₁ : s₁.val wY = IntegerMultBounds.Resampling.WeightNat.piN (p + 4) * k / r :=
    h₁.get (by simp)
  have hX₁ : s₁.val wX = (false).toNat := h₁.get (show (wX, 0) ∈ _ by simp)
  have hYb : IntegerMultBounds.Resampling.WeightNat.piN (p + 4) * k / r ≤ 4 * 2 ^ tblPhQ p 0 := by
    have h2 := tbl_twistAngleNum_le p r k (by omega) hk.le
    rw [tbl_twistAngleNum_eq, Int.natAbs_natCast, tbl_tw_Q] at h2
    exact h2
  have hsz : Nat.size (p + 0 + 14) ≤ p + 0 + 14 := by
    rw [Nat.size_le]; exact Nat.lt_two_pow_self
  refine (tblCore_do s₁ (L := (wJ, k) :: tblPhaseEnvO p 0 r s w)
    (tblKV.cons (h₁.get (by simp)) h₁O) (by simp [tblPhaseEnvO]) false
    hY₁ hq₁ hQ₁ hn₁ hX₁ hc₁ hYb (by unfold tblPhq tblPhQ; omega)).seq
    (fun s₂ ⟨h₂, ha₂, hre, hrn, him, hin, hrm, hime, hq₂, hQ₂, hn₂, hc₂⟩ => ?_)
  have h₂E : tblKV s₂ (tblPhaseEnv p 0 r s w) :=
    (tblPhaseEnv_iff s₂ p 0 r s w).2 ⟨h₂.sub (fun e he => List.mem_cons_of_mem _ he), hq₂, hQ₂,
      hn₂, hc₂⟩
  have hCC : s₂.val wCC = 2 ^ (p + 2) - 1 := h₂E.get (by simp [tblPhaseEnv])
  have hDen : s₂.val wDen = 2 ^ tblPhq p 0 * 4 := h₂E.get (by simp [tblPhaseEnv])
  have hPw : s₂.val wPw = 2 ^ w := h₂E.get (by simp [tblPhaseEnv])
  have hone₂ : s₂.val wOne = 1 := h₂E.get (by simp [tblPhaseEnv])
  have hk₂ : s₂.val wJ = k := h₂.get (by simp)
  have hbound : (2 ^ (p + 2) - 1) * ((p + 0 + 14) * 2 ^ (tblPhq p 0 + 6)) < 2 ^ W := by
    have h1 : (p + 0 + 14) * 2 ^ (tblPhq p 0 + 6 + (p + 2)) < 2 ^ W :=
      tbl_pow_bound (by unfold tblPhq; omega)
    have h2 : (2 ^ (p + 2) - 1) * ((p + 0 + 14) * 2 ^ (tblPhq p 0 + 6)) ≤
        (p + 0 + 14) * 2 ^ (tblPhq p 0 + 6 + (p + 2)) := by
      rw [show 2 ^ (tblPhq p 0 + 6 + (p + 2)) = 2 ^ (tblPhq p 0 + 6) * 2 ^ (p + 2) from
        pow_add _ _ _]
      calc (2 ^ (p + 2) - 1) * ((p + 0 + 14) * 2 ^ (tblPhq p 0 + 6))
          ≤ 2 ^ (p + 2) * ((p + 0 + 14) * 2 ^ (tblPhq p 0 + 6)) :=
            Nat.mul_le_mul_right _ (Nat.sub_le _ _)
        _ = (p + 0 + 14) * (2 ^ (tblPhq p 0 + 6) * 2 ^ (p + 2)) := by ring
    omega
  have hb1 : (2 ^ (p + 2) - 1) * s₂.val wRM < 2 ^ W :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ hrm) hbound
  have hb2 : (2 ^ (p + 2) - 1) * s₂.val wIM < 2 ^ W :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ hime) hbound
  refine (tblTwistB_do conj s₂ (L := (wJ, k) :: tblPhaseEnv p 0 r s w) (tblKV.cons hk₂ h₂E)
    (by simp [tblPhaseEnv]) hCC hDen hPw hone₂ rfl rfl rfl rfl hrn hin hb1 hb2 hw).mono
    (fun s' ⟨h₃, ha₃⟩ => ⟨h₃.sub (fun e he => List.mem_cons_of_mem _ he), h₃.get (by simp), ?_⟩)
    le_rfl
  rw [ha₃, ha₂, ha₁]
  congr 1
  unfold tblTwistEntry
  have hre' := tbl_disk_machine _ _ (2 ^ (p + 2) - 1) (2 ^ tblPhq p 0 * 4) _ hre
  have him' := tbl_disk_machine _ _ (2 ^ (p + 2) - 1) (2 ^ tblPhq p 0 * 4) _ him
  rw [← tbl_twRe_eq] at hre'
  rw [← tbl_twIm_eq] at him'
  cases conj
  · exact congrArg List.reverse (tbl_phase_pairs_red A w _ _ _ _ _ _ hre' him')
  · refine congrArg List.reverse (tbl_phase_pairs_red A w _ _ _ _ _ _ hre' ?_)
    simp only [ite_true]
    rw [tbl_sgn_flip _ hin, him']

/-- The twist stream: `tblPhaseInit` with `g = 0`, then the entries `k = 0 … r − 1`. -/
def tblTwistCode (conj : Bool) : TblCode 84 := tblPhaseInit ;; tblFor wJ wN (tblTwistBody conj)

/-- The twist stream: entries `k = 0 … r − 1`, each the numerators of `twistPlus p r k`
(`conj = false`) or `twistMinus p r k` (`conj = true`) at `p` bits as `w` pair symbols. -/
def tblTwistStream (A w p r : ℕ) (conj : Bool) : List (Fin (A + 4)) :=
  (List.range r).flatMap (tblTwistEntry A w p r conj)

/-- **The twist stream.** From `p, 0, r, s, w` in variables `54 … 58` (`0 < r`,
`8 p + size r + 80 ≤ W`, `w < W`; `s` arbitrary), `tblTwistCode conj` emits the twist stream,
within `r (39 p + 626) + 200 p + 4 w + 1503` atoms. -/
theorem tblTwist_do {A W w : ℕ} (conj : Bool) (st : TblSt 84 A) {p r s : ℕ}
    (hin : tblKV st [(wp, p), (wg, 0), (wN, r), (ws, s), (ww, w)]) (hr : 0 < r)
    (hW : 8 * p + Nat.size r + 80 ≤ W) (hw : w < W) :
    TblDo A W w (tblTwistCode conj) st
      (fun s' => s'.acc = (tblTwistStream A w p r conj).reverse ++ st.acc)
      (r * (39 * p + 626) + 200 * p + 4 * w + 1503) := by
  have hN2 : 2 * r < 2 ^ W := by
    have := tbl_pow_bound (n := r) (q := 1) (W := W) (by omega)
    simpa [mul_comm] using this
  have hNW : r < 2 ^ W := by omega
  refine ((tblPhaseInit_do st hin hr hN2 hw (by omega)).seq
    (K₂ := 1 + (r * (((2 + 1) + ((39 * (p + 14) + 56) + (17 + 1))) + 1 + 2) + 2))
    (fun s₀ ⟨h₀, ha₀⟩ => ?_)).mono (fun _ h => h) ?_
  · refine TblDo.for r ((2 + 1) + ((39 * (p + 14) + 56) + (17 + 1)))
      (h₀.get (by simp [tblPhaseEnv])) hNW (by decide) (fun k s' => tblKV s' (tblPhaseEnv p 0 r s w) ∧
        s'.acc = ((List.range k).flatMap (tblTwistEntry A w p r conj)).reverse ++ st.acc)
      ⟨fun e he => ?_, by simp [ha₀]⟩ ?_ ?_
    · have hk : e.1 ≠ wJ := by
        intro h
        simp [tblPhaseEnv] at he
        rcases he with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' |
          h' | h' | h' <;> rw [h'] at h <;> simp at h
      simp only [Function.update_of_ne hk]
      exact h₀ e he
    · intro k hk s' ⟨h1, h2⟩ hkv _
      refine (tblTwistBody_do conj s' h1 hkv hk hW hw).mono (fun s'' ⟨h3, h4, h5⟩ =>
        ⟨h4, h3.get (by simp [tblPhaseEnv]), fun e he => ?_, ?_⟩) le_rfl
      · have hk' : e.1 ≠ wJ := by
          intro h
          simp [tblPhaseEnv] at he
          rcases he with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' |
            h' | h' | h' <;> rw [h'] at h <;> simp at h
        simp only [Function.update_of_ne hk']
        exact h3 e he
      · simp only
        rw [h5, h2, tbl_flatMap_range_succ, List.append_assoc]
    · intro s' ⟨_, h2⟩ _ _
      exact h2
  · have e : 2 + 1 + (39 * (p + 14) + 56 + (17 + 1)) + 1 + 2 = 39 * p + 626 := by ring
    rw [e]
    omega

section Host

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → IntegerMultBounds.MathlibTM2.Host.Pr P T Q A U}
  {rg : TblR 84 → Fin T}

/-- **The twist stream on the host.** From registers carrying a state with `acc` empty, values
below `2^W` and `p, 0, r, s, w` in variables `54 … 58`, `tblHost rg (tblTwistCode conj) out`
pushes the twist stream `tblTwistStream A w p r conj` (entries `k = 0 … r − 1`, first entry first,
each `coeffSyms A w (red w ⟨tblTwRe p r k, ±tblTwIm p r k⟩)`, the numerators of `twistPlus p r k`,
resp. `twistMinus p r k`, by `TableNum.tbl_twistPlus`, `TableNum.tbl_twistMinus`) on top of the
output register `out`, in at most `(r (39 p + 626) + 200 p + 4 w + 1503) · tblC W w + 2 r w + 2`
steps; the input, output and left stacks and every register outside the layout and `out` are
unchanged. -/
theorem tblTwist_host (conj : Bool) (hrg : Function.Injective rg) {out : Fin T}
    (hout : ∀ r, rg r ≠ out) {W w : ℕ} (wl nl : List (Fin (A + 4))) (hwl : wl.length = W)
    (hnl : nl.length = w) (hw : w < W) (st : TblSt 84 A) (hst : ∀ j, st.val j < 2 ^ W)
    (hacc : st.acc = []) {p r s : ℕ} (hin : tblKV st [(wp, p), (wg, 0), (wN, r), (ws, s), (ww, w)])
    (hr : 0 < r) (hW : 8 * p + Nat.size r + 80 ≤ W)
    (v : IntegerMultBounds.MathlibTM2.Host.HS T Q A U) (S : IntegerMultBounds.MathlibTM2.Host.Stacks T A)
    (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' S' m, v'.user = v.user ∧
      m ≤ (r * (39 * p + 626) + 200 * p + 4 * w + 1503) * tblC W w + 2 * (r * w) + 2 ∧
      IntegerMultBounds.MathlibTM2.Stack.Exec body (tblHost rg (tblTwistCode conj) out) (IntegerMultBounds.MathlibTM2.Host.mk v S) m
        (IntegerMultBounds.MathlibTM2.Host.mk v' S') ∧
      S'.R out = tblTwistStream A w p r conj ++ S.R out ∧ S'.inp = S.inp ∧ S'.out = S.out ∧
      S'.L = S.L ∧ ∀ k, k ≠ out → (∀ r, rg r ≠ k) → S'.R k = S.R k := by
  obtain ⟨v', S', m, st', hp, hu, hm, he, hout', -, hi, ho, hL, hk⟩ :=
    tblHost_runs (body := body) hrg hout wl nl hwl hnl hw.le (tblTwist_do conj st hin hr hW hw) hst
      v S hS
  rw [hacc, List.append_nil] at hp
  have hlen : st'.acc.length = r * w := by
    rw [hp, List.length_reverse]
    exact tbl_stream_length A w r _ (fun j => by simp [tblTwistEntry])
  refine ⟨v', S', m, hu, by rw [← hlen]; exact hm, he, ?_, hi, ho, hL, hk⟩
  rw [hout', hp, List.reverse_reverse]

end Host

end IntegerMultBounds.MathlibTM2.Fast.TableVM
