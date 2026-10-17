module

public import IntegerMultBounds.MathlibTM2.Fast.TablePhaseInit
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# The chirp axis stream on the table machine

One stream per axis `(N, s)` of the chirp kernel (`Chirp.chirpProd`): the table entries
`axisPhase p g N s j` for `j = 0 … N − 1`, in this order, each written as the `w` pair symbols
`coeffSyms A w (red w ⟨tblAxRe p g N s j, tblAxIm p g N s j⟩)` of its numerators at `p + g` bits
(`TableNum.tbl_axisPhase`).

## Program

`tblChirpCode = tblPhaseInit ;; for j < N do tblChirpBody` on 84 variables. The body:

1. `tblChirpAL`: `u = s j² mod 2N`; the centred numerator `chirpNum N s j = ±tblCMag N u` with
   sign bit `[N < u]` (`tbl_chirpNum_eq`); `|angleNum| = tblYm (piN P) N u`, from
   `⌊piQ P · c / N⌋` with the ceiling `⌈a / N⌉ = ⌊(a + N − 1) / N⌋` for negative `c`
   (`tbl_angleNum_eq`, `tbl_chirp_angle`); the Taylor sign `[c ≥ 0]` (the imaginary Taylor sum
   vanishes for a zero angle, `tbl_cim_zero`).
2. The Taylor machine `tblTaylorCode` on variables `18 … 53` (`tblCore_do`).
3. `tblChirpBL`: the roundings `⌊(D + 2^(gT+1) − [neg]) / 2^(gT+2)⌋` (`tbl_round_machine`), the
   residues `tblSignedL` and one emission.

## Results

* `tblChirpBody_do`: one entry, `(16 + 1) + (39 (p + g + 14) + 56) + (18 + 1)` atoms.
* `tblChirp_do`: the stream `tblChirpStream A w p g N s`, within
  `N (39 (p + g) + 641) + 200 (p + g) + 4 w + 1503` atoms, for `0 < N`, `s N² < 2^W`,
  `8 (p + g) + size N + 80 ≤ W` and `w < W`.
* `tblChirp_host`: the host program `tblHost rg tblChirpCode out` pushes the stream onto `out`
  within `(N (39 (p + g) + 641) + 200 (p + g) + 4 w + 1503) · tblC W w + 2 N w + 2` steps.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds.MathlibTM2.Fast.TableNum IntegerMultBounds.MathlibTM2.Mult.Chirp IntegerMultBounds.MathlibTM2.Layer


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
local notation "w2N" => (61 : Fin 84)
local notation "wH" => (62 : Fin 84)
local notation "wHH" => (63 : Fin 84)
local notation "wPw" => (64 : Fin 84)
local notation "wNm1" => (70 : Fin 84)
local notation "wU" => (71 : Fin 84)
local notation "wCn" => (72 : Fin 84)
local notation "wCm" => (73 : Fin 84)
local notation "wT1" => (74 : Fin 84)
local notation "wT2" => (75 : Fin 84)
local notation "wXs" => (76 : Fin 84)
local notation "wYs" => (77 : Fin 84)
local notation "wT3" => (78 : Fin 84)
local notation "wCC" => (80 : Fin 84)
local notation "wDen" => (81 : Fin 84)

/-- The magnitude of the centred chirp numerator from `u = s j² mod 2N`. -/
def tblCMag (N u : ℕ) : ℕ := u * (1 - tblSdNeg N u) + (N + N - u) * tblSdNeg N u

/-- The magnitude `|angleNum|` from `π_N = piN P`, `N` and `u`. -/
def tblYm (pi N u : ℕ) : ℕ := (pi * tblCMag N u + tblSdNeg N u * (N - 1)) / N

theorem tbl_chirpNum_eq (N s j : ℕ) (hj : j < N) :
    chirpNum N s (j : ZMod N) =
      tblSgn (decide (tblSdNeg N (s * j * j % (N + N)) = 1)) * tblCMag N (s * j * j % (N + N)) := by
  have hv : (j : ZMod N).val = j := ZMod.val_natCast_of_lt hj
  have hu : s * (j : ZMod N).val ^ 2 % (2 * N) = s * j * j % (N + N) := by
    rw [hv, two_mul]; ring_nf
  have hlt : s * j * j % (N + N) < N + N := Nat.mod_lt _ (by omega)
  unfold chirpNum tblCMag tblSdNeg
  rw [hu]
  generalize s * j * j % (N + N) = u at hlt ⊢
  split_ifs with h1 h2 h2
  · omega
  · simp [tblSgn]
  · simp [tblSgn]
    push_cast [Nat.cast_sub hlt.le]
    ring
  · omega

theorem tbl_angleNum_eq (p g N s j : ℕ) (hj : j < N) :
    angleNum p g N s (j : ZMod N) =
      tblSgn (decide (tblSdNeg N (s * j * j % (N + N)) = 1)) *
        (tblYm (IntegerMultBounds.Resampling.WeightNat.piN (p + g + 4)) N (s * j * j % (N + N)) : ℤ) := by
  have hN : 0 < N := by omega
  unfold angleNum anglePrec
  rw [← tblPi_eq_piQ (p + g + 4) (by omega), tbl_chirpNum_eq N s j hj]
  unfold tblYm
  generalize s * j * j % (N + N) = u
  generalize IntegerMultBounds.Resampling.WeightNat.piN (p + g + 4) = pi
  have hb := tbl_sdNeg_le N u
  rcases Nat.lt_or_ge (tblSdNeg N u) 1 with h | h
  · have h0 : tblSdNeg N u = 0 := by omega
    rw [h0]
    simp [tblSgn]
  · have h1 : tblSdNeg N u = 1 := by omega
    rw [h1]
    simp only [tblSgn, decide_true, ite_true, one_mul, neg_mul, mul_neg]
    have e := tbl_neg_ediv (pi * tblCMag N u + (N - 1)) N hN
    rw [← e]
    congr 1
    push_cast [Nat.cast_sub (show 1 ≤ N by omega)]
    ring

theorem tbl_mag_zero_succ (q Q m : ℕ) : tblMag 0 q Q (m + 1) = 0 := by
  simp [tblMag]

theorem tbl_sum_zero_odd (q Q r n : ℕ) (hr : r % 2 = 1) : tblSum 0 q Q r n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [tblSum, ih, zero_add]
    split_ifs with h
    · rcases n with _ | n
      · omega
      · exact tbl_mag_zero_succ q Q n
    · rfl

theorem tbl_cim_zero (b : Bool) (q Q n : ℕ) : tblCim b 0 q Q n = 0 := by
  simp [tblCim, tbl_sum_zero_odd q Q 1 n rfl, tbl_sum_zero_odd q Q 3 n rfl]

/-- The angle numerator of a chirp entry in sign–magnitude form and the imaginary Taylor sign. -/
theorem tbl_chirp_angle (p g N s j : ℕ) (hj : j < N) (q Q n : ℕ) :
    (-angleNum p g N s (j : ZMod N)).natAbs =
        tblYm (IntegerMultBounds.Resampling.WeightNat.piN (p + g + 4)) N (s * j * j % (N + N)) ∧
      tblCim (decide (-angleNum p g N s (j : ZMod N) < 0)) (-angleNum p g N s (j : ZMod N)).natAbs
          q Q n =
        tblCim (decide (1 - tblSdNeg N (s * j * j % (N + N)) = 1))
          (tblYm (IntegerMultBounds.Resampling.WeightNat.piN (p + g + 4)) N (s * j * j % (N + N)))
          q Q n := by
  rw [tbl_angleNum_eq p g N s j hj]
  generalize tblYm (IntegerMultBounds.Resampling.WeightNat.piN (p + g + 4)) N
    (s * j * j % (N + N)) = Y
  have hb := tbl_sdNeg_le N (s * j * j % (N + N))
  generalize tblSdNeg N (s * j * j % (N + N)) = c at hb ⊢
  have hn : (-(tblSgn (decide (c = 1)) * (Y : ℤ))).natAbs = Y := by
    unfold tblSgn; split_ifs <;> simp
  refine ⟨hn, ?_⟩
  rw [hn]
  rcases Nat.eq_zero_or_pos Y with hY | hY
  · subst hY; rw [tbl_cim_zero, tbl_cim_zero]
  · congr 1
    interval_cases c
    · simp [tblSgn]; omega
    · simp [tblSgn]

theorem tbl_cmag_fold (N u : ℕ) :
    u * (1 - tblSdNeg N u) + (N + N - u) * tblSdNeg N u = tblCMag N u := rfl

theorem tbl_cmag_le (N u : ℕ) : tblCMag N u ≤ N + N := by
  unfold tblCMag tblSdNeg
  split_ifs
  · simp
  · simp; omega

theorem tbl_piN_le (P : ℕ) (hP : 2 ≤ P) :
    IntegerMultBounds.Resampling.WeightNat.piN P ≤ 2 ^ (5 * P + 5) := by
  rw [IntegerMultBounds.Resampling.PiNat.piN_eq P hP]
  have := tbl_atanN_le 5 (5 * P) (by norm_num)
  rw [pow_add]
  omega

/-- The index block of a chirp entry: `u = s j² mod 2N`, the sign bit and magnitude of the
centred numerator, `|angleNum|` into variable `18` and the Taylor sign `[angleNum ≥ 0]` into
`36`. -/
def tblChirpAL : List (TblIns 84) :=
  [.mul ws wJ wT1, .mul wT1 wJ wT1, .mod wT1 w2N wU,
    .add wN wU wT1, .inc wT1, .add wU wU wT2, .div wT2 wT1 wCn,
    .sub wOne wCn wT1, .mul wU wT1 wT1, .sub w2N wU wT2, .mul wT2 wCn wT2, .add wT1 wT2 wCm,
    .mul wPi wCm wT1, .mul wCn wNm1 wT2, .add wT1 wT2 wT1, .div wT1 wN wY]

theorem tblChirpA_do {A W w : ℕ} (st : TblSt 84 A) {L : List (Fin 84 × ℕ)} (hL : tblKV st L)
    (hd : ∀ e ∈ L, e.1 ∉ [wT1, wT2, wU, wCn, wCm, wY, wX]) {p g N s j : ℕ}
    (hpi : st.val wPi = IntegerMultBounds.Resampling.WeightNat.piN (p + g + 4))
    (hs : st.val ws = s) (hN : st.val wN = N) (h2N : st.val w2N = N + N)
    (hNm1 : st.val wNm1 = N - 1) (hone : st.val wOne = 1) (hjv : st.val wJ = j) (hj : j < N)
    (hsN : s * N * N < 2 ^ W) (hW : 5 * (p + g + 4) + 7 + Nat.size N ≤ W) :
    TblDo A W w (tblBlock 84 tblChirpAL (.sub wOne wCn wX)) st (fun s' =>
      tblKV s' ([(wY, tblYm (IntegerMultBounds.Resampling.WeightNat.piN (p + g + 4)) N
          (s * j * j % (N + N))), (wX, 1 - tblSdNeg N (s * j * j % (N + N)))] ++ L) ∧
        s'.acc = st.acc) (16 + 1) := by
  have hN0 : 0 < N := by omega
  set u := s * j * j % (N + N) with hu
  set pi := IntegerMultBounds.Resampling.WeightNat.piN (p + g + 4) with hpi'
  have hul : u < N + N := Nat.mod_lt _ (by omega)
  have hcb := tbl_sdNeg_le N u
  have hcm := tbl_cmag_le N u
  have hpib : pi ≤ 2 ^ (5 * (p + g + 4) + 5) := tbl_piN_le _ (by omega)
  have hB : N * 2 ^ (5 * (p + g + 4) + 7) < 2 ^ W := tbl_pow_bound (by omega)
  have hBe : 2 ^ (5 * (p + g + 4) + 7) = 2 ^ (5 * (p + g + 4) + 5) * 4 := by
    rw [show 5 * (p + g + 4) + 7 = (5 * (p + g + 4) + 5) + 2 by ring, pow_add]; norm_num
  have hpc : pi * tblCMag N u ≤ 2 ^ (5 * (p + g + 4) + 5) * (N + N) := Nat.mul_le_mul hpib hcm
  have hsj : s * j ≤ s * N := Nat.mul_le_mul_left _ hj.le
  have hsjj : s * j * j ≤ s * N * N := Nat.mul_le_mul hsj hj.le
  have hc1 : tblSdNeg N u * (N - 1) ≤ N - 1 := by
    have := Nat.mul_le_mul_right (N - 1) hcb; simpa using this
  have hc2 : u * (1 - tblSdNeg N u) ≤ u := by
    have := Nat.mul_le_mul_left u (Nat.sub_le 1 (tblSdNeg N u)); simpa using this
  have hc3 : (N + N - u) * tblSdNeg N u ≤ N + N - u := by
    have := Nat.mul_le_mul_left (N + N - u) hcb; simpa using this
  have hsN' : s * N ≤ s * N * N := Nat.le_mul_of_pos_right _ hN0
  refine tblKV_block [wT1, wT2, wU, wCn, wCm, wY, wX] hL hd ?_ ?_ ?_ ?_
  · simp [tblChirpAL, tblFitsList, TblIns.fits, TblIns.exact, hpi, hs, hN,
      h2N, hNm1, hone, hjv, ← hu, tbl_sd_neg, tbl_cmag_fold]
    have hBB : 2 ^ (5 * (p + g + 4) + 5) * (N + N) * 2 = N * 2 ^ (5 * (p + g + 4) + 7) := by
      rw [hBe]; ring
    have h4 : 4 ≤ 2 ^ (5 * (p + g + 4) + 5) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (5 * (p + g + 4) + 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4N : 2 ^ (5 * (p + g + 4) + 5) * (N + N) ≥ 4 * (N + N) := Nat.mul_le_mul_right _ h4
    and_intros <;> omega
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp [tblChirpAL, tblExactList, TblIns.exact, hx]
  · simp [tblChirpAL, tblExactList, TblIns.exact]
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;>
      simp [tblChirpAL, tblExactList, TblIns.exact, hpi, hs, hN, h2N, hNm1,
        hone, hjv, ← hu, tbl_sd_neg, tbl_cmag_fold, tblYm]

/-- The value computed by `tblSignedL`. -/
def tblSignedM (w sg mg : ℕ) : ℕ := mg * (1 - sg) + (2 ^ w - mg % 2 ^ w) * sg

theorem tbl_signedM_fold (w sg mg : ℕ) :
    mg * (1 - sg) + (2 ^ w - mg % 2 ^ w) * sg = tblSignedM w sg mg := rfl

theorem tbl_signedM_eq (w sg mg : ℕ) (hs : sg ≤ 1) :
    tblSignedM w sg mg = tblSignedVal w (decide (sg = 1)) mg := by
  unfold tblSignedM tblSignedVal
  interval_cases sg <;> simp

theorem tbl_signedM_le (w sg mg : ℕ) (hs : sg ≤ 1) : tblSignedM w sg mg ≤ max mg (2 ^ w) := by
  rw [tbl_signedM_eq w sg mg hs]; exact tblSignedVal_lt _ _ _

theorem tbl_signed_facts (w sg mg : ℕ) (hs : sg ≤ 1) :
    mg % 2 ^ w < 2 ^ w ∧ (2 ^ w - mg % 2 ^ w) * sg ≤ 2 ^ w ∧ mg * (1 - sg) ≤ mg := by
  refine ⟨Nat.mod_lt _ (Nat.two_pow_pos w), ?_, ?_⟩
  · interval_cases sg <;> simp
  · interval_cases sg <;> simp

/-- The rounding and emission block of a chirp entry. -/
def tblChirpBL : List (TblIns 84) :=
  [.add wRM wH wT1, .sub wT1 wRN wT1, .div wT1 wHH wT1,
    .add wIM wH wT2, .sub wT2 wIN wT2, .div wT2 wHH wT2] ++
  tblSignedL wRN wT1 wPw wOne wT3 wXs ++ tblSignedL wIN wT2 wPw wOne wT3 wYs

theorem tblChirpB_do {A W w : ℕ} (st : TblSt 84 A) {L : List (Fin 84 × ℕ)} (hL : tblKV st L)
    (hd : ∀ e ∈ L, e.1 ∉ [wT1, wT2, wT3, wXs, wYs]) {G rn rm i_n im : ℕ}
    (hH : st.val wH = 2 ^ (G + 1)) (hHH : st.val wHH = 2 ^ (G + 1) * 2)
    (hPw : st.val wPw = 2 ^ w) (hone : st.val wOne = 1) (h38 : st.val wRN = rn)
    (h39 : st.val wRM = rm) (h40 : st.val wIN = i_n) (h41 : st.val wIM = im) (hrn : rn ≤ 1)
    (hin : i_n ≤ 1) (hb : rm + 2 ^ (G + 1) < 2 ^ W) (hb' : im + 2 ^ (G + 1) < 2 ^ W)
    (hw : w < W) :
    TblDo A W w (tblBlock 84 tblChirpBL (.emit wXs wYs)) st (fun s' => tblKV s' L ∧
      s'.acc = (tblPairs A w
        (tblSignedVal w (decide (rn = 1)) ((rm + 2 ^ (G + 1) - rn) / (2 ^ (G + 1) * 2)))
        (tblSignedVal w (decide (i_n = 1)) ((im + 2 ^ (G + 1) - i_n) / (2 ^ (G + 1) * 2)))).reverse ++
        st.acc) (18 + 1) := by
  have hwW : 2 ^ w < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) hw
  have hG : 1 ≤ 2 ^ (G + 1) := Nat.one_le_two_pow
  set R1 := (rm + 2 ^ (G + 1) - rn) / (2 ^ (G + 1) * 2) with hR1
  set R2 := (im + 2 ^ (G + 1) - i_n) / (2 ^ (G + 1) * 2) with hR2
  have hR1l : R1 ≤ rm + 2 ^ (G + 1) := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hR2l : R2 ≤ im + 2 ^ (G + 1) := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  obtain ⟨f1, f2, f3⟩ := tbl_signed_facts w rn R1 hrn
  obtain ⟨g1, g2, g3⟩ := tbl_signed_facts w i_n R2 hin
  have m1 := tbl_signedM_le w rn R1 hrn
  have m2 := tbl_signedM_le w i_n R2 hin
  refine TblDo.block _ _ ?_ ⟨fun e he => ?_, ?_⟩
  · simp [tblChirpBL, tblSignedL, tblFitsList, TblIns.fits, TblIns.exact, 
      hH, hHH, hPw, hone, h38, h39, h40, h41, ← hR1, ← hR2, tbl_signedM_fold]
    and_intros <;> omega
  · rw [← hL e he]
    have hx := hd e he
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp [tblChirpBL, tblSignedL, tblExactList, TblIns.exact, hx]
  · simp [tblChirpBL, tblSignedL, tblExactList, TblIns.exact, 
      hH, hHH, hPw, hone, h38, h39, h40, h41, ← hR1, ← hR2, tbl_signedM_fold,
      tbl_signedM_eq w rn R1 hrn, tbl_signedM_eq w i_n R2 hin]

theorem tbl_phase_pairs_red (A w n1 R1 n2 R2 : ℕ) (re im : ℤ)
    (h1 : tblSgn (decide (n1 = 1)) * (R1 : ℤ) = re) (h2 : tblSgn (decide (n2 = 1)) * (R2 : ℤ) = im) :
    tblPairs A w (tblSignedVal w (decide (n1 = 1)) R1) (tblSignedVal w (decide (n2 = 1)) R2) =
      coeffSyms A w (red w ⟨re, im⟩) := by
  unfold tblPairs red
  rw [tblSignedVal_cast, tblSignedVal_cast, ← h1, ← h2]
  congr 2 <;> (unfold tblSgn; split_ifs <;> simp)

/-- The Taylor precision, angle precision and term count of the chirp axis entries. -/
theorem tbl_axRe_eq (p g N s j : ℕ) (hj : j < N) :
    tblAxRe p g N s (j : ZMod N) =
      (tblCre (tblYm (IntegerMultBounds.Resampling.WeightNat.piN (p + g + 4)) N (s * j * j % (N + N)))
        (tblPhq p g) (tblPhQ p g) (p + g + 14) + 2 ^ (tblPhG p g + 1)) / 2 ^ (tblPhG p g + 1 + 1) := by
  unfold tblAxRe
  rw [(tbl_chirp_angle p g N s j hj 0 0 0).1]
  have e1 : 5 * anglePrec p g = tblPhQ p g := by unfold anglePrec tblPhQ; ring
  rw [e1, show 1 + taylorGuard p g = tblPhG p g + 1 by rw [tblPhG_eq]; ring,
    show 2 + taylorGuard p g = tblPhG p g + 1 + 1 by rw [tblPhG_eq]; ring]
  rfl

theorem tbl_axIm_eq (p g N s j : ℕ) (hj : j < N) :
    tblAxIm p g N s (j : ZMod N) =
      (tblCim (decide (1 - tblSdNeg N (s * j * j % (N + N)) = 1))
        (tblYm (IntegerMultBounds.Resampling.WeightNat.piN (p + g + 4)) N (s * j * j % (N + N)))
        (tblPhq p g) (tblPhQ p g) (p + g + 14) + 2 ^ (tblPhG p g + 1)) /
        2 ^ (tblPhG p g + 1 + 1) := by
  unfold tblAxIm
  have e1 : 5 * anglePrec p g = tblPhQ p g := by unfold anglePrec tblPhQ; ring
  rw [(tbl_chirp_angle p g N s j hj _ _ _).2, e1,
    show 1 + taylorGuard p g = tblPhG p g + 1 by rw [tblPhG_eq]; ring,
    show 2 + taylorGuard p g = tblPhG p g + 1 + 1 by rw [tblPhG_eq]; ring]
  rfl

/-- The Taylor machine on variables `18 … 53`. -/
def tblCoreMap (x : Fin 36) : Fin 84 := ⟨x.val + 18, by omega⟩

theorem tblCoreMap_injective : Function.Injective tblCoreMap := fun a b h => by
  have := congrArg Fin.val h
  simp [tblCoreMap] at this
  exact Fin.ext this

/-- The Taylor machine embedded in the phase streams, on known values off `18 … 53`. -/
theorem tblCore_do {A W w : ℕ} (st : TblSt 84 A) {L : List (Fin 84 × ℕ)} (hL : tblKV st L)
    (hd : ∀ e ∈ L, e.1.val < 18 ∨ 54 ≤ e.1.val) {Y q Q n : ℕ} (xneg : Bool)
    (hY : st.val wY = Y) (hpq : st.val wPq = 2 ^ q) (hpQ : st.val wPQ = 2 ^ Q) (hn : st.val wn = n)
    (hx : st.val wX = xneg.toNat) (hone : st.val wC1 = 1) (hYb : Y ≤ 4 * 2 ^ Q)
    (hW : q + Q + Nat.size n + 10 ≤ W) :
    TblDo A W w (tblTaylorCode.rename tblCoreMap) st (fun s' => tblKV s' L ∧ s'.acc = st.acc ∧
      tblSgn (decide (s'.val wRN = 1)) * (s'.val wRM : ℤ) = tblCre Y q Q n ∧ s'.val wRN ≤ 1 ∧
      tblSgn (decide (s'.val wIN = 1)) * (s'.val wIM : ℤ) = tblCim xneg Y q Q n ∧ s'.val wIN ≤ 1 ∧
      s'.val wRM ≤ n * 2 ^ (q + 6) ∧ s'.val wIM ≤ n * 2 ^ (q + 6) ∧
      s'.val wPq = 2 ^ q ∧ s'.val wPQ = 2 ^ Q ∧ s'.val wn = n ∧ s'.val wC1 = 1) (39 * n + 56) := by
  refine (TblDo.rename tblCoreMap_injective (tblTaylor_do (st.restrict tblCoreMap) xneg hY hpq hpQ hn
    hx hone hYb hW)).mono (fun s' ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, hfr⟩ =>
      ⟨fun e he => (hfr e.1 (fun y hy => ?_)).trans (hL e he), h11, h1, h2, h3, h4, h5, h6, h7, h8, h9,
        h10⟩) le_rfl
  have := congrArg Fin.val hy
  have h18 := hd e he
  simp [tblCoreMap] at this
  omega

theorem tblKV_cons_iff {n A : ℕ} (s : TblSt n A) (a : Fin n × ℕ) (l : List (Fin n × ℕ)) :
    tblKV s (a :: l) ↔ s.val a.1 = a.2 ∧ tblKV s l := by
  constructor
  · intro h; exact ⟨h a (by simp), fun e he => h e (List.mem_cons_of_mem _ he)⟩
  · rintro ⟨h1, h2⟩; exact tblKV.cons h1 h2

theorem tblKV_nil {n A : ℕ} (s : TblSt n A) : tblKV s [] ↔ True :=
  ⟨fun _ => trivial, fun _ e he => by simp at he⟩

/-- The known values of `tblPhaseEnv` off the Taylor region `18 … 53`. -/
def tblPhaseEnvO (p g N s w : ℕ) : List (Fin 84 × ℕ) :=
  [(15, IntegerMultBounds.Resampling.WeightNat.piN (p + g + 4)), (wp, p), (wg, g), (wN, N),
    (ws, s), (ww, w), (wOne, 1), (w2N, N + N), (wH, 2 ^ (tblPhG p g + 1)),
    (wHH, 2 ^ (tblPhG p g + 1) * 2), (wPw, 2 ^ w), (wNm1, N - 1), (wCC, 2 ^ (p + 2) - 1),
    (wDen, 2 ^ tblPhq p g * 4)]

theorem tblPhaseEnv_iff {A : ℕ} (st : TblSt 84 A) (p g N s w : ℕ) :
    tblKV st (tblPhaseEnv p g N s w) ↔ tblKV st (tblPhaseEnvO p g N s w) ∧
      st.val wPq = 2 ^ tblPhq p g ∧ st.val wPQ = 2 ^ tblPhQ p g ∧ st.val wn = p + g + 14 ∧
      st.val wC1 = 1 := by
  simp only [tblPhaseEnv, tblPhaseEnvO, tblKV_cons_iff, tblKV_nil]
  tauto

theorem tbl_round_machine (rn rm G : ℕ) (hrn : rn ≤ 1) (C : ℤ)
    (hC : tblSgn (decide (rn = 1)) * (rm : ℤ) = C) :
    tblSgn (decide (rn = 1)) * (((rm + 2 ^ (G + 1) - rn) / (2 ^ (G + 1) * 2) : ℕ) : ℤ) =
      (C + 2 ^ (G + 1)) / 2 ^ (G + 1 + 1) := by
  rw [← hC, tbl_round_signed]
  have ht : (decide (rn = 1)).toNat = rn := by interval_cases rn <;> rfl
  rw [ht, pow_succ 2 (G + 1)]

/-- The body of the chirp axis stream: index block, Taylor machine, rounding and emission. -/
def tblChirpBody : TblCode 84 :=
  tblBlock 84 tblChirpAL (.sub wOne wCn wX) ;; tblTaylorCode.rename tblCoreMap ;;
    tblBlock 84 tblChirpBL (.emit wXs wYs)

/-- The emitted symbols of chirp axis entry `j`: the numerators of `axisPhase p g N s j`. -/
def tblChirpEntry (A w p g N s j : ℕ) : List (Fin (A + 4)) :=
  coeffSyms A w (red w ⟨tblAxRe p g N s (j : ZMod N), tblAxIm p g N s (j : ZMod N)⟩)

theorem tblChirpBody_do {A W w : ℕ} (st : TblSt 84 A) {p g N s j : ℕ}
    (henv : tblKV st (tblPhaseEnv p g N s w)) (hjv : st.val wJ = j) (hj : j < N)
    (hsN : s * N * N < 2 ^ W) (hW : 8 * (p + g) + Nat.size N + 80 ≤ W) (hw : w < W) :
    TblDo A W w tblChirpBody st (fun s' => tblKV s' (tblPhaseEnv p g N s w) ∧ s'.val wJ = j ∧
      s'.acc = (tblChirpEntry A w p g N s j).reverse ++ st.acc)
      ((16 + 1) + ((39 * (p + g + 14) + 56) + (18 + 1))) := by
  have : NeZero N := ⟨by omega⟩
  have hG := tblPhG_le p g
  have hpi : st.val 15 = IntegerMultBounds.Resampling.WeightNat.piN (p + g + 4) := henv.get (by simp [tblPhaseEnv])
  have hsv : st.val ws = s := henv.get (by simp [tblPhaseEnv])
  have hNv : st.val wN = N := henv.get (by simp [tblPhaseEnv])
  have h2N : st.val w2N = N + N := henv.get (by simp [tblPhaseEnv])
  have hNm1 : st.val wNm1 = N - 1 := henv.get (by simp [tblPhaseEnv])
  have hone : st.val wOne = 1 := henv.get (by simp [tblPhaseEnv])
  refine (tblChirpA_do st (L := (wJ, j) :: tblPhaseEnv p g N s w) (tblKV.cons hjv henv)
    (by simp [tblPhaseEnv]) hpi hsv hNv h2N hNm1 hone hjv hj hsN (by omega)).seq
    (fun s₁ ⟨h₁, ha₁⟩ => ?_)
  have h₁E : tblKV s₁ (tblPhaseEnv p g N s w) :=
    h₁.sub (fun e he => List.mem_append_right _ (List.mem_cons_of_mem _ he))
  obtain ⟨h₁O, hq₁, hQ₁, hn₁, hc₁⟩ := (tblPhaseEnv_iff s₁ p g N s w).1 h₁E
  have hY₁ : s₁.val wY = tblYm (IntegerMultBounds.Resampling.WeightNat.piN (p + g + 4)) N (s * j * j % (N + N)) := h₁.get (by simp)
  have hX₁ : s₁.val wX = (decide (1 - tblSdNeg N (s * j * j % (N + N)) = 1)).toNat := by
    rw [h₁.get (show (wX, 1 - tblSdNeg N (s * j * j % (N + N))) ∈ _ by simp)]
    have := tbl_sdNeg_le N (s * j * j % (N + N))
    interval_cases (tblSdNeg N (s * j * j % (N + N))) <;> rfl
  have hYb : tblYm (IntegerMultBounds.Resampling.WeightNat.piN (p + g + 4)) N (s * j * j % (N + N)) ≤ 4 * 2 ^ tblPhQ p g := by
    have h1 := (tbl_chirp_angle p g N s j hj 0 0 0).1
    have h2 := tbl_angle_le p g N s (j : ZMod N)
    rw [Int.natAbs_neg] at h1
    rw [h1] at h2
    have e1 : 5 * anglePrec p g = tblPhQ p g := by unfold anglePrec tblPhQ; ring
    rwa [e1] at h2
  have hsz : Nat.size (p + g + 14) ≤ p + g + 14 := by
    rw [Nat.size_le]; exact Nat.lt_two_pow_self
  refine (tblCore_do s₁ (L := (wJ, j) :: tblPhaseEnvO p g N s w)
    (tblKV.cons (h₁.get (by simp)) h₁O) (by simp [tblPhaseEnvO]) (decide (1 - tblSdNeg N (s * j * j % (N + N)) = 1))
    hY₁ hq₁ hQ₁ hn₁ hX₁ hc₁ hYb (by unfold tblPhq tblPhQ; omega)).seq
    (fun s₂ ⟨h₂, ha₂, hre, hrn, him, hin, hrm, hime, hq₂, hQ₂, hn₂, hc₂⟩ => ?_)
  have h₂E : tblKV s₂ (tblPhaseEnv p g N s w) :=
    (tblPhaseEnv_iff s₂ p g N s w).2 ⟨h₂.sub (fun e he => List.mem_cons_of_mem _ he), hq₂, hQ₂,
      hn₂, hc₂⟩
  have hH : s₂.val wH = 2 ^ (tblPhG p g + 1) := h₂E.get (by simp [tblPhaseEnv])
  have hHH : s₂.val wHH = 2 ^ (tblPhG p g + 1) * 2 := h₂E.get (by simp [tblPhaseEnv])
  have hPw : s₂.val wPw = 2 ^ w := h₂E.get (by simp [tblPhaseEnv])
  have hone₂ : s₂.val wOne = 1 := h₂E.get (by simp [tblPhaseEnv])
  have hj₂ : s₂.val wJ = j := h₂.get (by simp)
  have hbound : (p + g + 14) * 2 ^ (tblPhq p g + 6) + 2 ^ (tblPhG p g + 1) < 2 ^ W := by
    have h1 : (p + g + 14) * 2 ^ (tblPhq p g + 7) < 2 ^ W :=
      tbl_pow_bound (by unfold tblPhq; omega)
    have h2 : 2 ^ (tblPhG p g + 1) ≤ 2 ^ (tblPhq p g + 6) :=
      Nat.pow_le_pow_right (by norm_num) (by unfold tblPhq; omega)
    rw [pow_succ, ← mul_assoc] at h1
    have h3 : 2 ^ (tblPhq p g + 6) ≤ (p + g + 14) * 2 ^ (tblPhq p g + 6) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  refine (tblChirpB_do s₂ (L := (wJ, j) :: tblPhaseEnv p g N s w) (tblKV.cons hj₂ h₂E)
    (by simp [tblPhaseEnv]) hH hHH hPw hone₂ rfl rfl rfl rfl hrn hin (by omega) (by omega) hw).mono
    (fun s' ⟨h₃, ha₃⟩ => ⟨h₃.sub (fun e he => List.mem_cons_of_mem _ he), h₃.get (by simp), ?_⟩)
    le_rfl
  rw [ha₃, ha₂, ha₁]
  congr 1
  unfold tblChirpEntry
  rw [tbl_axRe_eq p g N s j hj, tbl_axIm_eq p g N s j hj]
  exact congrArg List.reverse (tbl_phase_pairs_red A w _ _ _ _ _ _
    (tbl_round_machine _ _ _ hrn _ hre) (tbl_round_machine _ _ _ hin _ him))

/-- The chirp axis stream for one axis `(N, s)`: `tblPhaseInit`, then the entries `j = 0 … N − 1`. -/
def tblChirpCode : TblCode 84 := tblPhaseInit ;; tblFor wJ wN tblChirpBody

/-- The chirp axis stream: entries `j = 0 … N − 1`, each the numerators of `axisPhase p g N s j`
at `p + g` bits as `w` pair symbols. -/
def tblChirpStream (A w p g N s : ℕ) : List (Fin (A + 4)) :=
  (List.range N).flatMap (tblChirpEntry A w p g N s)

theorem tbl_flatMap_range_succ {α : Type} (f : ℕ → List α) (j : ℕ) :
    ((List.range (j + 1)).flatMap f).reverse = (f j).reverse ++ ((List.range j).flatMap f).reverse := by
  rw [List.range_succ, List.flatMap_append, List.reverse_append]
  simp

/-- **The chirp axis stream.** From `p, g, N, s, w` in variables `54 … 58` (`0 < N`, `s N² < 2^W`,
`8 (p + g) + size N + 80 ≤ W`, `w < W`), `tblChirpCode` emits the chirp axis stream, within
`N (39 (p + g) + 641) + 200 (p + g) + 4 w + 1503` atoms. -/
theorem tblChirp_do {A W w : ℕ} (st : TblSt 84 A) {p g N s : ℕ}
    (hin : tblKV st [(wp, p), (wg, g), (wN, N), (ws, s), (ww, w)]) (hN : 0 < N)
    (hsN : s * N * N < 2 ^ W) (hW : 8 * (p + g) + Nat.size N + 80 ≤ W) (hw : w < W) :
    TblDo A W w tblChirpCode st (fun s' => s'.acc = (tblChirpStream A w p g N s).reverse ++ st.acc)
      (N * (39 * (p + g) + 641) + 200 * (p + g) + 4 * w + 1503) := by
  have hN2 : 2 * N < 2 ^ W := by
    have := tbl_pow_bound (n := N) (q := 1) (W := W) (by omega)
    simpa [mul_comm] using this
  have hNW : N < 2 ^ W := by omega
  refine ((tblPhaseInit_do st hin hN hN2 hw (by omega)).seq
    (K₂ := 1 + (N * (((16 + 1) + ((39 * (p + g + 14) + 56) + (18 + 1))) + 1 + 2) + 2))
    (fun s₀ ⟨h₀, ha₀⟩ => ?_)).mono (fun _ h => h) ?_
  · refine TblDo.for N ((16 + 1) + ((39 * (p + g + 14) + 56) + (18 + 1))) (h₀.get (by simp [tblPhaseEnv]))
      hNW (by decide) (fun j s' => tblKV s' (tblPhaseEnv p g N s w) ∧
        s'.acc = ((List.range j).flatMap (tblChirpEntry A w p g N s)).reverse ++ st.acc)
      ⟨fun e he => ?_, by simp [ha₀]⟩ ?_ ?_
    · have hk : e.1 ≠ wJ := by
        intro h
        simp [tblPhaseEnv] at he
        rcases he with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' |
          h' | h' | h' <;> rw [h'] at h <;> simp at h
      simp only [Function.update_of_ne hk]
      exact h₀ e he
    · intro j hj s' ⟨h1, h2⟩ hjv _
      refine (tblChirpBody_do s' h1 hjv hj hsN hW hw).mono (fun s'' ⟨h3, h4, h5⟩ =>
        ⟨h4, h3.get (by simp [tblPhaseEnv]), fun e he => ?_, ?_⟩) le_rfl
      · have hk : e.1 ≠ wJ := by
          intro h
          simp [tblPhaseEnv] at he
          rcases he with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' |
            h' | h' | h' <;> rw [h'] at h <;> simp at h
        simp only [Function.update_of_ne hk]
        exact h3 e he
      · simp only
        rw [h5, h2, tbl_flatMap_range_succ, List.append_assoc]
    · intro s' ⟨_, h2⟩ _ _
      exact h2
  · have e : 16 + 1 + (39 * (p + g + 14) + 56 + (18 + 1)) + 1 + 2 = 39 * (p + g) + 641 := by ring
    rw [e]
    omega

theorem tbl_stream_length (A w N : ℕ) (f : ℕ → List (Fin (A + 4))) (hf : ∀ j, (f j).length = w) :
    ((List.range N).flatMap f).length = N * w := by
  rw [List.length_flatMap]
  simp [hf]

section Host

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → IntegerMultBounds.MathlibTM2.Host.Pr P T Q A U}
  {rg : TblR 84 → Fin T}

/-- **The chirp axis stream on the host.** From registers carrying a state with `acc` empty, values
below `2^W` and `p, g, N, s, w` in variables `54 … 58`, `tblHost rg tblChirpCode out` pushes the
chirp axis stream `tblChirpStream A w p g N s` (entries `j = 0 … N − 1`, first entry first, each
`coeffSyms A w (red w ⟨tblAxRe p g N s j, tblAxIm p g N s j⟩)`, the numerators of
`axisPhase p g N s j` by `TableNum.tbl_axisPhase`) on top of the output register `out`, in at most
`(N (39 (p + g) + 641) + 200 (p + g) + 4 w + 1503) · tblC W w + 2 N w + 2` steps; the input,
output and left stacks and every register outside the layout and `out` are unchanged. -/
theorem tblChirp_host (hrg : Function.Injective rg) {out : Fin T} (hout : ∀ r, rg r ≠ out)
    {W w : ℕ} (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = w)
    (hw : w < W) (st : TblSt 84 A) (hst : ∀ j, st.val j < 2 ^ W) (hacc : st.acc = [])
    {p g N s : ℕ} (hin : tblKV st [(wp, p), (wg, g), (wN, N), (ws, s), (ww, w)]) (hN : 0 < N)
    (hsN : s * N * N < 2 ^ W) (hW : 8 * (p + g) + Nat.size N + 80 ≤ W)
    (v : IntegerMultBounds.MathlibTM2.Host.HS T Q A U) (S : IntegerMultBounds.MathlibTM2.Host.Stacks T A)
    (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' S' m, v'.user = v.user ∧
      m ≤ (N * (39 * (p + g) + 641) + 200 * (p + g) + 4 * w + 1503) * tblC W w + 2 * (N * w) + 2 ∧
      IntegerMultBounds.MathlibTM2.Stack.Exec body (tblHost rg tblChirpCode out) (IntegerMultBounds.MathlibTM2.Host.mk v S) m
        (IntegerMultBounds.MathlibTM2.Host.mk v' S') ∧
      S'.R out = tblChirpStream A w p g N s ++ S.R out ∧ S'.inp = S.inp ∧ S'.out = S.out ∧
      S'.L = S.L ∧ ∀ k, k ≠ out → (∀ r, rg r ≠ k) → S'.R k = S.R k := by
  obtain ⟨v', S', m, st', hp, hu, hm, he, hout', -, hi, ho, hL, hk⟩ :=
    tblHost_runs (body := body) hrg hout wl nl hwl hnl hw.le (tblChirp_do st hin hN hsN hW hw) hst v S hS
  rw [hacc, List.append_nil] at hp
  have hlen : st'.acc.length = N * w := by
    rw [hp, List.length_reverse]
    exact tbl_stream_length A w N _ (fun j => by simp [tblChirpEntry])
  refine ⟨v', S', m, hu, by rw [← hlen]; exact hm, he, ?_, hi, ho, hL, hk⟩
  rw [hout', hp, List.reverse_reverse]

end Host

end IntegerMultBounds.MathlibTM2.Fast.TableVM
