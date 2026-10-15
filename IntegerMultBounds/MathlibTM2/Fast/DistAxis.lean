module

public import IntegerMultBounds.MathlibTM2.Fast.DistBase

/-!
# The axis loop of the distribution machine

One loop over the axes `i = 0, …, d - 1` computes, in the variables of the parameter layout,
the per-axis values of the records of the stage loaders and pushes them in unary.

## Values

On ℕ indices: `dsT n i = t_i` (`R = 2^(ℓ-1)` below `numHalf`, `r` above; `dsT_eq`),
`dsP n i = ∏_{j<i} t_j`, `dsL n i = log₂ t_i`, `dsQ n i = p + 1` (`p` on the last axis),
`dsS n i = s_i` (`Moduli.modulus`), `dsG n i = (T / r) / (P_i t_i)` (`1` on the last axis): the
product of the lengths strictly between axis `i` and the last axis.

## States

The variables `0 … 30` hold the parameters (`pmVal`), `38` holds the table word size `W`.
Between iterations (`dsLV n W i`): `31` holds `i`, `32` holds `P_i`, `33 … 37`, `39` hold `0`.
After the axis code (`dsAV n W i`): `33 … 37` hold `t_i`, `log₂ t_i`, `s_i`, `q_i`, `G_i`.

## Programs

* `dsAxC` (`dsAxC_do`): from `dsLV n W i` to `dsAV n W i`, `33` atoms.
* `dsUpC` (`dsUpC_do`): from `dsAV n W i` to `dsLV n W (i + 1)` (`P_{i+1} = P_i t_i`), `7` atoms.
* `dsAxBody rg L`: `dsAxC`, the pushes `L`, `dsUpC`.
* `dsAxes rg uD tm L = scanP uD tm (dsAxBody rg L)` with `d` symbols on `uD`
  (`ds_axes`): every register `k` gains `dsAcc n W L (d n) k`, the pushes of the axes
  `d - 1, …, 0` from the top.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Moduli

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-! ### Values -/

section Values

/-- The axis length `t_i` on ℕ indices. -/
def dsT (n i : ℕ) : ℕ := pmTv (numHalf n) (2 ^ (ℓ n - 1)) (r n) i

/-- The prefix product `P_i = ∏_{j < i} t_j`. -/
def dsP (n i : ℕ) : ℕ := ∏ j ∈ Finset.range i, dsT n j

/-- `log₂ t_i`. -/
def dsL (n i : ℕ) : ℕ := if i < numHalf n then ℓ n - 1 else ℓ n

/-- The product shift of the `Ã` record: `p + 1`, and `p` on the last axis. -/
def dsQ (n i : ℕ) : ℕ := if i + 1 < d n then p n + 1 else p n

/-- The source length `s_i`. -/
def dsS (n i : ℕ) : ℕ := modulus (N n) (pmX0 n) (numHalf n) i

/-- The product of the lengths strictly between axis `i` and the last axis. -/
def dsG (n i : ℕ) : ℕ := if i + 1 < d n then T n / r n / (dsP n i * dsT n i) else 1

theorem dsT_eq (n : ℕ) (i : Fin (d n)) : dsT n i = t n i := pmTv_eq n i

theorem dsS_eq (n : ℕ) (i : Fin (d n)) : dsS n i = s n i := rfl

theorem dsT_le {n : ℕ} (hn : 2 ≤ n) (i : ℕ) : dsT n i ≤ r n := by
  have := pm_one_le_ℓ hn
  unfold dsT pmTv r
  split_ifs
  · exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · exact le_rfl

theorem dsT_pos (n i : ℕ) : 0 < dsT n i := by
  unfold dsT pmTv r
  split_ifs <;> positivity

theorem dsT_last {n : ℕ} (hn : 2 ≤ n) : dsT n (d n - 1) = r n := by
  have h := numHalf_lt (one_le_d hn)
  unfold dsT pmTv
  rw [if_neg (by omega)]

theorem dsP_zero (n : ℕ) : dsP n 0 = 1 := rfl

theorem dsP_succ (n i : ℕ) : dsP n (i + 1) = dsP n i * dsT n i := Finset.prod_range_succ _ _

theorem dsP_pos (n i : ℕ) : 0 < dsP n i :=
  Finset.prod_pos fun j _ => dsT_pos n j

theorem dsP_d {n : ℕ} (hn : 2 ≤ n) : dsP n (d n) = T n := by
  rw [← prod_t (one_le_d hn), dsP, ← Fin.prod_univ_eq_prod_range]
  exact Finset.prod_congr rfl fun i _ => dsT_eq n i

theorem dsP_dvd (n : ℕ) {i j : ℕ} (hij : i ≤ j) : dsP n i ∣ dsP n j :=
  Finset.prod_dvd_prod_of_subset _ _ _ (Finset.range_subset_range.2 hij)

theorem dsP_le {n : ℕ} (hn : 2 ≤ n) {i : ℕ} (hi : i ≤ d n) : dsP n i ≤ T n := by
  rw [← dsP_d hn]
  exact Nat.le_of_dvd (dsP_pos n _) (dsP_dvd n hi)

theorem dsT_dvd_T {n : ℕ} (hn : 2 ≤ n) : r n ∣ T n := by
  have := one_le_d hn
  have h := dsP_dvd n (show d n - 1 + 1 ≤ d n by omega)
  rw [dsP_succ, dsT_last hn, dsP_d hn] at h
  exact Dvd.dvd.trans (Dvd.intro_left _ rfl) h

/-- `T = P_{d-1} r`. -/
theorem dsP_last {n : ℕ} (hn : 2 ≤ n) : dsP n (d n - 1) * r n = T n := by
  have hd := one_le_d hn
  rw [← dsT_last hn, ← dsP_succ, Nat.sub_add_cancel hd, dsP_d hn]

/-- For `i + 1 < d`: `P_i t_i G_i r = T`. -/
theorem dsG_mul {n : ℕ} (hn : 2 ≤ n) {i : ℕ} (hi : i + 1 < d n) :
    dsP n i * dsT n i * dsG n i * r n = T n := by
  have hd := dsP_dvd n (show i + 1 ≤ d n - 1 by omega)
  rw [dsP_succ] at hd
  obtain ⟨c, hc⟩ := hd
  have hr := dsP_last hn
  have hpos : 0 < dsP n i * dsT n i := Nat.mul_pos (dsP_pos n i) (dsT_pos n i)
  have hrpos : 0 < r n := by unfold r; positivity
  have e1 : T n / r n = dsP n i * dsT n i * c := by
    rw [← hr, hc, Nat.mul_div_cancel _ hrpos]
  unfold dsG
  rw [if_pos hi, e1, Nat.mul_div_cancel_left _ hpos, ← e1, Nat.div_mul_cancel (dsT_dvd_T hn)]

theorem dsG_le {n : ℕ} (hn : 2 ≤ n) (i : ℕ) : dsG n i ≤ T n := by
  by_cases hi : i + 1 < d n
  · have h := dsG_mul hn hi
    have h1 : 1 ≤ dsP n i * dsT n i := Nat.mul_pos (dsP_pos n i) (dsT_pos n i)
    have h2 : 1 ≤ r n := by unfold r; exact Nat.one_le_two_pow
    calc dsG n i ≤ dsP n i * dsT n i * dsG n i * r n := by
          calc dsG n i = 1 * dsG n i * 1 := by ring
            _ ≤ dsP n i * dsT n i * dsG n i * r n :=
              Nat.mul_le_mul (Nat.mul_le_mul_right _ h1) h2
      _ = T n := h
  · unfold dsG
    rw [if_neg hi]
    unfold T; exact Nat.one_le_two_pow

end Values

/-! ### States and the table code -/

section Code

variable {A W' w : ℕ}

/-- The variables between iterations: the parameters, `i` in `31`, `P_i` in `32`, `W` in `38`. -/
def dsLV (n W i : ℕ) (j : Fin pmNV) : ℕ :=
  if j.val < 31 then pmVal n j else if j.val = 31 then i else if j.val = 32 then dsP n i
  else if j.val = 38 then W else 0

/-- The variables after the axis code: `t_i`, `log₂ t_i`, `s_i`, `q_i`, `G_i` in `33 … 37`. -/
def dsAV (n W i : ℕ) (j : Fin pmNV) : ℕ :=
  if j.val = 33 then dsT n i else if j.val = 34 then dsL n i else if j.val = 35 then dsS n i
  else if j.val = 36 then dsQ n i else if j.val = 37 then dsG n i else dsLV n W i j

/-- The axis code: `t`, `log₂ t` by the test `i < numHalf`; `q := p`, `+ 1` and
`G := (T / r) / (P t)` when `i + 1 < d` (else `G := 1`); `s_i` by `pmModC`; scratch `39`
cleared. -/
def dsAxC : TblCode pmNV :=
  .ite 31 11 (tblBlock pmNV [.copy 10 33] (.copy 9 34)) (tblBlock pmNV [.copy 8 33] (.copy 7 34)) ;;
  tblBlock pmNV [.copy 2 36, .copy 31 39] (.inc 39) ;;
  .ite 39 3 (tblBlock pmNV [.inc 36, .div 6 8 37, .mul 32 33 39] (.div 37 39 37))
    (tblBlock pmNV [.zero 37] (.inc 37)) ;;
  pmModC.rename ![16, 17, 11, 31, 35, 39] ;; .ins (.zero 39)

/-- The update code: `P := P t`, `i := i + 1`, `33 … 37` cleared. -/
def dsUpC : TblCode pmNV :=
  tblBlock pmNV [.mul 32 33 32, .inc 31, .zero 33, .zero 34, .zero 35, .zero 36] (.zero 37)

/-- Values linear in `b` fit the words of the parameter machine. -/
theorem ds_small (n : ℕ) {x : ℕ} (hx : x ≤ 1000 * (b n + 1)) : x < 2 ^ pmW n := by
  have h1 : b n + 1 ≤ 2 ^ b n := Nat.lt_two_pow_self
  have h2 : 2 ^ (b n + 10) ≤ 2 ^ pmW n := pm_two_pow_le (by have := pmW_ge n; omega)
  have e : 2 ^ (b n + 10) = 1024 * 2 ^ b n := by rw [pow_add]; ring
  omega

theorem dsS_lt {n : ℕ} (hn : 2 ≤ n) {i : ℕ} (hi : i < d n) : dsS n i < 2 ^ pmW n := by
  have h1 := pm_modulus_le_bound (N n) (pmX0 n) (numHalf n) i
  have h2 := pm_modBound_lt hn hi
  have h3 : 2 ^ (2 * b n + 9) ≤ 2 ^ pmW n := pm_two_pow_le (by have := pmW_ge n; omega)
  unfold dsS; omega

/-- The parameters fit the words of the parameter machine. -/
theorem ds_pmVals_lt {n : ℕ} (hn : 2 ≤ n) (j : Fin pmNV) : pmVals n j < 2 ^ pmW n := by
  obtain ⟨st', k, hb, ⟨hv, -⟩, -⟩ := pmCode1_do (A := 0) (w := pmW n) hn (pmW_ge n)
    (pmSt0 0 n) (pm_st0_F n)
  have := hb.lt (pm_st0_lt n) j
  rwa [hv] at this

theorem ds_pmVal_lt {n : ℕ} (hn : 2 ≤ n) (j : ℕ) : pmVal n j < 2 ^ pmW n := by
  by_cases hj : j < 40
  · exact ds_pmVals_lt hn ⟨j, hj⟩
  · rw [pmVal_ge n j (by omega)]; exact Nat.two_pow_pos _

theorem ds_T_lt {n : ℕ} (hn : 2 ≤ n) : T n < 2 ^ pmW n := ds_pmVal_lt hn 6

theorem ds_d_lt {n : ℕ} (hn : 2 ≤ n) : d n < 2 ^ pmW n := ds_pmVal_lt hn 3

theorem dsLV_lt {n W : ℕ} (hn : 2 ≤ n) (hW : W < 2 ^ pmW n) {i : ℕ} (hi : i ≤ d n)
    (j : Fin pmNV) : dsLV n W i j < 2 ^ pmW n := by
  have hT := ds_T_lt hn
  have hd := ds_d_lt hn
  have hP := dsP_le hn hi
  unfold dsLV
  split_ifs
  · exact ds_pmVal_lt hn j
  · omega
  · omega
  · exact hW
  · exact Nat.two_pow_pos _

theorem dsAV_lt {n W : ℕ} (hn : 2 ≤ n) (hW : W < 2 ^ pmW n) {i : ℕ} (hi : i < d n)
    (j : Fin pmNV) : dsAV n W i j < 2 ^ pmW n := by
  have hT := ds_T_lt hn
  have ht := dsT_le hn i
  have hr : r n ≤ T n := pm_r_le_T hn
  have hG := dsG_le hn i
  have hl : ℓ n ≤ T n := (Nat.lt_two_pow_self).le.trans hr
  have hp : p n + 1 < 2 ^ pmW n := ds_small n (by unfold p; omega)
  unfold dsAV
  split_ifs
  · omega
  · unfold dsL; split_ifs <;> omega
  · exact dsS_lt hn hi
  · unfold dsQ; split_ifs <;> omega
  · omega
  · exact dsLV_lt hn hW hi.le j

/-- The variables after the lengths. -/
def dsSA (n Wt i : ℕ) : Fin pmNV → ℕ :=
  Function.update (Function.update (dsLV n Wt i) 33 (dsT n i)) 34 (dsL n i)

/-- The variables after `q := p`, `39 := i + 1`. -/
def dsSB (n Wt i : ℕ) : Fin pmNV → ℕ :=
  Function.update (Function.update (dsSA n Wt i) 36 (p n)) 39 (i + 1)

/-- The variables after `q`, `G` (off `39`). -/
def dsSC (n Wt i : ℕ) : Fin pmNV → ℕ :=
  Function.update (Function.update (dsSB n Wt i) 36 (dsQ n i)) 37 (dsG n i)

theorem dsAV_eq (n Wt i : ℕ) :
    dsAV n Wt i = Function.update (Function.update (dsSC n Wt i) 35 (dsS n i)) 39 0 := by
  funext j
  fin_cases j <;> simp [dsAV, dsSC, dsSB, dsSA, dsLV, Fin.ext_iff, pmNV]

section Steps

variable {n Wt i : ℕ}

theorem dsAxC_A :
    TblDo A (pmW n) w (.ite 31 11 (tblBlock pmNV [.copy 10 33] (.copy 9 34))
      (tblBlock pmNV [.copy 8 33] (.copy 7 34))) ⟨dsLV n Wt i, []⟩ (· = ⟨dsSA n Wt i, []⟩) 3 := by
  by_cases h : i < numHalf n
  · refine (TblDo.iteT (by simp [dsLV, h, pmNV, pmVal]) (TblDo.block _ _
      (by simp [tblFitsList, TblIns.fits]) ?_)).mono (fun _ h => h) (by norm_num)
    simp [tblExactList, TblIns.exact, dsSA, dsT, pmTv, h, dsL, dsLV, pmVal, pmNV]
  · refine (TblDo.iteF (by simp [dsLV, h, pmNV, pmVal]) (TblDo.block _ _
      (by simp [tblFitsList, TblIns.fits]) ?_)).mono (fun _ h => h) (by norm_num)
    simp [tblExactList, TblIns.exact, dsSA, dsT, pmTv, h, dsL, dsLV, pmVal, pmNV]

theorem dsAxC_B (hn : 2 ≤ n) (hi : i < d n) :
    TblDo A (pmW n) w (tblBlock pmNV [.copy 2 36, .copy 31 39] (.inc 39)) ⟨dsSA n Wt i, []⟩
      (· = ⟨dsSB n Wt i, []⟩) 3 := by
  have hd := ds_d_lt hn
  refine TblDo.block _ _ ?_ ?_
  · simp [tblFitsList, TblIns.fits, TblIns.exact, dsSA, dsLV, pmNV]; omega
  · simp [tblExactList, TblIns.exact, dsSB, dsSA, dsLV, pmVal, pmNV]

@[simp] theorem dsSB_3 : dsSB n Wt i 3 = d n := by simp [dsSB, dsSA, dsLV, pmVal, pmNV]
@[simp] theorem dsSB_6 : dsSB n Wt i 6 = T n := by simp [dsSB, dsSA, dsLV, pmVal, pmNV]
@[simp] theorem dsSB_8 : dsSB n Wt i 8 = r n := by simp [dsSB, dsSA, dsLV, pmVal, pmNV]
@[simp] theorem dsSB_32 : dsSB n Wt i 32 = dsP n i := by simp [dsSB, dsSA, dsLV, pmVal, pmNV]
@[simp] theorem dsSB_33 : dsSB n Wt i 33 = dsT n i := by simp [dsSB, dsSA, dsLV, pmVal, pmNV]
@[simp] theorem dsSB_36 : dsSB n Wt i 36 = p n := by simp [dsSB, dsSA, dsLV, pmVal, pmNV]
@[simp] theorem dsSB_39 : dsSB n Wt i 39 = i + 1 := by simp [dsSB, dsSA, dsLV, pmVal, pmNV]

theorem dsAxC_C (hn : 2 ≤ n) (hi : i < d n) :
    TblDo A (pmW n) w (.ite 39 3 (tblBlock pmNV [.inc 36, .div 6 8 37, .mul 32 33 39]
      (.div 37 39 37)) (tblBlock pmNV [.zero 37] (.inc 37))) ⟨dsSB n Wt i, []⟩
      (fun s => s.acc = [] ∧ ∀ j, j ≠ 39 → s.val j = dsSC n Wt i j) 5 := by
  have hT := ds_T_lt hn
  have hPt : dsP n i * dsT n i ≤ T n := by
    rw [← dsP_succ]; exact dsP_le hn (by omega)
  by_cases h : i + 1 < d n
  · refine (TblDo.iteT (by simpa using h) (TblDo.block _ _ ?_ ?_)).mono
      (fun _ h => h) (by norm_num)
    · simp only [tblFitsList, TblIns.fits, TblIns.exact, List.cons_append, List.nil_append]
      refine ⟨?_, trivial, ?_, trivial, trivial⟩
      · rw [dsSB_36]; exact ds_small n (by unfold p; omega)
      · simp only [Function.update_apply]; simp; omega
    · refine ⟨rfl, fun j hj => ?_⟩
      simp only [tblExactList, TblIns.exact, List.cons_append, List.nil_append]
      rcases eq_or_ne j 37 with rfl | h37
      · simp [dsSC, dsG, h]
      rcases eq_or_ne j 36 with rfl | h36
      · simp [dsSC, dsQ, h]
      simp [dsSC, Function.update_of_ne h37, Function.update_of_ne h36, Function.update_of_ne hj]
  · refine (TblDo.iteF (by simpa using h) (TblDo.block _ _ ?_ ?_)).mono
      (fun _ h => h) (by norm_num)
    · simp only [tblFitsList, TblIns.fits, TblIns.exact, List.cons_append, List.nil_append]
      refine ⟨trivial, ?_, trivial⟩
      simp only [Function.update_self]
      exact Nat.one_lt_two_pow (by have := pmW_ge n; omega)
    · refine ⟨rfl, fun j hj => ?_⟩
      simp only [tblExactList, TblIns.exact, List.cons_append, List.nil_append]
      rcases eq_or_ne j 37 with rfl | h37
      · simp [dsSC, dsG, h]
      rcases eq_or_ne j 36 with rfl | h36
      · simp [dsSC, dsQ, h]
      simp [dsSC, Function.update_of_ne h37, Function.update_of_ne h36, Function.update_of_ne hj]

theorem dsAxC_D (hn : 2 ≤ n) (hi : i < d n) (s : TblSt pmNV A) (hacc : s.acc = [])
    (hs : ∀ j, j ≠ 39 → s.val j = dsSC n Wt i j) :
    TblDo A (pmW n) w (pmModC.rename ![16, 17, 11, 31, 35, 39] ;; .ins (.zero 39)) s
      (· = ⟨dsAV n Wt i, []⟩) 10 := by
  have hf : Function.Injective (![16, 17, 11, 31, 35, 39] : Fin 6 → Fin pmNV) := by decide
  have hB : pmModBound (N n) (pmX0 n) i < 2 ^ pmW n :=
    (pm_modBound_lt hn hi).trans_le (pm_two_pow_le (by have := pmW_ge n; omega))
  have hM := pmModC_do (A := A) (W := pmW n) (w := w) (N := N n) (x₀ := pmX0 n)
    (a := numHalf n) (i := i) (s.restrict ![16, 17, 11, 31, 35, 39])
    (by simp [hs, dsSC, dsSB, dsSA, dsLV, pmVal, pmNV])
    (by simp [hs, dsSC, dsSB, dsSA, dsLV, pmVal, pmNV])
    (by simp [hs, dsSC, dsSB, dsSA, dsLV, pmVal, pmNV])
    (by simp [hs, dsSC, dsSB, dsSA, dsLV, pmVal, pmNV]) (pm_one_le_N n) hB
  refine ((TblDo.rename hf hM).seq (K₂ := 1)
    (fun s₁ ⟨⟨hv, hfr, hac₁⟩, hout⟩ => TblDo.ins _ ?_)).mono (fun _ h => h) (by norm_num)
  simp only [TblIns.run]
  rw [dsAV_eq]
  simp only [TblSt.restrict_val, TblSt.restrict_acc] at hv hfr hac₁
  congr 1
  · funext j
    rcases eq_or_ne j 39 with rfl | h39
    · simp
    rw [Function.update_of_ne h39, Function.update_of_ne h39]
    rcases eq_or_ne j 35 with rfl | h35
    · simpa [dsS] using hv
    rw [Function.update_of_ne h35, ← hs j h39]
    by_cases hj : ∃ y, (![16, 17, 11, 31, 35, 39] : Fin 6 → Fin pmNV) y = j
    · obtain ⟨y, rfl⟩ := hj
      fin_cases y
      · simpa using hfr 0 (by decide) (by decide)
      · simpa using hfr 1 (by decide) (by decide)
      · simpa using hfr 2 (by decide) (by decide)
      · simpa using hfr 3 (by decide) (by decide)
      · exact absurd rfl h35
      · exact absurd rfl h39
    · push Not at hj
      exact hout j hj
  · rw [hac₁, hacc]

end Steps

/-- **The axis code**: from `dsLV n Wt i` to `dsAV n Wt i`, `21` atoms. -/
theorem dsAxC_do {n Wt i : ℕ} (hn : 2 ≤ n) (hi : i < d n) :
    TblDo A (pmW n) w dsAxC ⟨dsLV n Wt i, []⟩ (· = ⟨dsAV n Wt i, []⟩) 21 :=
  (dsAxC_A.seq fun _ hs => hs ▸ (dsAxC_B hn hi).seq fun _ hs => hs ▸ (dsAxC_C hn hi).seq
    fun s (h : s.acc = [] ∧ ∀ j, j ≠ 39 → s.val j = dsSC n Wt i j) =>
      dsAxC_D hn hi s h.1 h.2).mono (fun _ h => h) (by norm_num)

/-- **The update code**: from `dsAV n Wt i` to `dsLV n Wt (i + 1)`, `7` atoms. -/
theorem dsUpC_do {n Wt i : ℕ} (hn : 2 ≤ n) (hi : i < d n) :
    TblDo A (pmW n) w dsUpC ⟨dsAV n Wt i, []⟩ (· = ⟨dsLV n Wt (i + 1), []⟩) 7 := by
  have hT := ds_T_lt hn
  have hd := ds_d_lt hn
  have hPt : dsP n i * dsT n i ≤ T n := by
    rw [← dsP_succ]; exact dsP_le hn (by omega)
  refine TblDo.block _ _ ?_ ?_
  · simp [tblFitsList, TblIns.fits, TblIns.exact, dsAV, dsLV, pmNV]
    omega
  · simp only [tblExactList, TblIns.exact, List.cons_append, List.nil_append]
    congr 1
    funext j
    fin_cases j <;> simp [dsAV, dsLV, Function.update_apply, dsP_succ, Fin.ext_iff, pmNV]

end Code

/-! ### The loop -/

section Loop

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR pmNV → Fin T}

/-- One iteration: the axis code, the pushes `L`, the update code. -/
def dsAxBody (rg : TblR pmNV → Fin T) (L : List (Fin T × Fin pmNV × DsMode)) : Pr P T Q A U :=
  .seq (tblCompile rg dsAxC) (.seq (dsPush rg L) (tblCompile rg dsUpC))

/-- The axis loop: one iteration per symbol of `uD`, through the spare `tm`. -/
def dsAxes (rg : TblR pmNV → Fin T) (uD tm : Fin T) (L : List (Fin T × Fin pmNV × DsMode)) :
    Pr P T Q A U :=
  scanP uD tm (dsAxBody rg L)

/-- What register `k` gains in the first `j` iterations, the latest on top. -/
def dsAcc (n Wt : ℕ) (L : List (Fin T × Fin pmNV × DsMode)) (j : ℕ) (k : Fin T) :
    List (Fin (A + 4)) :=
  ((List.range j).reverse).flatMap fun i => dsOut (dsAV n Wt i) L k

/-- The step bound of iteration `i`. -/
def dsAxCost (n Wt : ℕ) (L : List (Fin T × Fin pmNV × DsMode)) (i : ℕ) : ℕ :=
  28 * tblC (pmW n) (pmW n) + dsPushCost (pmW n) (dsAV n Wt i) L

/-- The step bound of the loop. -/
def dsAxesCost (n Wt : ℕ) (L : List (Fin T × Fin pmNV × DsMode)) : ℕ :=
  ∑ i ∈ Finset.range (d n), (dsAxCost n Wt L i + 3) + 2 * d n + 4

theorem dsOut_none (val : Fin pmNV → ℕ) (L : List (Fin T × Fin pmNV × DsMode)) {k : Fin T}
    (hk : ∀ e ∈ L, e.1 ≠ k) : dsOut (A := A) val L k = [] := by
  unfold dsOut
  rw [List.filter_eq_nil_iff.2 (fun e he => by simpa using hk e he)]
  rfl

theorem dsAcc_zero (n Wt : ℕ) (L : List (Fin T × Fin pmNV × DsMode)) (k : Fin T) :
    dsAcc (A := A) n Wt L 0 k = [] := rfl

theorem dsAcc_succ (n Wt : ℕ) (L : List (Fin T × Fin pmNV × DsMode)) (j : ℕ) (k : Fin T) :
    dsAcc (A := A) n Wt L (j + 1) k = dsOut (dsAV n Wt j) L k ++ dsAcc n Wt L j k := by
  simp [dsAcc, List.range_succ, List.reverse_append]

theorem dsAcc_none (n Wt : ℕ) (L : List (Fin T × Fin pmNV × DsMode)) {k : Fin T}
    (hk : ∀ e ∈ L, e.1 ≠ k) (j : ℕ) : dsAcc (A := A) n Wt L j k = [] := by
  simp [dsAcc, dsOut_none _ L hk]

/-- The register file of the loop after `j` iterations. -/
noncomputable def dsPsi (rg : TblR pmNV → Fin T) (R : Regs T A) (n Wt : ℕ)
    (L : List (Fin T × Fin pmNV × DsMode)) (wl : List (Fin (A + 4))) (j : ℕ) : Regs T A :=
  dsOv rg (fun k => dsAcc n Wt L j k ++ R k) (tblRho (pmW n) wl wl ⟨dsLV n Wt j, []⟩)

variable (hrg : Function.Injective rg)
include hrg

/-- **One iteration** over any register file off the layout. -/
theorem ds_axBody {n Wt i : ℕ} (hn : 2 ≤ n) (hWt : Wt < 2 ^ pmW n) (hi : i < d n)
    (wl : List (Fin (A + 4))) (hwl : wl.length = pmW n) (L : List (Fin T × Fin pmNV × DsMode))
    (hL : ∀ e ∈ L, ∀ r, rg r ≠ e.1) (X : Regs T A) :
    dsRuns body (dsAxBody rg L) (dsOv rg X (tblRho (pmW n) wl wl ⟨dsLV n Wt i, []⟩))
      (dsOv rg (dsGain (dsAV n Wt i) L X) (tblRho (pmW n) wl wl ⟨dsLV n Wt (i + 1), []⟩))
      (dsAxCost n Wt L i) := by
  have h1 := ds_code (body := body) hrg wl wl hwl hwl le_rfl (dsAxC_do (A := A) (w := pmW n)
    (Wt := Wt) hn hi) (dsLV_lt hn hWt hi.le) X
  have h2 := ds_push (body := body) hrg (W := pmW n) wl wl ⟨dsAV n Wt i, []⟩ L hL
    (fun e _ => dsAV_lt hn hWt hi _) X
  have h3 := ds_code (body := body) hrg wl wl hwl hwl le_rfl (dsUpC_do (A := A) (w := pmW n)
    (Wt := Wt) hn hi) (dsAV_lt hn hWt hi) (dsGain (dsAV n Wt i) L X)
  refine (h1.seq (h2.seq h3)).mono ?_
  unfold dsAxCost
  dsimp only
  omega

/-- **The axis loop.** With `d` symbols on `uD`, the spare `tm` empty and the layout carrying
`dsLV n Wt 0`, the loop ends with the layout carrying `dsLV n Wt d` and every register `k` off
the layout with `dsAcc n Wt L d k` on top; `uD` and `tm` end as they started. -/
theorem ds_axes {uD tm : Fin T} (huD : ∀ r, rg r ≠ uD) (htm : ∀ r, rg r ≠ tm) (hut : uD ≠ tm)
    {n Wt : ℕ} (hn : 2 ≤ n) (hWt : Wt < 2 ^ pmW n) (wl : List (Fin (A + 4)))
    (hwl : wl.length = pmW n) (L : List (Fin T × Fin pmNV × DsMode))
    (hL : ∀ e ∈ L, ∀ r, rg r ≠ e.1) (hLu : ∀ e ∈ L, e.1 ≠ uD) (hLt : ∀ e ∈ L, e.1 ≠ tm)
    (R : Regs T A) (hRu : (R uD).length = d n) (hRt : R tm = []) :
    dsRuns body (dsAxes rg uD tm L) (dsOv rg R (tblRho (pmW n) wl wl ⟨dsLV n Wt 0, []⟩))
      (dsPsi rg R n Wt L wl (d n)) (dsAxesCost n Wt L) := by
  have hspec : IterSpec body (dsAxBody rg L) uD tm (dsPsi rg R n Wt L wl)
      (fun j => dsAxCost n Wt L j) (d n) := by
    intro j hj v S hS
    have hX : S.R = dsOv rg S.R (tblRho (pmW n) wl wl ⟨dsLV n Wt j, []⟩) :=
      dsOv_eq_of hrg (fun r => by rw [hS (rg r) (huD r) (htm r), dsPsi, dsOv_rg hrg])
        (fun _ _ => rfl)
    obtain ⟨v', m, hu, hm, he⟩ := ds_axBody (body := body) hrg hn hWt hj wl hwl L hL S.R v S hX
    refine ⟨v', _, m, hu, hm, he, ?_, ?_, fun k hku hkt => ?_⟩
    · rw [dsOv_off _ _ huD, dsGain_eq, dsOut_none _ L hLu, List.nil_append]
    · rw [dsOv_off _ _ htm, dsGain_eq, dsOut_none _ L hLt, List.nil_append]
    · by_cases hk : ∃ r, rg r = k
      · obtain ⟨r, rfl⟩ := hk
        rw [dsOv_rg hrg, dsPsi, dsOv_rg hrg]
      · push Not at hk
        rw [dsOv_off _ _ hk, dsGain_eq, hS k hku hkt, dsPsi, dsPsi, dsOv_off _ _ hk,
          dsOv_off _ _ hk, dsAcc_succ, List.append_assoc]
  intro v S hS
  obtain ⟨v', R', m, hu, hm, he, hRu', hRt', hR'⟩ := scanP_exec body hut hspec 0 v S
    (by rw [hS, dsOv_off _ _ huD, hRu, Nat.zero_add])
    (fun k _ _ => by rw [hS, dsPsi]; simp [dsAcc_zero])
  refine ⟨v', m, hu, ?_, ?_⟩
  · rw [hS, dsOv_off _ _ huD, dsOv_off _ _ htm, hRu, hRt] at hm
    unfold dsAxesCost
    simpa using hm
  · have e : R' = dsPsi rg R n Wt L wl (d n) := by
      funext k
      by_cases hku : k = uD
      · subst hku
        rw [hRu', hS, dsOv_off _ _ htm, hRt, List.reverse_nil, List.nil_append, dsOv_off _ _ huD,
          dsPsi, dsOv_off _ _ huD, dsAcc_none n Wt L hLu, List.nil_append]
      by_cases hkt : k = tm
      · subst hkt
        rw [hRt', dsPsi, dsOv_off _ _ htm, dsAcc_none n Wt L hLt, List.nil_append, hRt]
      rw [hR' k hku hkt, Nat.zero_add, hS, dsOv_off _ _ huD, hRu]
    rw [e] at he
    exact he

end Loop

end IntegerMultBounds.MathlibTM2.Fast.TableVM
