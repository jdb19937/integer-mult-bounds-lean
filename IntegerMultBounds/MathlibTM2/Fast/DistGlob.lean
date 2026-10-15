module

public import IntegerMultBounds.MathlibTM2.Fast.DistAxis

/-!
# The global values of the distribution machine

Single values computed on the parameter layout and pushed in unary (or, for the word `E`, in
binary), between the steps the variables are `dsV1 n Wt w`: the parameters in `0 … 30`, the
table word size `Wt` in `38`, the coefficient width `w` in `39`, `0` in the scratch `31 … 37`.

* `dsStep rg c o` (`ds_step`): the table code `c` computes a value `x` into `31` (`DsPost`:
  nothing outside the scratch changes), `o` gains `x` ticks, the scratch is cleared (`dsZC`).
* The codes (`dsCN_do`, …): `N = logT - ℓ` (`Σ aᵢ`, the address bits of the synthetic
  transform), `D = d - 1`, `B = r w` (the record length of the layout stage), the layout word
  size `W_L = N² + N + r w + 4` (`dsWL`), `topN w = 2 ^ size (2 w)` (`dsCTop_do`: doubling while
  below `2 w + 1`), and the long-axis word `E = 2^(d-1) - 2^numHalf` (`dsCE_do`).
* `dsStepE rg oE oWL` (`ds_stepE`): `E` copied onto the empty `oE` and widened to the length of
  `oWL` (`bwiden`): `oE` ends holding `binSyms W_L E`.
* `dsLoad rg u x` (`ds_load`): variable `x` becomes the length of the unary register `u`
  (`toBinary`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Moduli

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-! ### States -/

section States

/-- The variables of the second phase: the parameters, `Wt` in `38`, `w` in `39`. -/
def dsV1 (n Wt w : ℕ) (j : Fin pmNV) : ℕ :=
  if j.val < 31 then pmVal n j else if j.val = 38 then Wt else if j.val = 39 then w else 0

/-- The layout word size `W_L = r w + N² + N + 4`, `N = logT - ℓ`. -/
def dsWL (n w : ℕ) : ℕ := r n * w + ((logT n - ℓ n) ^ 2 + (logT n - ℓ n) + 4)

/-- The word of the long axes: bit `i` set for `numHalf ≤ i < d - 1`. -/
def dsE (n : ℕ) : ℕ := 2 ^ (d n - 1) - 2 ^ numHalf n

/-- `topN w = 2 ^ size (2 w)`. -/
def dsTopN (w : ℕ) : ℕ := 2 ^ Nat.size (2 * w)

theorem dsV1_scr (n Wt w : ℕ) (j : Fin pmNV) (h1 : 31 ≤ j.val) (h2 : j.val < 38) :
    dsV1 n Wt w j = 0 := by
  unfold dsV1; split_ifs <;> omega

theorem dsV1_lt {n Wt w : ℕ} (hn : 2 ≤ n) (hWt : Wt < 2 ^ pmW n) (hw : w < 2 ^ pmW n)
    (j : Fin pmNV) : dsV1 n Wt w j < 2 ^ pmW n := by
  unfold dsV1
  split_ifs
  · exact ds_pmVal_lt hn j
  · exact hWt
  · exact hw
  · exact Nat.two_pow_pos _

theorem dsV1_pm (n : ℕ) : dsV1 n 0 0 = pmVals n := by
  funext j
  unfold dsV1 pmVals
  split_ifs with h1 h2 h3
  · rfl
  · rw [pmVal_ge n j (by omega)]
  · rw [pmVal_ge n j (by omega)]
  · rw [pmVal_ge n j (by omega)]

theorem dsV1_upd38 (n Wt w : ℕ) : Function.update (dsV1 n 0 w) 38 Wt = dsV1 n Wt w := by
  funext j
  fin_cases j <;> simp [dsV1, Fin.ext_iff, pmNV]

theorem dsV1_upd39 (n Wt w : ℕ) : Function.update (dsV1 n Wt 0) 39 w = dsV1 n Wt w := by
  funext j
  fin_cases j <;> simp [dsV1, Fin.ext_iff, pmNV]

theorem dsLV_zero (n Wt : ℕ) : dsLV n Wt 0 = Function.update (dsV1 n Wt 0) 32 1 := by
  funext j
  fin_cases j <;> simp [dsV1, dsLV, dsP_zero, Fin.ext_iff, pmNV]

theorem dsLV_end (n Wt : ℕ) :
    Function.update (Function.update (dsLV n Wt (d n)) 31 0) 32 0 = dsV1 n Wt 0 := by
  funext j
  fin_cases j <;> simp [dsV1, dsLV, Fin.ext_iff, pmNV]

theorem dsV1_fin (n Wt w : ℕ) :
    Function.update (Function.update (dsV1 n Wt w) 38 0) 39 0 = pmVals n := by
  rw [← dsV1_pm]
  funext j
  fin_cases j <;> simp [dsV1, Fin.ext_iff, pmNV]

/-- Off the scratch variables. -/
theorem ds_off_scr {j k : Fin pmNV} (hj : j.val < 31 ∨ 38 ≤ j.val) (h1 : 31 ≤ k.val)
    (h2 : k.val < 38) : j ≠ k := by
  rintro rfl; omega

theorem ds_upd_off {j k : Fin pmNV} (hj : j.val < 31 ∨ 38 ≤ j.val) (h1 : 31 ≤ k.val)
    (h2 : k.val < 38) (f : Fin pmNV → ℕ) (v : ℕ) : Function.update f k v j = f j :=
  Function.update_of_ne (ds_off_scr hj h1 h2) _ _

end States

/-! ### Clearing the scratch -/

section Clear

variable {A W w : ℕ}

/-- Clear the scratch variables `31 … 37`. -/
def dsZC : TblCode pmNV :=
  tblBlock pmNV [.zero 31, .zero 32, .zero 33, .zero 34, .zero 35, .zero 36] (.zero 37)

/-- The post-condition of the code of a step: `31` holds `x`, `acc` is empty, nothing outside
the scratch changes. -/
def DsPost (σ : Fin pmNV → ℕ) (x : ℕ) (s : TblSt pmNV A) : Prop :=
  s.acc = [] ∧ s.val 31 = x ∧ ∀ j : Fin pmNV, (j.val < 31 ∨ 38 ≤ j.val) → s.val j = σ j

theorem dsZC_do (σ : Fin pmNV → ℕ) (hσ : ∀ j : Fin pmNV, 31 ≤ j.val → j.val < 38 → σ j = 0)
    (s : TblSt pmNV A) (hacc : s.acc = [])
    (hs : ∀ j : Fin pmNV, (j.val < 31 ∨ 38 ≤ j.val) → s.val j = σ j) :
    TblDo A W w dsZC s (· = ⟨σ, []⟩) 7 := by
  refine TblDo.block _ _ (by simp [tblFitsList, TblIns.fits]) ?_
  simp only [tblExactList, TblIns.exact, List.cons_append, List.nil_append]
  rw [hacc]
  congr 1
  funext j
  by_cases hj : j.val < 31 ∨ 38 ≤ j.val
  · simp only [ds_upd_off hj (k := 37) (by decide) (by decide),
      ds_upd_off hj (k := 36) (by decide) (by decide), ds_upd_off hj (k := 35) (by decide) (by decide),
      ds_upd_off hj (k := 34) (by decide) (by decide), ds_upd_off hj (k := 33) (by decide) (by decide),
      ds_upd_off hj (k := 32) (by decide) (by decide), ds_upd_off hj (k := 31) (by decide) (by decide)]
    exact hs j hj
  · rw [hσ j (by omega) (by omega)]
    have : j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨ j = 35 ∨ j = 36 ∨ j = 37 := by
      simp only [Fin.ext_iff]; simp [pmNV]; omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end Clear

/-! ### A step -/

section Step

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR pmNV → Fin T}

/-- Compute into `31` with `c`, push its value onto `o`, clear the scratch. -/
def dsStep (rg : TblR pmNV → Fin T) (c : TblCode pmNV) (o : Fin T) : Pr P T Q A U :=
  .seq (tblCompile rg c) (.seq (dsUn rg 31 o) (tblCompile rg dsZC))

/-- The step bound of `dsStep` for `K` atoms and the value `x`. -/
def dsStepCost (W K x : ℕ) : ℕ := (K + 7) * tblC W W + (W * (4 * x + 11) + 2 * x + 6)

variable (hrg : Function.Injective rg)
include hrg

/-- **A step**: `o` gains `x` ticks; the layout ends as it started. -/
theorem ds_step {o : Fin T} (ho : ∀ r, rg r ≠ o) {W : ℕ} (wl : List (Fin (A + 4)))
    (hwl : wl.length = W) {c : TblCode pmNV} {σ : Fin pmNV → ℕ} {x K : ℕ}
    (hc : TblDo A W W c ⟨σ, []⟩ (DsPost σ x) K)
    (hσ0 : ∀ j : Fin pmNV, 31 ≤ j.val → j.val < 38 → σ j = 0) (hσ : ∀ j, σ j < 2 ^ W)
    (R : Regs T A) :
    dsRuns body (dsStep rg c o) (dsOv rg R (tblRho W wl wl ⟨σ, []⟩))
      (dsOv rg (Function.update R o (List.replicate x tick ++ R o)) (tblRho W wl wl ⟨σ, []⟩))
      (dsStepCost W K x) := by
  obtain ⟨st', k, hb, hp, hk⟩ := hc
  have hlt := hb.lt hσ
  have h1 := ds_tbl (body := body) hrg ((tblCompile_runs hrg wl wl hwl hwl le_rfl hb hσ).mono
    (Nat.mul_le_mul_right _ hk)) R
  have h2 := ds_un (body := body) hrg ho wl wl st' 31 (hlt 31) R
  rw [hp.2.1] at h2
  have h3 := ds_code (body := body) hrg wl wl hwl hwl le_rfl
    (dsZC_do (A := A) (W := W) (w := W) σ hσ0 st' hp.1 hp.2.2) hlt
    (Function.update R o (List.replicate x tick ++ R o))
  refine (h1.seq (h2.seq h3)).mono ?_
  unfold dsStepCost
  nlinarith

/-- Load the length of the unary register `u` into variable `x`. -/
def dsLoad (rg : TblR pmNV → Fin T) (u : Fin T) (x : Fin pmNV) : Pr P T Q A U :=
  .seq (bclear (rg (.v x))) (toBinary u (rg .wr) (rg (.v x)) (rg (.z 0)) (rg (.z 1)) (rg (.z 10)))

/-- **Loading**: variable `x` becomes `|u|`. -/
theorem ds_load {u : Fin T} (hu : ∀ r, rg r ≠ u) {W : ℕ} (wl : List (Fin (A + 4)))
    (hwl : wl.length = W) (σ : Fin pmNV → ℕ) (x : Fin pmNV) (R : Regs T A) :
    dsRuns body (dsLoad rg u x) (dsOv rg R (tblRho W wl wl ⟨σ, []⟩))
      (dsOv rg R (tblRho W wl wl ⟨Function.update σ x (R u).length, []⟩))
      (2 * W + 2 + ((R u).length * (4 * W + 10) + 4 * W + 8)) := by
  intro v S hS
  obtain ⟨v₁, hu₁, -, he₁⟩ := bclear_exec body (rg (.v x)) v S
  have hreg : [u, rg .wr, rg (.v x), rg (.z 0), rg (.z 1)].Nodup := by
    have h4 := tbl_nodup hrg (l := [.wr, .v x, .z 0, .z 1]) (by simp)
    simp only [List.map_cons, List.map_nil] at h4
    have hu' : u ∉ [rg .wr, rg (.v x), rg (.z 0), rg (.z 1)] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => hu _ h.symm, fun h => hu _ h.symm, fun h => hu _ h.symm,
        fun h => hu _ h.symm⟩
    exact List.nodup_cons.2 ⟨hu', h4⟩
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := toBinary_exec body hreg (rg (.z 10)) v₁
    { S with R := Function.update S.R (rg (.v x)) [] } (by simp)
    (by simp [Function.update_of_ne (hrg.ne (show (TblR.z 0 : TblR pmNV) ≠ .v x by simp)), hS,
      dsOv_rg hrg])
    (by simp [Function.update_of_ne (hrg.ne (show (TblR.z 1 : TblR pmNV) ≠ .v x by simp)), hS,
      dsOv_rg hrg])
  dsimp only at he₂ hm₂
  have e : Function.update (Function.update S.R (rg (.v x)) []) (rg (.v x))
      (binSyms ((Function.update S.R (rg (.v x)) []) (rg .wr)).length
        ((Function.update S.R (rg (.v x)) []) u).length) =
      dsOv rg R (tblRho W wl wl ⟨Function.update σ x (R u).length, []⟩) := by
    simp only [Function.update_idem]
    refine dsOv_eq_of hrg (fun r => ?_) (fun k hk => ?_)
    · by_cases hr : r = .v x
      · subst hr
        rw [Function.update_self, Function.update_of_ne (hrg.ne (by simp)),
          Function.update_of_ne (Ne.symm (hu _)), hS, dsOv_rg hrg, dsOv_off _ _ hu]
        simp [hwl]
      · rw [Function.update_of_ne (hrg.ne hr), hS, dsOv_rg hrg]
        cases r with
        | v i =>
          have hi : i ≠ x := fun h => hr (by rw [h])
          simp [Function.update_of_ne hi]
        | _ => rfl
    · rw [Function.update_of_ne (Ne.symm (hk _)), hS, dsOv_off _ _ hk]
  rw [e] at he₂
  refine ⟨v₂, _, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂⟩
  have e1 : (S.R (rg (.v x))).length = W := by rw [hS, dsOv_rg hrg]; simp
  have e2 : ((Function.update S.R (rg (.v x)) []) u).length = (R u).length := by
    rw [Function.update_of_ne (Ne.symm (hu _)), hS, dsOv_off _ _ hu]
  have e3 : ((Function.update S.R (rg (.v x)) []) (rg .wr)).length = W := by
    rw [Function.update_of_ne (hrg.ne (by simp)), hS, dsOv_rg hrg]; simp [hwl]
  rw [e1]; rw [e2, e3] at hm₂; omega

end Step

/-! ### The codes -/

section Codes

variable {A w' : ℕ} {n Wt w : ℕ}

/-- `31 := logT - ℓ`. -/
def dsCN : TblCode pmNV := .ins (.sub 5 7 31)

/-- `31 := d - 1`. -/
def dsCD : TblCode pmNV := tblBlock pmNV [.zero 32, .inc 32] (.sub 3 32 31)

/-- `31 := N² + N + 4`, `N = logT - ℓ`. -/
def dsCWL : TblCode pmNV :=
  tblBlock pmNV [.sub 5 7 32, .mul 32 32 33, .add 33 32 31, .inc 31, .inc 31, .inc 31] (.inc 31)

/-- `31 := 2 ^ size (2 w)`: `31 := 1`, doubled while below `2 w + 1`. -/
def dsCTop : TblCode pmNV :=
  tblBlock pmNV [.add 39 39 32, .copy 32 33, .inc 33, .zero 31] (.inc 31) ;;
    .loop 31 33 (.ins (.add 31 31 31))

/-- `31 := 2^(d-1) - 2^numHalf`. -/
def dsCE : TblCode pmNV :=
  tblBlock pmNV [.zero 32, .inc 32] (.sub 3 32 33) ;; tblPow2 34 33 35 ;; tblPow2 36 11 35 ;;
    .ins (.sub 34 36 31)

theorem dsCN_do (hn : 2 ≤ n) :
    TblDo A (pmW n) w' dsCN ⟨dsV1 n Wt w, []⟩ (DsPost (dsV1 n Wt w) (logT n - ℓ n)) 1 := by
  have h1 := pm_ℓ_le_logT hn
  have h2 := ds_pmVal_lt hn 5
  refine TblDo.insX _ ?_ ⟨rfl, ?_, fun j hj => ?_⟩
  · simp [TblIns.fits, dsV1, pmNV]; exact ⟨h1, h2⟩
  · simp [TblIns.exact, dsV1, pmNV, pmVal]
  · simp [TblIns.exact, ds_upd_off hj (k := 31) (by decide) (by decide)]

theorem dsCD_do (hn : 2 ≤ n) :
    TblDo A (pmW n) w' dsCD ⟨dsV1 n Wt w, []⟩ (DsPost (dsV1 n Wt w) (d n - 1)) 3 := by
  have h1 := one_le_d hn
  have h2 := ds_pmVal_lt hn 3
  have h3 : 1 < 2 ^ pmW n := Nat.one_lt_two_pow (by have := pmW_ge n; omega)
  refine TblDo.block _ _ ?_ ⟨rfl, ?_, fun j hj => ?_⟩
  · simp [tblFitsList, TblIns.fits, TblIns.exact, dsV1, pmNV, pmVal]
    exact ⟨by have := pmW_ge n; omega, h1, h2⟩
  · simp [tblExactList, TblIns.exact, dsV1, pmNV, pmVal]
  · simp [tblExactList, TblIns.exact, ds_upd_off hj (k := 31) (by decide) (by decide),
      ds_upd_off hj (k := 32) (by decide) (by decide)]

/-- Values quadratic in `b` fit the words of the parameter machine. -/
theorem ds_small2 (n : ℕ) {x : ℕ} (hx : x ≤ 100 * (b n + 1) ^ 2) : x < 2 ^ pmW n := by
  have h1 : b n + 1 ≤ 2 ^ b n := Nat.lt_two_pow_self
  have h2 : (b n + 1) ^ 2 ≤ (2 ^ b n) ^ 2 := Nat.pow_le_pow_left h1 2
  have h3 : 2 ^ (2 * b n + 7) ≤ 2 ^ pmW n := pm_two_pow_le (by have := pmW_ge n; omega)
  have e : 2 ^ (2 * b n + 7) = 128 * (2 ^ b n) ^ 2 := by
    rw [pow_add, ← pow_mul, mul_comm (b n) 2]; ring
  have h4 : 1 ≤ (b n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

theorem dsCWL_do (hn : 2 ≤ n) :
    TblDo A (pmW n) w' dsCWL ⟨dsV1 n Wt w, []⟩
      (DsPost (dsV1 n Wt w) ((logT n - ℓ n) ^ 2 + (logT n - ℓ n) + 4)) 7 := by
  have h1 := pm_ℓ_le_logT hn
  have h2 := ds_pmVal_lt hn 5
  have hL := pm_logT_le hn
  obtain ⟨N, hN⟩ : ∃ N, logT n - ℓ n = N := ⟨_, rfl⟩
  have hNb : N ≤ b n + 2 := by omega
  have hsq : N ^ 2 + N + 4 < 2 ^ pmW n := ds_small2 n (by nlinarith)
  have hNN : N ≤ N ^ 2 := Nat.le_self_pow (by norm_num) N
  refine TblDo.block _ _ ?_ ⟨rfl, ?_, fun j hj => ?_⟩
  · simp [tblFitsList, TblIns.fits, TblIns.exact, dsV1, pmNV, pmVal]
    simp only [hN]
    refine ⟨⟨h1, h2⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith
  · simp [tblExactList, TblIns.exact, dsV1, pmNV, pmVal]
    simp only [hN]; ring
  · simp [tblExactList, TblIns.exact, ds_upd_off hj (k := 31) (by decide) (by decide),
      ds_upd_off hj (k := 32) (by decide) (by decide), ds_upd_off hj (k := 33) (by decide) (by decide)]

/-- The atoms of `dsCTop`. -/
def dsTopK (w : ℕ) : ℕ := 3 * Nat.size (2 * w) + 7

theorem dsCTop_do (hw : 4 * w + 2 < 2 ^ pmW n) :
    TblDo A (pmW n) w' dsCTop ⟨dsV1 n Wt w, []⟩ (DsPost (dsV1 n Wt w) (dsTopN w)) (dsTopK w) := by
  set σ := dsV1 n Wt w with hσ
  set s0 : Fin pmNV → ℕ := Function.update (Function.update (Function.update (Function.update
    (Function.update σ 32 (w + w)) 33 (w + w)) 33 (w + w + 1)) 31 0) 31 1 with hs0
  have hB : TblDo A (pmW n) w' (tblBlock pmNV [.add 39 39 32, .copy 32 33, .inc 33, .zero 31]
      (.inc 31)) ⟨σ, []⟩ (· = ⟨s0, []⟩) 5 := by
    refine TblDo.block _ _ ?_ ?_
    · simp [tblFitsList, TblIns.fits, TblIns.exact, σ, dsV1, pmNV]
      exact ⟨by omega, by omega, by have := pmW_ge n; omega⟩
    · simp [tblExactList, TblIns.exact, s0, σ, dsV1, pmNV]
  set N := Nat.size (2 * w) with hN
  let Inv : ℕ → TblSt pmNV A → Prop := fun j s => s.acc = [] ∧ s.val 31 = 2 ^ j ∧
    s.val 33 = 2 * w + 1 ∧ ∀ k : Fin pmNV, (k.val < 31 ∨ 38 ≤ k.val) → s.val k = σ k
  have hL : TblDo A (pmW n) w' (.loop 31 33 (.ins (.add 31 31 31))) ⟨s0, []⟩
      (DsPost σ (dsTopN w)) (N * (1 + 2) + 2) := by
    refine TblDo.loop Inv N 1 ⟨rfl, by simp [s0], by simp [s0]; omega, fun k hk => ?_⟩ ?_ ?_
    · simp [s0, ds_upd_off hk (k := 31) (by decide) (by decide),
        ds_upd_off hk (k := 32) (by decide) (by decide), ds_upd_off hk (k := 33) (by decide) (by decide)]
    · intro j hj s ⟨h1, h2, h3, h4⟩
      have hp : 2 ^ j ≤ 2 * w := Nat.lt_size.1 hj
      refine ⟨by rw [h2, h3]; omega, TblDo.ins _ ⟨by simp [TblIns.run, h1], ?_, ?_, fun k hk => ?_⟩⟩
      · simp only [TblIns.run, Function.update_self, h2]
        rw [← two_mul, ← pow_succ', Nat.mod_eq_of_lt (by rw [pow_succ']; omega)]
      · simp [TblIns.run, h3]
      · simp [TblIns.run, ds_upd_off hk (k := 31) (by decide) (by decide), h4 k hk]
    · intro s ⟨h1, h2, h3, h4⟩
      refine ⟨?_, h1, by rw [h2]; rfl, h4⟩
      have : 2 * w < 2 ^ N := Nat.lt_size_self _
      rw [h2, h3]; omega
  refine (hB.seq fun s hs => hs ▸ hL).mono (fun _ h => h) ?_
  unfold dsTopK; omega

/-- The atoms of `dsCE`. -/
def dsEK (n : ℕ) : ℕ := 4 * (d n - 1) + 4 * numHalf n + 14

theorem dsCE_do (hn : 2 ≤ n) :
    TblDo A (pmW n) w' dsCE ⟨dsV1 n Wt w, []⟩ (DsPost (dsV1 n Wt w) (dsE n)) (dsEK n) := by
  set σ := dsV1 n Wt w with hσ
  have hd1 := one_le_d hn
  have hh := numHalf_lt hd1
  have hdb := d_le_b n
  have hdW : d n - 1 < pmW n := by have := pmW_ge n; omega
  have h2d : 2 ^ (d n - 1) < 2 ^ pmW n := Nat.pow_lt_pow_right (by norm_num) hdW
  have hB : TblDo A (pmW n) w' (tblBlock pmNV [.zero 32, .inc 32] (.sub 3 32 33)) ⟨σ, []⟩
      (fun s => s.acc = [] ∧ s.val 33 = d n - 1 ∧ s.val 11 = numHalf n ∧
        ∀ k : Fin pmNV, (k.val < 31 ∨ 38 ≤ k.val) → s.val k = σ k) 3 := by
    refine TblDo.block _ _ ?_ ⟨rfl, ?_, ?_, fun k hk => ?_⟩
    · simp [tblFitsList, TblIns.fits, TblIns.exact, σ, dsV1, pmNV, pmVal]
      exact ⟨by have := pmW_ge n; omega, hd1, ds_d_lt hn⟩
    · simp [tblExactList, TblIns.exact, σ, dsV1, pmNV, pmVal]
    · simp [tblExactList, TblIns.exact, σ, dsV1, pmNV, pmVal]
    · simp [tblExactList, TblIns.exact, ds_upd_off hk (k := 32) (by decide) (by decide),
        ds_upd_off hk (k := 33) (by decide) (by decide)]
  refine (hB.seq (K₂ := 4 * (d n - 1) + 5 + (4 * numHalf n + 5 + 1)) fun s ⟨h1, h2, h3, h4⟩ =>
    ((tblPow2_do (A := A) (W := pmW n) (w := w') (c := 34) (e := 33) (i := 35) (by decide)
      (by decide) (by decide) s (by rw [h2]; exact hdW)).seq
      (K₂ := 4 * numHalf n + 5 + 1) fun s' ⟨g1, g2, g3, g4⟩ =>
      ((tblPow2_do (A := A) (W := pmW n) (w := w') (c := 36) (e := 11) (i := 35) (by decide)
        (by decide) (by decide) s' (by rw [g3 11 (by decide) (by decide), h3]; omega)).seq
        (K₂ := 1) fun s'' ⟨f1, f2, f3, f4⟩ => ?_).mono (fun _ h => h)
          (by rw [g3 11 (by decide) (by decide), h3])).mono (fun _ h => h) (by rw [h2])).mono
    (fun _ h => h) (by unfold dsEK; omega)
  have e34 : s''.val 34 = 2 ^ (d n - 1) := by rw [f3 34 (by decide) (by decide), g1, h2]
  have e36 : s''.val 36 = 2 ^ numHalf n := by rw [f1, g3 11 (by decide) (by decide), h3]
  have hle : 2 ^ numHalf n ≤ 2 ^ (d n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine TblDo.insX _ ⟨by rw [e34, e36]; exact hle, by rw [e34]; exact h2d⟩
    ⟨by simp [TblIns.exact, f4, g4, h1], by simp [TblIns.exact, e34, e36, dsE], fun k hk => ?_⟩
  simp only [TblIns.exact, ds_upd_off hk (k := 31) (by decide) (by decide)]
  rw [f3 k (ds_off_scr hk (by decide) (by decide)) (ds_off_scr hk (by decide) (by decide)),
    g3 k (ds_off_scr hk (by decide) (by decide)) (ds_off_scr hk (by decide) (by decide)), h4 k hk]

end Codes

/-! ### Unary copies and products -/

section Unary

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- `ucopy`: `b` gains `|a|` ticks. -/
theorem ds_ucopy {a b t : Fin T} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (R : Regs T A)
    (ht : R t = []) :
    dsRuns body (ucopy a b t) R (Function.update R b (List.replicate (R a).length tick ++ R b))
      (4 * (R a).length + 4) := by
  intro v S hS
  obtain ⟨v', hu, he⟩ := ucopy_exec body hab hat hbt v S (by rw [hS, ht])
  rw [hS] at he
  exact ⟨v', _, hu, le_rfl, he⟩

/-- Unary product: `c` gains `|a| · |b|` ticks; `a` kept through `t₁`, `b` copied through
`t₂`. -/
def dsUMul (a b c t₁ t₂ : Fin T) : Pr P T Q A U := scanP a t₁ (ucopy b c t₂)

/-- **Unary product.** -/
theorem ds_umul {a b c t₁ t₂ : Fin T} (hreg : [a, b, c, t₁, t₂].Nodup) (R : Regs T A)
    (ht₁ : R t₁ = []) (ht₂ : R t₂ = []) :
    dsRuns body (dsUMul a b c t₁ t₂) R
      (Function.update R c (List.replicate ((R a).length * (R b).length) tick ++ R c))
      ((R a).length * (4 * (R b).length + 7) + 2 * (R a).length + 4) := by
  have hreg' := hreg
  regs_ne hreg'
  have hab : a ≠ b := ‹_›
  have hac : a ≠ c := ‹_›
  have hat₁ : a ≠ t₁ := ‹_›
  have hat₂ : a ≠ t₂ := ‹_›
  have hbc : b ≠ c := ‹_›
  have hbt₁ : b ≠ t₁ := ‹_›
  have hbt₂ : b ≠ t₂ := ‹_›
  have hct₁ : c ≠ t₁ := ‹_›
  have hct₂ : c ≠ t₂ := ‹_›
  have ht₁t₂ : t₁ ≠ t₂ := ‹_›
  set Ψ : ℕ → Regs T A := fun j =>
    Function.update R c (List.replicate (j * (R b).length) tick ++ R c) with hΨ
  have hspec : IterSpec body (ucopy b c t₂) a t₁ Ψ (fun _ => 4 * (R b).length + 4)
      (R a).length := by
    intro j _ v S hS
    have hb : S.R b = R b := by rw [hS b hab.symm hbt₁, hΨ]; simp [Function.update_of_ne hbc]
    obtain ⟨v', hu, he⟩ := ucopy_exec body hbc hbt₂ hct₂ v S
      (by rw [hS t₂ (Ne.symm hat₂) (Ne.symm ht₁t₂), hΨ]; simp [Function.update_of_ne (Ne.symm hct₂), ht₂])
    refine ⟨v', _, _, hu, by rw [hb], he, ?_, ?_, fun k hka hkt => ?_⟩
    · simp [Function.update_of_ne hac]
    · simp [Function.update_of_ne (Ne.symm hct₁)]
    · by_cases hkc : k = c
      · subst hkc
        rw [Function.update_self, hb, hS k hka hkt, hΨ]
        simp only [Function.update_self, ← List.append_assoc, List.replicate_append_replicate]
        congr 2; ring
      · rw [Function.update_of_ne hkc, hS k hka hkt, hΨ]
        simp [Function.update_of_ne hkc]
  intro v S hS
  obtain ⟨v', R', m, hu, hm, he, hRa, hRt, hR'⟩ := scanP_exec body hat₁ hspec 0 v S
    (by rw [hS]; omega) (fun k _ _ => by rw [hS, hΨ]; simp)
  refine ⟨v', m, hu, ?_, ?_⟩
  · rw [hS, ht₁] at hm
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.zero_add] at hm
    simp only [List.length_nil] at hm
    nlinarith
  · have e : R' = Function.update R c (List.replicate ((R a).length * (R b).length) tick ++ R c) := by
      funext k
      by_cases hka : k = a
      · subst hka; rw [hRa, hS, ht₁]; simp [Function.update_of_ne hac]
      by_cases hkt : k = t₁
      · subst hkt; rw [hRt]; simp [Function.update_of_ne (Ne.symm hct₁), ht₁]
      rw [hR' k hka hkt, hS, Nat.zero_add]
    rw [← e]; exact he

end Unary

/-! ### The binary step -/

section StepB

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR pmNV → Fin T}

/-- Compute into `31` with `c`, copy it onto `oE` and widen it to the length of `oWL`, clear the
scratch. -/
def dsStepB (rg : TblR pmNV → Fin T) (c : TblCode pmNV) (oE oWL : Fin T) : Pr P T Q A U :=
  .seq (tblCompile rg c) (.seq (bcopy (rg (.v 31)) oE (rg (.z 0)) (rg (.z 1)))
    (.seq (bwiden oE oWL (rg (.z 0)) (rg (.z 1)) (rg (.z 2))) (tblCompile rg dsZC)))

/-- The step bound of `dsStepB`. -/
def dsStepBCost (W K WL : ℕ) : ℕ := (K + 7) * tblC W W + 6 * W + 12 * WL + 24

variable (hrg : Function.Injective rg)
include hrg

/-- **The binary step**: the empty `oE` ends holding `binSyms |oWL| x`. -/
theorem ds_stepB {oE oWL : Fin T} (hoE : ∀ r, rg r ≠ oE) (hoW : ∀ r, rg r ≠ oWL)
    (hEW : oE ≠ oWL) {W : ℕ} (wl : List (Fin (A + 4))) (hwl : wl.length = W) {c : TblCode pmNV}
    {σ : Fin pmNV → ℕ} {x K : ℕ} (hc : TblDo A W W c ⟨σ, []⟩ (DsPost σ x) K)
    (hσ0 : ∀ j : Fin pmNV, 31 ≤ j.val → j.val < 38 → σ j = 0) (hσ : ∀ j, σ j < 2 ^ W)
    {WL : ℕ} (hWWL : W ≤ WL) (R : Regs T A) (hRE : R oE = []) (hRW : (R oWL).length = WL) :
    dsRuns body (dsStepB rg c oE oWL) (dsOv rg R (tblRho W wl wl ⟨σ, []⟩))
      (dsOv rg (Function.update R oE (binSyms WL x)) (tblRho W wl wl ⟨σ, []⟩))
      (dsStepBCost W K WL) := by
  obtain ⟨st', k, hb, hp, hk⟩ := hc
  have hlt := hb.lt hσ
  have h1 := ds_tbl (body := body) hrg ((tblCompile_runs hrg wl wl hwl hwl le_rfl hb hσ).mono
    (Nat.mul_le_mul_right _ hk)) R
  have hz : ∀ j : Fin 12, (rg (.z j)) ≠ oE := fun j => hoE _
  have h2 : dsRuns body (bcopy (rg (.v 31)) oE (rg (.z 0)) (rg (.z 1)))
      (dsOv rg R (tblRho W wl wl st'))
      (dsOv rg (Function.update R oE (binSyms W x)) (tblRho W wl wl st')) (6 * W + 6) := by
    intro v S hS
    have hreg : [rg (.v 31), oE, rg (.z 0), rg (.z 1)].Nodup := by
      have h3 := tbl_nodup hrg (l := [.v 31, .z 0, .z 1]) (by simp)
      simp only [List.map_cons, List.map_nil] at h3
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h3 ⊢
      exact ⟨⟨hoE _, h3.1.1, h3.1.2⟩, ⟨fun h => hoE _ h.symm, fun h => hoE _ h.symm⟩, h3.2⟩
    obtain ⟨v', hu, he⟩ := bcopy_exec body hreg v S (by rw [hS, dsOv_rg hrg]; rfl)
      (by rw [hS, dsOv_rg hrg]; rfl)
    have e : Function.update S.R oE (S.R (rg (.v 31)) ++ S.R oE) =
        dsOv rg (Function.update R oE (binSyms W x)) (tblRho W wl wl st') := by
      rw [hS, dsOv_rg hrg, dsOv_off _ _ hoE, hRE, dsOv_update _ _ hoE]
      simp [hp.2.1]
    rw [e] at he
    refine ⟨v', _, hu, ?_, he⟩
    rw [hS, dsOv_rg hrg]; simp
  have h3 : dsRuns body (bwiden oE oWL (rg (.z 0)) (rg (.z 1)) (rg (.z 2)))
      (dsOv rg (Function.update R oE (binSyms W x)) (tblRho W wl wl st'))
      (dsOv rg (Function.update R oE (binSyms WL x)) (tblRho W wl wl st')) (12 * WL + 18) := by
    intro v S hS
    have hreg : [oE, oWL, rg (.z 0), rg (.z 1), rg (.z 2)].Nodup := by
      have h3 := tbl_nodup hrg (l := [.z 0, .z 1, .z 2]) (by simp)
      simp only [List.map_cons, List.map_nil] at h3
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h3 ⊢
      exact ⟨⟨hEW, fun h => hoE _ h.symm, fun h => hoE _ h.symm, fun h => hoE _ h.symm⟩,
        ⟨fun h => hoW _ h.symm, fun h => hoW _ h.symm, fun h => hoW _ h.symm⟩, h3⟩
    have hx : x < 2 ^ W := hp.2.1 ▸ hlt 31
    obtain ⟨v', hu, he⟩ := bwiden_exec body hreg hWWL hx v S
      (by rw [hS, dsOv_off _ _ hoE]; simp)
      (by rw [hS, dsOv_off _ _ hoW, Function.update_of_ne (Ne.symm hEW), hRW])
      (by rw [hS, dsOv_rg hrg]; rfl) (by rw [hS, dsOv_rg hrg]; rfl) (by rw [hS, dsOv_rg hrg]; rfl)
    have e : Function.update S.R oE (binSyms WL x) =
        dsOv rg (Function.update R oE (binSyms WL x)) (tblRho W wl wl st') := by
      rw [hS, dsOv_update _ _ hoE, Function.update_idem]
    rw [e] at he
    exact ⟨v', _, hu, le_rfl, he⟩
  have h4 := ds_code (body := body) hrg wl wl hwl hwl le_rfl
    (dsZC_do (A := A) (W := W) (w := W) σ hσ0 st' hp.1 hp.2.2) hlt
    (Function.update R oE (binSyms WL x))
  refine (h1.seq (h2.seq (h3.seq h4))).mono ?_
  unfold dsStepBCost
  nlinarith

end StepB

end IntegerMultBounds.MathlibTM2.Fast.TableVM
