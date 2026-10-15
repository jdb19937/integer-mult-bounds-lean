module

public import IntegerMultBounds.MathlibTM2.Fast.DistSrcBase

/-!
# Table codes of the converter

Small codes on the parameter layout (`Fast/DistGlob.lean` conventions, `DsPost`):
`w - γ`, `w - Σ aᵢ`, `p + 1`, `p + g + 2`, `w - (p + 2)`, `p + 2` into `31`; and the glue
codes `dsZ38`, `dsZ39` (clear `Wt`, `w`), `dsCInit` (`S_0 = P_0 = 1`), `dsCEnd` (clear the CRT
loop's variables).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

section Codes

variable {A w' : ℕ} {n w : ℕ}

/-- `Wt := 0`. -/
def dsZ38 : TblCode pmNV := .ins (.zero 38)

/-- `w := 0`. -/
def dsZ39 : TblCode pmNV := .ins (.zero 39)

/-- `S := 1`, `P := 1`. -/
def dsCInit : TblCode pmNV := tblBlock pmNV [.inc 32] (.inc 33)

/-- Clear `31 … 35`. -/
def dsCEnd : TblCode pmNV := tblBlock pmNV [.zero 31, .zero 32, .zero 33, .zero 34] (.zero 35)

/-- `31 := w - γ`. -/
def dsCwg : TblCode pmNV := .ins (.sub 39 14 31)

/-- `31 := w - (logT - ℓ)`. -/
def dsCwN : TblCode pmNV := tblBlock pmNV [.sub 5 7 32] (.sub 39 32 31)

/-- `31 := p + 1`. -/
def dsCp1 : TblCode pmNV := tblBlock pmNV [.copy 2 31] (.inc 31)

/-- `31 := p + g + 2`. -/
def dsCpg2 : TblCode pmNV := tblBlock pmNV [.copy 28 31, .inc 31] (.inc 31)

/-- `31 := w - (p + 2)`. -/
def dsCwp2 : TblCode pmNV := tblBlock pmNV [.copy 2 32, .inc 32, .inc 32] (.sub 39 32 31)

/-- `31 := p + 2`. -/
def dsCp2 : TblCode pmNV := tblBlock pmNV [.copy 2 31, .inc 31] (.inc 31)

theorem dsZ38_do (Wt : ℕ) :
    TblDo A (pmW n) w' dsZ38 ⟨dsV1 n Wt 0, []⟩ (· = ⟨pmVals n, []⟩) 1 := by
  refine TblDo.ins _ ?_
  rw [← dsV1_pm, ← dsV1_upd38 n Wt 0]
  simp only [TblIns.run]
  congr 1
  funext j; fin_cases j <;> simp [dsV1, Fin.ext_iff, pmNV]

theorem dsZ39_do :
    TblDo A (pmW n) w' dsZ39 ⟨dsV1 n 0 w, []⟩ (· = ⟨pmVals n, []⟩) 1 := by
  refine TblDo.ins _ ?_
  rw [← dsV1_pm]
  simp only [TblIns.run]
  congr 1
  funext j; fin_cases j <;> simp [dsV1, Fin.ext_iff, pmNV]

theorem dsCInit_do :
    TblDo A (pmW n) w' dsCInit ⟨pmVals n, []⟩ (· = ⟨dsCV n 0, []⟩) 2 := by
  have h2 : 2 < 2 ^ pmW n := by
    have : 2 ^ 2 ≤ 2 ^ pmW n := pm_two_pow_le (by have := pmW_ge n; omega)
    omega
  refine TblDo.block _ _ ?_ ?_
  · simp [tblFitsList, TblIns.fits, TblIns.exact, pmVals, pmVal_ge n _ (show 31 ≤ 32 by omega),
      pmVal_ge n _ (show 31 ≤ 33 by omega), pmNV]
    have := pmW_ge n; omega
  · simp only [tblExactList, TblIns.exact, List.nil_append, List.cons_append]
    congr 1
    funext j
    fin_cases j <;> simp [dsCV, pmVals, Function.update_apply, Fin.ext_iff, pmNV, dsSP, dsP,
      dsSig, dsMsk, pmVal_ge]

theorem dsCEnd_do :
    TblDo A (pmW n) w' dsCEnd ⟨dsCV n (d n), []⟩ (· = ⟨pmVals n, []⟩) 5 := by
  refine TblDo.block _ _ (by simp [tblFitsList, TblIns.fits]) ?_
  simp only [tblExactList, TblIns.exact, List.nil_append, List.cons_append]
  congr 1
  funext j
  fin_cases j <;> simp [dsCV, pmVals, Function.update_apply, Fin.ext_iff, pmNV, pmVal_ge]

section Post

variable {x K : ℕ}

/-- A single-instruction step writing `31`. -/
theorem ds_post1 {i : TblIns pmNV} (σ : Fin pmNV → ℕ) (hf : i.fits A (pmW n) ⟨σ, []⟩)
    (hx : (i.exact A w' ⟨σ, []⟩).val 31 = x)
    (hfr : ∀ j : Fin pmNV, (j.val < 31 ∨ 38 ≤ j.val) → (i.exact A w' ⟨σ, []⟩).val j = σ j)
    (hacc : (i.exact A w' ⟨σ, []⟩).acc = []) :
    TblDo A (pmW n) w' (.ins i) ⟨σ, []⟩ (DsPost σ x) 1 :=
  TblDo.insX _ hf ⟨hacc, hx, hfr⟩

end Post

theorem dsCwg_do (hw : gamma n ≤ w) (hw2 : w < 2 ^ pmW n) :
    TblDo A (pmW n) w' dsCwg ⟨dsV1 n 0 w, []⟩ (DsPost (dsV1 n 0 w) (w - gamma n)) 1 := by
  refine TblDo.insX _ ?_ ⟨rfl, ?_, fun j hj => ?_⟩
  · simp [TblIns.fits, dsV1, pmNV, pmVal]; exact ⟨hw, hw2⟩
  · simp [TblIns.exact, dsV1, pmNV, pmVal]
  · simp [TblIns.exact, ds_upd_off hj (k := 31) (by decide) (by decide)]

theorem dsCwN_do (hn : 2 ≤ n) (hw : logT n - ℓ n ≤ w) (hw2 : w < 2 ^ pmW n) :
    TblDo A (pmW n) w' dsCwN ⟨dsV1 n 0 w, []⟩ (DsPost (dsV1 n 0 w) (w - (logT n - ℓ n))) 2 := by
  have h1 := pm_ℓ_le_logT hn
  have h2 := ds_pmVal_lt hn 5
  refine TblDo.block _ _ ?_ ⟨rfl, ?_, fun j hj => ?_⟩
  · simp [tblFitsList, TblIns.fits, TblIns.exact, dsV1, pmNV, pmVal]
    exact ⟨⟨h1, h2⟩, by omega, hw2⟩
  · simp [tblExactList, TblIns.exact, dsV1, pmNV, pmVal]
  · simp [tblExactList, TblIns.exact, ds_upd_off hj (k := 31) (by decide) (by decide),
      ds_upd_off hj (k := 32) (by decide) (by decide)]

theorem dsCp1_do :
    TblDo A (pmW n) w' dsCp1 ⟨dsV1 n 0 w, []⟩ (DsPost (dsV1 n 0 w) (p n + 1)) 2 := by
  refine TblDo.block _ _ ?_ ⟨rfl, ?_, fun j hj => ?_⟩
  · simp [tblFitsList, TblIns.fits, TblIns.exact, dsV1, pmNV, pmVal]
    exact ds_small n (by unfold p; omega)
  · simp [tblExactList, TblIns.exact, dsV1, pmNV, pmVal]
  · simp [tblExactList, TblIns.exact, ds_upd_off hj (k := 31) (by decide) (by decide)]

theorem dsCpg2_do :
    TblDo A (pmW n) w' dsCpg2 ⟨dsV1 n 0 w, []⟩
      (DsPost (dsV1 n 0 w) (p n + Chirp.chirpGuard (d n) + 2)) 3 := by
  have hg := pm_g_le n
  refine TblDo.block _ _ ?_ ⟨rfl, ?_, fun j hj => ?_⟩
  · simp [tblFitsList, TblIns.fits, TblIns.exact, dsV1, pmNV, pmVal]
    exact ⟨ds_small n (by unfold p; omega), ds_small n (by unfold p; omega)⟩
  · simp [tblExactList, TblIns.exact, dsV1, pmNV, pmVal]
  · simp [tblExactList, TblIns.exact, ds_upd_off hj (k := 31) (by decide) (by decide)]

theorem dsCwp2_do (hw : p n + 2 ≤ w) (hw2 : w < 2 ^ pmW n) :
    TblDo A (pmW n) w' dsCwp2 ⟨dsV1 n 0 w, []⟩ (DsPost (dsV1 n 0 w) (w - (p n + 2))) 4 := by
  refine TblDo.block _ _ ?_ ⟨rfl, ?_, fun j hj => ?_⟩
  · simp [tblFitsList, TblIns.fits, TblIns.exact, dsV1, pmNV, pmVal]
    refine ⟨ds_small n (by unfold p; omega), ds_small n (by unfold p; omega), by omega, hw2⟩
  · simp [tblExactList, TblIns.exact, dsV1, pmNV, pmVal]
  · simp [tblExactList, TblIns.exact, ds_upd_off hj (k := 31) (by decide) (by decide),
      ds_upd_off hj (k := 32) (by decide) (by decide)]

theorem dsCp2_do :
    TblDo A (pmW n) w' dsCp2 ⟨dsV1 n 0 w, []⟩ (DsPost (dsV1 n 0 w) (p n + 2)) 3 := by
  refine TblDo.block _ _ ?_ ⟨rfl, ?_, fun j hj => ?_⟩
  · simp [tblFitsList, TblIns.fits, TblIns.exact, dsV1, pmNV, pmVal]
    exact ⟨ds_small n (by unfold p; omega), ds_small n (by unfold p; omega)⟩
  · simp [tblExactList, TblIns.exact, dsV1, pmNV, pmVal]
  · simp [tblExactList, TblIns.exact, ds_upd_off hj (k := 31) (by decide) (by decide)]

end Codes

end IntegerMultBounds.MathlibTM2.Fast.TableVM
