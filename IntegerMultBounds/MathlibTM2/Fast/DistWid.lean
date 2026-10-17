module

public import IntegerMultBounds.MathlibTM2.Fast.DistSrcBase
public import IntegerMultBounds.MathlibTM2.Fast.DistWidth
import IntegerMultBounds.MathlibTM2.Fast.SrcStage
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# The widths of the pipeline, computed by the machine

The converter (`Fast/DistSrc.lean`) reads the coefficient width `w` and the table word size
`Wt` in unary from `o .uw`, `o .uW`. `dsWid rg g` writes them there from the parameter layout:

* `dsWidC` (`dsWidC_do`): `31 := 10 p + g + 3 + (logT - ℓ) = dsW n`, fifteen atoms;
* `dsWWC` (`dsWWC_do`): `31 := 70 p + 8 g + 3 ℓ + dsW n + 128 = dsWW n`, forty-three atoms;
* `dsWid rg g = dsStep rg dsWidC (o .uw); dsStep rg dsWWC (o .uW)` (`ds_wid_runs`): from the
  layout carrying `pmVals n` and the two registers empty, they end with `dsW n` and `dsWW n`
  ticks, the layout as it started, within `dsWidCost₀ n` steps.

`ds_src_widths`: every width hypothesis of `srcP_runs`/`srcOpp_runs` (`Fast/SrcStage.lean`) and
of `ds_src_runs` holds at `w = dsW n`, `W = dsWW n` for `Big n`; `ds_dsW_le_p`, `ds_dsWW_le_p`:
`dsW n ≤ 12 p`, `dsWW n ≤ 100 p`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Src


/-! ### The codes -/

section Codes

variable {A w' : ℕ} {n : ℕ}

/-- The layout with `a` in `31`, `c` in `32`, the parameters elsewhere. -/
def dsV2 (n a c : ℕ) (j : Fin pmNV) : ℕ := if j = 31 then a else if j = 32 then c else pmVals n j

/-- `31 := 10 p + g + 3 + (logT - ℓ)`, `32 := logT - ℓ`. -/
def dsWidC : TblCode pmNV :=
  tblBlock pmNV [.sub 5 7 32, .add 2 21 31, .add 31 2 31, .add 31 2 31, .add 31 2 31,
    .add 31 2 31, .add 31 2 31, .add 31 2 31, .add 31 2 31, .add 31 2 31, .add 31 2 31,
    .add 31 32 31, .inc 31, .inc 31] (.inc 31)

/-- `31 := 31 + 70 p`, `32 := 64 p`. -/
def dsWWC₂ : TblCode pmNV :=
  tblBlock pmNV [.copy 2 32, .add 32 32 32, .add 31 32 31, .add 32 32 32, .add 31 32 31,
    .add 32 32 32, .add 32 32 32, .add 32 32 32, .add 32 32 32] (.add 31 32 31)

/-- `31 := 31 + 8 g + 3 ℓ`, `32 := 8 g`. -/
def dsWWC₃ : TblCode pmNV :=
  tblBlock pmNV [.copy 21 32, .add 32 32 32, .add 32 32 32, .add 32 32 32, .add 31 32 31,
    .add 31 7 31, .add 31 7 31] (.add 31 7 31)

/-- `31 := 31 + 128`, `32 := 128`. -/
def dsWWC₄ : TblCode pmNV :=
  tblBlock pmNV [.zero 32, .inc 32, .add 32 32 32, .add 32 32 32, .add 32 32 32, .add 32 32 32,
    .add 32 32 32, .add 32 32 32, .add 32 32 32] (.add 31 32 31)

/-- `31 := 70 p + 8 g + 3 ℓ + (10 p + g + 3 + (logT - ℓ)) + 128`. -/
def dsWWC : TblCode pmNV := .seq dsWidC (.seq dsWWC₂ (.seq dsWWC₃ dsWWC₄))

theorem ds_wid_small (hn : 2 ≤ n) : ∀ x, x ≤ dsWW n → x < 2 ^ pmW n := fun x hx =>
  ds_small n (by have := ds_dsWW_le hn; omega)

theorem dsV2_pm (n : ℕ) : dsV2 n 0 0 = pmVals n := by
  funext j
  unfold dsV2
  split_ifs with h1 h2
  · subst h1; simp [pmVals, pmVal, pmNV]
  · subst h2; simp [pmVals, pmVal, pmNV]
  · rfl

theorem dsV2_post (n a c x : ℕ) (hx : a = x) :
    DsPost (A := A) (pmVals n) x ⟨dsV2 n a c, []⟩ :=
  ⟨rfl, by simp [dsV2, hx], fun j hj => by
    show (if j = 31 then a else if j = 32 then c else pmVals n j) = pmVals n j
    rw [ite_eq_right (ds_off_scr hj (k := 31) (by decide) (by decide)),
      ite_eq_right (ds_off_scr hj (k := 32) (by decide) (by decide))]⟩

/-- The bounds the codes use. -/
theorem ds_wid_bounds (hn : 2 ≤ n) :
    Chirp.chirpGuard (d n) ≤ b n + 4 ∧ ℓ n ≤ b n + 2 ∧ logT n ≤ b n + 2 ∧ ℓ n ≤ logT n ∧
      dsW n ≤ 63 * b n + 9 ∧ dsW n ≤ dsWW n ∧ dsWW n ≤ 500 * (b n + 1) :=
  ⟨pm_g_le n, pm_ℓ_le hn, pm_logT_le hn, pm_ℓ_le_logT hn, ds_dsW_le hn, (ds_w_lt_WT n).le,
    ds_dsWW_le hn⟩

theorem dsWidC_do (hn : 2 ≤ n) {a c : ℕ} (ha : a = 0) (hc : c = 0) :
    TblDo A (pmW n) w' dsWidC ⟨dsV2 n a c, []⟩
      (· = ⟨dsV2 n (dsW n) (logT n - ℓ n), []⟩) 15 := by
  subst ha hc
  have hs := ds_wid_small hn
  obtain ⟨hg, hℓ, hlT, hℓT, hW, hWW, h200⟩ := ds_wid_bounds hn
  refine TblDo.block _ _ ?_ ?_
  · simp [tblFitsList, TblIns.fits, TblIns.exact, dsV2, pmVals, pmNV, pmVal]
    repeat' (refine And.intro ?_ ?_)
    all_goals first | exact hℓT | (have := pmW_ge n; omega) | (apply hs; unfold dsWW dsW p; omega)
  · simp [tblExactList, TblIns.exact, dsV2, pmVals, pmNV, pmVal]
    funext j
    fin_cases j <;> simp [dsV2, pmVals, pmNV, pmVal]
    all_goals (unfold dsW; omega)

theorem dsWWC₂_do (hn : 2 ≤ n) {a c : ℕ} (ha : a = dsW n) :
    TblDo A (pmW n) w' dsWWC₂ ⟨dsV2 n a c, []⟩
      (· = ⟨dsV2 n (dsW n + 70 * p n) (64 * p n), []⟩) 10 := by
  subst ha
  have hs := ds_wid_small hn
  obtain ⟨hg, hℓ, hlT, hℓT, hW, hWW, h200⟩ := ds_wid_bounds hn
  refine TblDo.block _ _ ?_ ?_
  · simp [tblFitsList, TblIns.fits, TblIns.exact, dsV2, pmVals, pmNV, pmVal]
    repeat' (refine And.intro ?_ ?_)
    all_goals first | exact hℓT | (have := pmW_ge n; omega) | (apply hs; unfold dsWW dsW p; omega)
  · simp [tblExactList, TblIns.exact, dsV2, pmVals, pmNV, pmVal]
    funext j
    fin_cases j <;> simp [dsV2, pmVals, pmNV, pmVal]
    all_goals omega

theorem dsWWC₃_do (hn : 2 ≤ n) {a c : ℕ} (ha : a = dsW n + 70 * p n) :
    TblDo A (pmW n) w' dsWWC₃ ⟨dsV2 n a c, []⟩
      (· = ⟨dsV2 n (dsW n + 70 * p n + 8 * Chirp.chirpGuard (d n) + 3 * ℓ n)
        (8 * Chirp.chirpGuard (d n)), []⟩) 8 := by
  subst ha
  have hs := ds_wid_small hn
  obtain ⟨hg, hℓ, hlT, hℓT, hW, hWW, h200⟩ := ds_wid_bounds hn
  refine TblDo.block _ _ ?_ ?_
  · simp [tblFitsList, TblIns.fits, TblIns.exact, dsV2, pmVals, pmNV, pmVal]
    repeat' (refine And.intro ?_ ?_)
    all_goals first | exact hℓT | (have := pmW_ge n; omega) | (apply hs; unfold dsWW dsW p; omega)
  · simp [tblExactList, TblIns.exact, dsV2, pmVals, pmNV, pmVal]
    funext j
    fin_cases j <;> simp [dsV2, pmVals, pmNV, pmVal]
    all_goals omega

theorem dsWWC₄_do (hn : 2 ≤ n) {a c : ℕ}
    (ha : a = dsW n + 70 * p n + 8 * Chirp.chirpGuard (d n) + 3 * ℓ n) :
    TblDo A (pmW n) w' dsWWC₄ ⟨dsV2 n a c, []⟩ (· = ⟨dsV2 n (dsWW n) 128, []⟩) 10 := by
  subst ha
  have hs := ds_wid_small hn
  obtain ⟨hg, hℓ, hlT, hℓT, hW, hWW, h200⟩ := ds_wid_bounds hn
  refine TblDo.block _ _ ?_ ?_
  · simp [tblFitsList, TblIns.fits, TblIns.exact, dsV2, pmNV]
    repeat' (refine And.intro ?_ ?_)
    all_goals first | exact hℓT | (have := pmW_ge n; omega) | (apply hs; unfold dsWW dsW p; omega)
  · simp [tblExactList, TblIns.exact, dsV2, pmNV]
    funext j
    fin_cases j <;> simp [dsV2, pmVals, pmNV, pmVal]
    all_goals (unfold dsWW; omega)

theorem dsWidC_post (hn : 2 ≤ n) :
    TblDo A (pmW n) w' dsWidC ⟨pmVals n, []⟩ (DsPost (pmVals n) (dsW n)) 15 := by
  have h := (dsWidC_do (A := A) (w' := w') hn (a := 0) (c := 0) rfl rfl).mono
    (fun s hs => by subst hs; exact dsV2_post n _ _ _ rfl) le_rfl
  rwa [dsV2_pm] at h

theorem dsWWC_post (hn : 2 ≤ n) :
    TblDo A (pmW n) w' dsWWC ⟨pmVals n, []⟩ (DsPost (pmVals n) (dsWW n)) 43 := by
  have h := TblDo.seq (dsWidC_do (A := A) (w' := w') hn (a := 0) (c := 0) rfl rfl) fun s hs => by
    subst hs
    exact TblDo.seq (dsWWC₂_do hn rfl) fun s hs => by
      subst hs
      exact TblDo.seq (dsWWC₃_do hn rfl) fun s hs => by
        subst hs
        exact (dsWWC₄_do hn rfl).mono (fun s hs => by subst hs; exact dsV2_post n _ _ _ rfl) le_rfl
  rw [dsV2_pm] at h
  exact h.mono (fun _ hs => hs) (by norm_num)

end Codes

/-! ### The program -/

section Prog

variable {T Q A t₀ : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR pmNV → Fin T}
  {g : DsY t₀ → Fin T}

/-- The width program: `dsW n` ticks onto `o .uw`, `dsWW n` ticks onto `o .uW`. -/
def dsWid (rg : TblR pmNV → Fin T) (g : DsY t₀ → Fin T) : Pr P T Q A U :=
  .seq (dsStep rg dsWidC (g (.o .uw))) (dsStep rg dsWWC (g (.o .uW)))

/-- The step bound of `dsWid`. -/
def dsWidCost₀ (n : ℕ) : ℕ := dsStepCost (pmW n) 15 (dsW n) + dsStepCost (pmW n) 43 (dsWW n)

variable (h : DsLay rg g)
include h

/-- **The widths.** -/
theorem ds_wid_runs (R : Regs T A) {n : ℕ} (hB : Big n) (wl : List (Fin (A + 4)))
    (hwl : wl.length = pmW n) (X : DsY t₀ → List (Fin (A + 4))) (huw : X (.o .uw) = [])
    (huW : X (.o .uW) = []) :
    dsRuns body (dsWid rg g) (dsF rg g R X (pmW n) wl (pmVals n))
      (dsF rg g R (Function.update (Function.update X (.o .uw) (List.replicate (dsW n) tick))
        (.o .uW) (List.replicate (dsWW n) tick)) (pmW n) wl (pmVals n)) (dsWidCost₀ n) := by
  have hn : 2 ≤ n := hB.1
  have hσ0 : ∀ j : Fin pmNV, 31 ≤ j.val → j.val < 38 → pmVals n j = 0 :=
    fun j h1 _ => pmVal_ge n j (by omega)
  have hσ : ∀ j, pmVals n j < 2 ^ pmW n := fun j => ds_pmVals_lt hB j
  have s1 := dsF_step (body := body) h R wl X (pmVals n) (.o .uw) (dsWidC_post hn) hσ0 hσ hwl huw
  simp only [List.append_nil] at s1
  have s2 := dsF_step (body := body) h R wl
    (Function.update X (.o .uw) (List.replicate (dsW n) tick)) (pmVals n) (.o .uW)
    (dsWWC_post hn) hσ0 hσ hwl (l := []) (by rw [Function.update_of_ne (by simp), huW])
  simp only [List.append_nil] at s2
  exact s1.seq s2

end Prog

/-! ### The width hypotheses at the pipeline widths -/

section Widths

variable {n : ℕ}

theorem ds_dsW_le_p (hn : 2 ≤ n) : dsW n ≤ 12 * p n := by
  have := ds_dsW_le hn; have := one_le_b hn; unfold p; omega

theorem ds_dsWW_le_p (hbig : Big n) : dsWW n ≤ 100 * p n := by
  have := ds_dsWW_le hbig.1; have := hbig.sixteen_le_b; unfold p; omega

/-- `8 p + size r + 80 ≤ dsWW n`. -/
theorem ds_W_twist (n : ℕ) : 8 * p n + Nat.size (r n) + 80 ≤ dsWW n := by
  have h : Nat.size (r n) = ℓ n + 1 := by unfold r; exact Nat.size_pow
  unfold dsWW; omega

/-- **The width hypotheses** of `srcP_runs`, `srcOpp_runs` and `ds_src_runs` at `w = dsW n`,
`W = dsWW n`. -/
theorem ds_src_widths (hbig : Big n) :
    (p n + Chirp.chirpGuard (d n) + 3 ≤ dsW n) ∧ dsW n < dsWW n ∧
    (∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) * (Pipeline.windowA (p n) (alpha n) + 1)) ^ 2 *
      2 ^ (13 * p n + 8) < 2 ^ dsWW n) ∧
    (9 * p n + 2 ≤ dsW n ∧ ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) *
      (8 * FastB0.fastWindow (p n) (alpha n) + 1)) ^ 2 * 2 ^ (65 * p n + 8) < 2 ^ dsWW n) ∧
    (∀ k, s n k * t n k * t n k < 2 ^ dsWW n) ∧
    (∀ k, 8 * (p n + Chirp.chirpGuard (d n)) + Nat.size (t n k) + 80 ≤ dsWW n) ∧
    p n + 2 ≤ dsW n ∧ gamma n ≤ dsW n ∧ logT n - ℓ n ≤ dsW n ∧
    4 * dsW n + 2 < 2 ^ pmW n ∧ pmW n ≤ dsWL n (dsW n) ∧ dsWW n < 2 ^ pmW n ∧
    8 * p n + Nat.size (r n) + 80 ≤ dsWW n := by
  obtain ⟨h1, h2, h3⟩ := ds_widths_dist hbig.1
  refine ⟨ds_w_chirp n, ds_w_lt_WT n, ds_A_W hbig, ⟨by unfold dsW; omega, ds_B_W65 hbig⟩,
    ds_chirp_sN hbig, ds_chirp_W n,
    ds_w_B n, (src_gamma_le hbig).trans (by unfold dsW; omega), by unfold dsW; omega, h2, h3, h1,
    ds_W_twist n⟩

end Widths

end IntegerMultBounds.MathlibTM2.Fast.TableVM
