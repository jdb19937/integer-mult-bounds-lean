module

public import IntegerMultBounds.MathlibTM2.Fast.BundleLay

/-!
# The rounding and output parameters from the parameter layout

After the distribution machine the parameter layout `mnPm` still holds `pmVals n` (`bdρ n`).
`bdRnd` fills the registers of the rounding and output stages that the distribution contract
`MnDistOut` asks for, one table step (`dsStep`, `dsStepB` of `Fast/DistGlob`) each:

* `io .dwn`, `rnd .wn`: `w = dsW n` ticks (`dsWidC`);
* `rnd .mn`: `mnMw n w = w + 2 size S` ticks; under `Big n`, `size S = logT` (`bd_size_S`), so
  the code `bdCMw` computes `w + 2 logT` (`bdMw n`);
* `rnd .nn`: `topN (mnMw n w)` ticks (`bdCTop`: `bdCMw`, then `dsCTop` of `Fast/DistGlob` on
  the value copied into variable `39`);
* `rnd .sq`: `binSyms (mnMw n w) (S²)` (`bdCSq`, a binary step widened to the length of
  `rnd .mn`);
* `rnd .wo`, `out .wr`: `mnWo n = 2 b + 2 size S + 6` ticks (`bdCWo`).

`bd_rnd_runs`: from the layout `bdρ n` and the seven registers empty, `bdRnd` ends with the
seven registers filled (`bdRndF n R`), everything else as it was, within `bdRndCost n` steps;
`bd_rndCost_le`: `bdRndCost n = O((b n + 1)^4)`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open IntegerMultBounds.Schoenhage.Schedule (topN)
open Filter

set_option linter.unusedSimpArgs false

noncomputable section

/-! ### The widths -/

/-- The rounding operand width at `w = dsW n`, with `size S = logT`. -/
def bdMw (n : ℕ) : ℕ := dsW n + 2 * logT n

/-- The output word size, with `size S = logT`. -/
def bdWo (n : ℕ) : ℕ := 2 * b n + 2 * logT n + 6

lemma bd_size_S {n : ℕ} (hbig : Big n) : Nat.size (S n) = logT n := by
  have h1 : S n < 2 ^ logT n := hbig.S_lt_T
  have h2 : 2 ^ logT n < 2 * S n := hbig.T_lt_two_S
  have hl := hbig.one_le_logT
  apply le_antisymm (Nat.size_le.2 h1)
  by_contra h
  push Not at h
  have h3 : S n < 2 ^ (logT n - 1) := Nat.size_le.1 (by omega)
  have h4 : 2 ^ logT n = 2 * 2 ^ (logT n - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

lemma bdMw_eq {n : ℕ} (hbig : Big n) : mnMw n (dsW n) = bdMw n := by
  unfold mnMw bdMw; rw [bd_size_S hbig]

lemma bdWo_eq {n : ℕ} (hbig : Big n) : mnWo n = bdWo n := by
  unfold mnWo bdWo; rw [bd_size_S hbig]

lemma bd_S_sq_lt {n : ℕ} (hbig : Big n) : S n * S n < 2 ^ pmW n := by
  have h1 : S n < 2 ^ logT n := hbig.S_lt_T
  have h2 := hbig.logT_bounds.2
  have h3 : 2 ^ logT n * 2 ^ logT n ≤ 2 ^ pmW n := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by have := pmW_ge n; omega)
  exact (Nat.mul_lt_mul'' h1 h1).trans_le h3

/-! ### The codes -/

section Codes

variable {w' : ℕ} {n : ℕ}

/-- `31 := w + 2 logT`, `32 := 2 logT`. -/
def bdCMw : TblCode pmNV := dsWidC ;; tblBlock pmNV [.add 5 5 32] (.add 31 32 31)

/-- `31 := S²`. -/
def bdCSq : TblCode pmNV := .ins (.mul 18 18 31)

/-- `31 := 2 b + 2 logT + 6`, `32 := 2 logT`. -/
def bdCWo : TblCode pmNV :=
  tblBlock pmNV [.add 1 1 31, .add 5 5 32, .add 31 32 31, .inc 31, .inc 31, .inc 31, .inc 31,
    .inc 31] (.inc 31)

/-- `31 := topN (w + 2 logT)`: `bdCMw`, the value copied into `39`, the scratch cleared,
`dsCTop`, `39` cleared. -/
def bdCTop : TblCode pmNV :=
  bdCMw ;; .ins (.copy 31 39) ;; dsZC ;; dsCTop ;; .ins (.zero 39)

/-- The atoms of `bdCTop`. -/
def bdTopK (n : ℕ) : ℕ := dsTopK (bdMw n) + 17

theorem bdCMw₂_do (hn : 2 ≤ n) :
    TblDo bdA (pmW n) w' (tblBlock pmNV [.add 5 5 32] (.add 31 32 31))
      ⟨dsV2 n (dsW n) (logT n - ℓ n), []⟩ (· = ⟨dsV2 n (bdMw n) (2 * logT n), []⟩) 2 := by
  obtain ⟨hg, hℓ, hlT, hℓT, hW, hWW, h200⟩ := ds_wid_bounds hn
  refine TblDo.block _ _ ?_ ?_
  · simp [tblFitsList, TblIns.fits, TblIns.exact, dsV2, pmVals, pmNV, pmVal]
    constructor <;> apply ds_small n <;> omega
  · simp [tblExactList, TblIns.exact, dsV2, pmVals, pmNV, pmVal]
    funext j
    fin_cases j <;> simp [dsV2, pmVals, pmNV, pmVal]
    all_goals first | omega | (unfold bdMw; omega)

theorem bdCMw_do (hn : 2 ≤ n) :
    TblDo bdA (pmW n) w' bdCMw ⟨pmVals n, []⟩ (DsPost (pmVals n) (bdMw n)) 8 := by
  have h := (dsWidC_do (A := bdA) (w' := w') hn (a := 0) (c := 0) rfl rfl).seq fun s hs => by
    subst hs
    exact bdCMw₂_do hn
  rw [dsV2_pm] at h
  exact h.mono (fun s hs => by subst hs; exact dsV2_post n _ _ _ rfl) le_rfl

theorem bdCSq_do (hbig : Big n) :
    TblDo bdA (pmW n) w' bdCSq ⟨pmVals n, []⟩ (DsPost (pmVals n) (S n * S n)) 1 := by
  refine TblDo.insX _ ?_ ⟨rfl, ?_, fun j hj => ?_⟩
  · simp [TblIns.fits, pmVals, pmNV, pmVal]; exact bd_S_sq_lt hbig
  · simp [TblIns.exact, pmVals, pmNV, pmVal]
  · simp [TblIns.exact, ds_upd_off hj (k := 31) (by decide) (by decide)]

theorem bdCWo_do (hn : 2 ≤ n) :
    TblDo bdA (pmW n) w' bdCWo ⟨pmVals n, []⟩ (DsPost (pmVals n) (bdWo n)) 9 := by
  obtain ⟨hg, hℓ, hlT, hℓT, hW, hWW, h200⟩ := ds_wid_bounds hn
  have h : TblDo bdA (pmW n) w' bdCWo ⟨dsV2 n 0 0, []⟩
      (· = ⟨dsV2 n (bdWo n) (2 * logT n), []⟩) 9 := by
    refine TblDo.block _ _ ?_ ?_
    · simp [tblFitsList, TblIns.fits, TblIns.exact, dsV2, pmVals, pmNV, pmVal]
      repeat' (refine And.intro ?_ ?_)
      all_goals apply ds_small n; omega
    · simp [tblExactList, TblIns.exact, dsV2, pmVals, pmNV, pmVal]
      funext j
      fin_cases j <;> simp [dsV2, pmVals, pmNV, pmVal]
      all_goals first | omega | (unfold bdWo; omega)
  rw [dsV2_pm] at h
  exact h.mono (fun s hs => by subst hs; exact dsV2_post n _ _ _ rfl) le_rfl

lemma bdMw_le (hn : 2 ≤ n) : bdMw n ≤ 11 * b n + 13 := by
  obtain ⟨hg, hℓ, hlT, hℓT, hW, hWW, h200⟩ := ds_wid_bounds hn
  unfold bdMw; omega

theorem bdCTop_do (hbig : Big n) :
    TblDo bdA (pmW n) w' bdCTop ⟨pmVals n, []⟩ (DsPost (pmVals n) (dsTopN (bdMw n)))
      (bdTopK n) := by
  have hn := hbig.1
  have hm := bdMw_le hn
  have hw : 4 * bdMw n + 2 < 2 ^ pmW n := ds_small n (by omega)
  have h39 : pmVals n 39 = 0 := pmVal_ge n 39 (by norm_num)
  have h38 : pmVals n 38 = 0 := pmVal_ge n 38 (by norm_num)
  have hV : ∀ j : Fin pmNV, j.val < 31 ∨ 38 ≤ j.val → j ≠ 39 →
      dsV1 n 0 (bdMw n) j = pmVals n j := by
    intro j hj hj39
    unfold dsV1
    split_ifs with h1 h2 h3
    · rfl
    · rw [show j = 38 from Fin.ext h2, h38]
    · exact absurd (Fin.ext h3) hj39
    · exfalso; have := j.isLt; simp only [pmNV] at this; omega
  have h : TblDo bdA (pmW n) w' (bdCMw ;; .ins (.copy 31 39) ;; dsZC ;; dsCTop ;; .ins (.zero 39))
      ⟨pmVals n, []⟩ (DsPost (pmVals n) (dsTopN (bdMw n)))
      (8 + (1 + (7 + (dsTopK (bdMw n) + 1)))) := by
    -- `bdCMw`
    refine (bdCMw_do hn).seq fun s hs => ?_
    obtain ⟨hacc, h31, hs⟩ := hs
    -- `copy 31 39`
    refine (TblDo.insX (.copy 31 39) (st := s)
      (P := (· = ⟨Function.update s.val 39 (bdMw n), []⟩)) trivial ?_).seq fun s' hs' => ?_
    · simp [TblIns.exact, hacc, h31]
    subst hs'
    -- `dsZC`
    refine (dsZC_do (dsV1 n 0 (bdMw n)) (fun j h1 h2 => dsV1_scr n 0 (bdMw n) j h1 h2) _ rfl
      ?_).seq fun s' hs' => ?_
    · intro j hj
      by_cases hj39 : j = 39
      · subst hj39; simp [dsV1]
      · show Function.update s.val 39 (bdMw n) j = _
        rw [Function.update_of_ne hj39, hs j hj, hV j hj hj39]
    subst hs'
    -- `dsCTop`
    refine (dsCTop_do (A := bdA) (w' := w') (n := n) (Wt := 0) (w := bdMw n) hw).seq
      fun s' hs' => ?_
    obtain ⟨hacc', h31', hs'⟩ := hs'
    -- `zero 39`
    refine TblDo.insX (.zero 39) trivial ⟨?_, ?_, fun j hj => ?_⟩
    · simpa [TblIns.exact] using hacc'
    · simp only [TblIns.exact]
      rw [Function.update_of_ne (by decide), h31']
    · simp only [TblIns.exact]
      by_cases hj39 : j = 39
      · subst hj39; simp [h39]
      · rw [Function.update_of_ne hj39, hs' j hj, hV j hj hj39]
  exact h.mono (fun _ h => h) (by unfold bdTopK; omega)

end Codes

/-! ### The program -/

/-- **The rounding and output parameters.** -/
def bdRnd : MnPr bdA :=
  .seq (dsStep mnPm dsWidC (mnIo .dwn)) <| .seq (dsStep mnPm dsWidC (mnRnd .wn)) <|
  .seq (dsStep mnPm bdCMw (mnRnd .mn)) <| .seq (dsStep mnPm bdCTop (mnRnd .nn)) <|
  .seq (dsStepB mnPm bdCSq (mnRnd .sq) (mnRnd .mn)) <|
  .seq (dsStep mnPm bdCWo (mnRnd .wo)) (dsStep mnPm bdCWo (mnOutR .wr))

/-- The step bound of `bdRnd`. -/
def bdRndCost (n : ℕ) : ℕ :=
  dsStepCost (pmW n) 6 (dsW n) + dsStepCost (pmW n) 6 (dsW n) + dsStepCost (pmW n) 8 (bdMw n) +
    dsStepCost (pmW n) (bdTopK n) (dsTopN (bdMw n)) + dsStepBCost (pmW n) 1 (bdMw n) +
    dsStepCost (pmW n) 9 (bdWo n) + dsStepCost (pmW n) 9 (bdWo n)

/-- The register file after `bdRnd`. -/
def bdRndF (n : ℕ) (R : Regs mnT bdA) : Regs mnT bdA :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update R
      (mnIo .dwn) (List.replicate (dsW n) tick))
      (mnRnd .wn) (List.replicate (dsW n) tick))
      (mnRnd .mn) (List.replicate (bdMw n) tick))
      (mnRnd .nn) (List.replicate (dsTopN (bdMw n)) tick))
      (mnRnd .sq) (binSyms (bdMw n) (S n * S n)))
      (mnRnd .wo) (List.replicate (bdWo n) tick))
      (mnOutR .wr) (List.replicate (bdWo n) tick)

/-- The registers `bdRnd` writes. -/
def bdRndRegs : List MnR :=
  [.io .dwn, .rnd .wn, .rnd .mn, .rnd .nn, .rnd .sq, .rnd .wo, .out .wr]

section Runs

variable {body : MnProc → MnPr bdA} {n : ℕ}

lemma bd_pm_ne {q : MnR} (r : TblR pmNV) (h : q ≠ .pm r) : mnPm r ≠ mnRg q :=
  mn_rg_ne (Ne.symm h)

/-- A step onto an empty register. -/
lemma bd_step_nil (hn : 2 ≤ n) (o : Fin mnT) (ho : ∀ r, mnPm r ≠ o) {c : TblCode pmNV} {x K : ℕ}
    (hc : TblDo bdA (pmW n) (pmW n) c ⟨pmVals n, []⟩ (DsPost (pmVals n) x) K)
    (R : Regs mnT bdA) (hR : R o = []) :
    dsRuns body (dsStep mnPm c o) (dsOv mnPm R (bdρ n))
      (dsOv mnPm (Function.update R o (List.replicate x tick)) (bdρ n))
      (dsStepCost (pmW n) K x) := by
  have h := ds_step (body := body) bdPm_inj ho (bdWl n) (bdWl_length n) hc
    (fun j h1 _ => pmVal_ge n j h1) (ds_pmVals_lt hn) R
  rwa [hR, List.append_nil] at h

/-- A binary step onto an empty register. -/
lemma bd_stepB_nil (hn : 2 ≤ n) (oE oWL : Fin mnT) (hoE : ∀ r, mnPm r ≠ oE)
    (hoW : ∀ r, mnPm r ≠ oWL) (hEW : oE ≠ oWL) {c : TblCode pmNV} {x K : ℕ}
    (hc : TblDo bdA (pmW n) (pmW n) c ⟨pmVals n, []⟩ (DsPost (pmVals n) x) K)
    {WL : ℕ} (hWWL : pmW n ≤ WL) (R : Regs mnT bdA) (hRE : R oE = []) (hRW : (R oWL).length = WL) :
    dsRuns body (dsStepB mnPm c oE oWL) (dsOv mnPm R (bdρ n))
      (dsOv mnPm (Function.update R oE (binSyms WL x)) (bdρ n)) (dsStepBCost (pmW n) K WL) :=
  ds_stepB (body := body) bdPm_inj hoE hoW hEW (bdWl n) (bdWl_length n) hc
    (fun j h1 _ => pmVal_ge n j h1) (ds_pmVals_lt hn) hWWL R hRE hRW

/-- `pmW n ≤ bdMw n` under `Big n`. -/
lemma bd_pmW_le_Mw (hbig : Big n) : pmW n ≤ bdMw n := by
  have h1 : Nat.size n ≤ b n + 1 := pm_size_le
  have h2 := hbig.sixteen_le_b
  have h3 : dsW n = p n + Chirp.chirpGuard (d n) + 3 + (logT n - ℓ n) := rfl
  unfold pmW bdMw p at *
  omega

/-- **The rounding and output parameters**: from the layout `bdρ n` and the seven registers
empty, `bdRnd` fills them (`bdRndF`) within `bdRndCost n` steps. -/
theorem bd_rnd_runs (hbig : Big n) (R : Regs mnT bdA) (hR : ∀ r ∈ bdRndRegs, R (mnRg r) = []) :
    dsRuns body bdRnd (dsOv mnPm R (bdρ n)) (dsOv mnPm (bdRndF n R) (bdρ n)) (bdRndCost n) := by
  have hn := hbig.1
  simp only [bdRndRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hR
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hR
  have hc1 := dsWidC_post (A := bdA) (w' := pmW n) hn
  set R₁ := Function.update R (mnIo .dwn) (List.replicate (dsW n) tick) with hR₁
  set R₂ := Function.update R₁ (mnRnd .wn) (List.replicate (dsW n) tick) with hR₂
  set R₃ := Function.update R₂ (mnRnd .mn) (List.replicate (bdMw n) tick) with hR₃
  set R₄ := Function.update R₃ (mnRnd .nn) (List.replicate (dsTopN (bdMw n)) tick) with hR₄
  set R₅ := Function.update R₄ (mnRnd .sq) (binSyms (bdMw n) (S n * S n)) with hR₅
  set R₆ := Function.update R₅ (mnRnd .wo) (List.replicate (bdWo n) tick) with hR₆
  have s1 := bd_step_nil (body := body) hn (mnIo .dwn) (fun r => bd_pm_ne r (by simp)) hc1 R h1
  have s2 := bd_step_nil (body := body) hn (mnRnd .wn) (fun r => bd_pm_ne r (by simp)) hc1 R₁
    (by rw [hR₁, Function.update_of_ne (mn_rg_ne' (.rnd .wn) (.io .dwn))]; exact h2)
  have s3 := bd_step_nil (body := body) hn (mnRnd .mn) (fun r => bd_pm_ne r (by simp))
    (bdCMw_do hn) R₂
    (by rw [hR₂, Function.update_of_ne (mn_rg_ne' (.rnd .mn) (.rnd .wn)), hR₁,
      Function.update_of_ne (mn_rg_ne' (.rnd .mn) (.io .dwn))]; exact h3)
  have s4 := bd_step_nil (body := body) hn (mnRnd .nn) (fun r => bd_pm_ne r (by simp))
    (bdCTop_do hbig) R₃
    (by rw [hR₃, Function.update_of_ne (mn_rg_ne' (.rnd .nn) (.rnd .mn)), hR₂,
      Function.update_of_ne (mn_rg_ne' (.rnd .nn) (.rnd .wn)), hR₁,
      Function.update_of_ne (mn_rg_ne' (.rnd .nn) (.io .dwn))]; exact h4)
  have s5 := bd_stepB_nil (body := body) hn (mnRnd .sq) (mnRnd .mn)
    (fun r => bd_pm_ne r (by simp)) (fun r => bd_pm_ne r (by simp))
    (mn_rg_ne' (.rnd .sq) (.rnd .mn)) (bdCSq_do hbig) (bd_pmW_le_Mw hbig) R₄
    (by rw [hR₄, Function.update_of_ne (mn_rg_ne' (.rnd .sq) (.rnd .nn)), hR₃,
      Function.update_of_ne (mn_rg_ne' (.rnd .sq) (.rnd .mn)), hR₂,
      Function.update_of_ne (mn_rg_ne' (.rnd .sq) (.rnd .wn)), hR₁,
      Function.update_of_ne (mn_rg_ne' (.rnd .sq) (.io .dwn))]; exact h5)
    (by rw [hR₄, Function.update_of_ne (mn_rg_ne' (.rnd .mn) (.rnd .nn)), hR₃,
      Function.update_self]; simp)
  have s6 := bd_step_nil (body := body) hn (mnRnd .wo) (fun r => bd_pm_ne r (by simp))
    (bdCWo_do hn) R₅
    (by rw [hR₅, Function.update_of_ne (mn_rg_ne' (.rnd .wo) (.rnd .sq)), hR₄,
      Function.update_of_ne (mn_rg_ne' (.rnd .wo) (.rnd .nn)), hR₃,
      Function.update_of_ne (mn_rg_ne' (.rnd .wo) (.rnd .mn)), hR₂,
      Function.update_of_ne (mn_rg_ne' (.rnd .wo) (.rnd .wn)), hR₁,
      Function.update_of_ne (mn_rg_ne' (.rnd .wo) (.io .dwn))]; exact h6)
  have s7 := bd_step_nil (body := body) hn (mnOutR .wr) (fun r => bd_pm_ne r (by simp))
    (bdCWo_do hn) R₆
    (by rw [hR₆, Function.update_of_ne (mn_rg_ne' (.out .wr) (.rnd .wo)), hR₅,
      Function.update_of_ne (mn_rg_ne' (.out .wr) (.rnd .sq)), hR₄,
      Function.update_of_ne (mn_rg_ne' (.out .wr) (.rnd .nn)), hR₃,
      Function.update_of_ne (mn_rg_ne' (.out .wr) (.rnd .mn)), hR₂,
      Function.update_of_ne (mn_rg_ne' (.out .wr) (.rnd .wn)), hR₁,
      Function.update_of_ne (mn_rg_ne' (.out .wr) (.io .dwn))]; exact h7)
  refine (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq s7)))))).mono ?_
  unfold bdRndCost; omega

end Runs

/-! ### Reading the final file -/

section Final

variable {n : ℕ} {R : Regs mnT bdA}

lemma bdRndF_dwn : bdRndF n R (mnIo .dwn) = List.replicate (dsW n) tick := by
  simp [bdRndF, Function.update_apply]

lemma bdRndF_rwn : bdRndF n R (mnRnd .wn) = List.replicate (dsW n) tick := by
  simp [bdRndF, Function.update_apply]

lemma bdRndF_rmn : bdRndF n R (mnRnd .mn) = List.replicate (bdMw n) tick := by
  simp [bdRndF, Function.update_apply]

lemma bdRndF_rnn : bdRndF n R (mnRnd .nn) = List.replicate (dsTopN (bdMw n)) tick := by
  simp [bdRndF, Function.update_apply]

lemma bdRndF_rsq : bdRndF n R (mnRnd .sq) = binSyms (bdMw n) (S n * S n) := by
  simp [bdRndF, Function.update_apply]

lemma bdRndF_rwo : bdRndF n R (mnRnd .wo) = List.replicate (bdWo n) tick := by
  simp [bdRndF, Function.update_apply]

lemma bdRndF_owr : bdRndF n R (mnOutR .wr) = List.replicate (bdWo n) tick := by
  simp [bdRndF, Function.update_apply]

/-- Off the seven registers the file is unchanged. -/
lemma bdRndF_off {k : Fin mnT} (hk : ∀ r ∈ bdRndRegs, mnRg r ≠ k) : bdRndF n R k = R k := by
  simp only [bdRndRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hk
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hk
  unfold bdRndF
  rw [Function.update_of_ne (Ne.symm h7), Function.update_of_ne (Ne.symm h6),
    Function.update_of_ne (Ne.symm h5), Function.update_of_ne (Ne.symm h4),
    Function.update_of_ne (Ne.symm h3), Function.update_of_ne (Ne.symm h2),
    Function.update_of_ne (Ne.symm h1)]

lemma bdRndF_rg {r : MnR} (hr : r ∉ bdRndRegs) : bdRndF n R (mnRg r) = R (mnRg r) :=
  bdRndF_off fun _ hq h => hr (mnRg_inj h ▸ hq)

lemma bdRndF_ι (j : Fin 64) : bdRndF n R (mnι j) = R (mnι j) :=
  bdRndF_off fun q _ => mnRg_ne_ι q j

lemma bdRndF_lay (x : LReg CReg) : bdRndF n R (mnLay x) = R (mnLay x) :=
  bdRndF_off fun q _ => mnRg_ne_lay q x

end Final

/-! ### The cost -/

section Cost

lemma bd_tblC_le {W B : ℕ} (hB : 1 ≤ B) (hW : W ≤ 24 * B) : tblC W W ≤ 25280 * B ^ 2 := by
  unfold tblC
  have h1 : (W + 4) ^ 2 ≤ (28 * B) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : B ≤ B ^ 2 := by
    rcases Nat.eq_zero_or_pos B with h | h
    · subst h; simp
    · exact Nat.le_self_pow (by norm_num) B
  have : (28 * B) ^ 2 = 784 * B ^ 2 := by ring
  omega

lemma bd_stepCost_le {W K x B : ℕ} (hW : W ≤ 24 * B) (hK : K + 7 ≤ B) (hx : x + 1 ≤ B) :
    dsStepCost W K x ≤ 25280 * B ^ 4 + 270 * B ^ 3 := by
  unfold dsStepCost
  have h1 := bd_tblC_le (by omega) hW
  have h2 : (K + 7) * tblC W W ≤ B * (25280 * B ^ 2) := Nat.mul_le_mul hK h1
  have h3 : W * (4 * x + 11) ≤ 24 * B * (11 * B) := Nat.mul_le_mul hW (by omega)
  have h4 : 2 * x + 6 ≤ 6 * B := by omega
  have h5 : B ≤ B ^ 3 := by
    rcases Nat.eq_zero_or_pos B with h | h
    · subst h; simp
    · exact Nat.le_self_pow (by norm_num) B
  have e1 : B * (25280 * B ^ 2) = 25280 * B ^ 3 := by ring
  have e2 : 24 * B * (11 * B) = 264 * B ^ 2 := by ring
  have h6 : B ^ 2 ≤ B ^ 3 := by
    rcases Nat.eq_zero_or_pos B with h | h
    · subst h; simp
    · exact Nat.pow_le_pow_right h (by norm_num)
  have h7 : B ^ 3 ≤ B ^ 4 := by
    rcases Nat.eq_zero_or_pos B with h | h
    · subst h; simp
    · exact Nat.pow_le_pow_right h (by norm_num)
  omega

lemma bd_stepBCost_le {W K WL B : ℕ} (hW : W ≤ 24 * B) (hK : K + 7 ≤ B) (hWL : WL ≤ B) :
    dsStepBCost W K WL ≤ 25280 * B ^ 4 + 270 * B ^ 3 := by
  unfold dsStepBCost
  have h1 := bd_tblC_le (by omega) hW
  have h2 : (K + 7) * tblC W W ≤ B * (25280 * B ^ 2) := Nat.mul_le_mul hK h1
  have e1 : B * (25280 * B ^ 2) = 25280 * B ^ 3 := by ring
  have h5 : B ≤ B ^ 3 := by
    rcases Nat.eq_zero_or_pos B with h | h
    · subst h; simp
    · exact Nat.le_self_pow (by norm_num) B
  have h7 : B ^ 3 ≤ B ^ 4 := by
    rcases Nat.eq_zero_or_pos B with h | h
    · subst h; simp
    · exact Nat.pow_le_pow_right h (by norm_num)
  omega

/-- `2 ^ size (2 m) ≤ 4 m` for `1 ≤ m`. -/
lemma bd_topN_le {m : ℕ} (hm : 1 ≤ m) : dsTopN m ≤ 4 * m := by
  unfold dsTopN
  have h1 : 1 ≤ Nat.size (2 * m) := Nat.lt_size.2 (by rw [pow_zero]; omega)
  have h2 : 2 ^ (Nat.size (2 * m) - 1) ≤ 2 * m := Nat.lt_size.1 (by omega)
  have h3 : 2 ^ Nat.size (2 * m) = 2 * 2 ^ (Nat.size (2 * m) - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

lemma bd_size_le (x : ℕ) : Nat.size x ≤ x := Nat.size_le.2 Nat.lt_two_pow_self

/-- **The cost of `bdRnd`**: eventually `bdRndCost n ≤ 2 · 10^13 (b n + 1)^4`. -/
theorem bd_rndCost_le : ∀ᶠ n in atTop, bdRndCost n ≤ 2 * 10 ^ 13 * (b n + 1) ^ 4 := by
  filter_upwards [eventually_big] with n hbig
  have hn := hbig.1
  obtain ⟨hg, hℓ, hlT, hℓT, hW, hWW, h200⟩ := ds_wid_bounds hn
  have hsz : Nat.size n ≤ b n + 1 := pm_size_le
  have hb := hbig.sixteen_le_b
  have hlT1 := hbig.one_le_logT
  set B := 100 * (b n + 1) with hB
  have hpm : pmW n ≤ 24 * B := by unfold pmW; omega
  have hMw := bdMw_le hn
  have hMw1 : 1 ≤ bdMw n := by unfold bdMw; omega
  have hTop : dsTopN (bdMw n) ≤ 4 * bdMw n := bd_topN_le hMw1
  have hTopK : bdTopK n ≤ 6 * bdMw n + 24 := by
    unfold bdTopK dsTopK
    have := bd_size_le (2 * bdMw n)
    omega
  have hWo : bdWo n ≤ 4 * b n + 10 := by unfold bdWo; omega
  have c1 := bd_stepCost_le (K := 6) (x := dsW n) hpm (by omega) (by omega)
  have c3 := bd_stepCost_le (K := 8) (x := bdMw n) hpm (by omega) (by omega)
  have c4 := bd_stepCost_le (K := bdTopK n) (x := dsTopN (bdMw n)) hpm (by omega) (by omega)
  have c5 := bd_stepBCost_le (K := 1) (WL := bdMw n) hpm (by omega) (by omega)
  have c6 := bd_stepCost_le (K := 9) (x := bdWo n) hpm (by omega) (by omega)
  have hB4 : B ^ 4 = 10 ^ 8 * (b n + 1) ^ 4 := by rw [hB]; ring
  have hB3 : B ^ 3 ≤ B ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  unfold bdRndCost
  omega

end Cost

end

end IntegerMultBounds.MathlibTM2.Fast.Main
