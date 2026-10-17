module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlWorkspace
public import IntegerMultBounds.MathlibTM2.Fast.CRTControlGenerateLoop
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-! # Runtime provisioning for the CRT descriptor generator

Powers are constructed directly as binary words from unary bit widths. No
unary tape proportional to a power of two is allocated.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Replace one generator variable by a power of two. -/
def crtControlBankPow2 (rg : TblR 10 → Fin T) (exponent : Fin T) (j : Fin 10) :
    Pr P T Q A U :=
  .seq (uclear (rg (.v j)))
    (crtControlPow2 (rg .wr) exponent (rg (.v j)) (rg (.z 0)) (rg (.z 1)))

theorem crtControlBankPow2_runs {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg) (exponent : Fin T)
    (hexp : ∀ r, rg r ≠ exponent) (j : Fin 10)
    {W e : ℕ} (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (heW : e < W)
    (st : TblSt 10 A) (R : Regs T A)
    (hR : ∀ r, R (rg r) = tblRho W wl nl st r) (he : (R exponent).length = e) :
    crtRuns body (crtControlBankPow2 rg exponent j) R
      (crtBankOverlay rg R (tblRho W wl nl ⟨Function.update st.val j (2 ^ e), st.acc⟩))
      (12 * W + 8 * e + 26) := by
  have hc := crtClear_runs (body := body) (rg (.v j)) R
  let R₁ := Function.update R (rg (.v j)) []
  have hp := crtControlPow2_runs (body := body)
    (width := rg .wr) (exponent := exponent) (dst := rg (.v j))
    (pad := rg (.z 0)) (tmp := rg (.z 1))
    (by simp [List.nodup_cons, hrg.eq_iff, hexp, Ne.symm (hexp (.v j)),
      Ne.symm (hexp (.z 0)), Ne.symm (hexp (.z 1))]) R₁ W e
    (by simp [R₁, hrg.eq_iff, hR, tblRho, hwl])
    (by simp [R₁, Ne.symm (hexp (.v j)), he]) heW (by simp [R₁])
    (by simp [R₁, hrg.eq_iff, hR, tblRho])
    (by simp [R₁, hrg.eq_iff, hR, tblRho])
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq hc hp) ?_) ?_
  · funext k
    by_cases hk : ∃ r, rg r = k
    · obtain ⟨r, rfl⟩ := hk
      rw [crtBankOverlay_on hrg]
      cases r with
      | v k =>
        by_cases hkj : k = j <;> simp [R₁, hrg.eq_iff, hR, tblRho, hkj]
      | wr => simp [R₁, hrg.eq_iff, hR, tblRho]
      | wn => simp [R₁, hrg.eq_iff, hR, tblRho]
      | acc => simp [R₁, hrg.eq_iff, hR, tblRho]
      | z k => simp [R₁, hrg.eq_iff, hR, tblRho]
    · have hk' : ∀ r, rg r ≠ k := by simpa using hk
      simp [R₁, Function.update_of_ne (hk' (.v j)).symm,
        crtBankOverlay_off _ _ _ _ hk']
  · simp [hR, tblRho, length_binSyms]; omega

/-- Initial traversal state before target constants are installed. -/
def crtControlGenerateInitial (acc : List (Fin (A + 4))) : TblSt 10 A :=
  ⟨fun j => if j = 2 ∨ j = 6 then 1 else 0, acc⟩

def crtControlGenerateInit (rg : TblR 10 → Fin T) : Pr P T Q A U :=
  .seq (crtWorkspaceZeros rg (List.finRange 10))
    (tblCompile rg (.seq (.ins (.inc 2)) (.ins (.inc 6))))

theorem crtControlGenerateInit_runs {rg : TblR 10 → Fin T} (hrg : Function.Injective rg)
    {W w : ℕ} (hW : 0 < W) (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (R : Regs T A) (hwr : R (rg .wr) = wl) (hwn : R (rg .wn) = nl)
    (hv : ∀ i, R (rg (.v i)) = []) (hz : ∀ j, R (rg (.z j)) = []) :
    crtRuns body (crtControlGenerateInit rg) R
      (crtBankOverlay rg R (tblRho W wl nl (crtControlGenerateInitial (R (rg .acc)))))
      (10 * (4 * W + 4) + 1 + 2 * tblC W w) := by
  have hinit := crtWorkspaceZeros_runs (body := body) hrg (List.finRange 10)
    (List.nodup_finRange _) R (fun i _ => hv i) (hz 0)
  rw [hwr, hwl] at hinit
  let R₀ : Regs T A := fun k => if ∃ i : Fin 10, rg (.v i) = k then binSyms W 0 else R k
  have hinit' : crtRuns body (crtWorkspaceZeros rg (List.finRange 10)) R R₀
      (10 * (4 * W + 4) + 1) := by simpa [R₀] using hinit
  let st : TblSt 10 A := ⟨fun _ => 0, R (rg .acc)⟩
  have hR₀ : ∀ r, R₀ (rg r) = tblRho W wl nl st r := by
    intro r
    cases r <;> simp [R₀, hrg.eq_iff, tblRho, st, hwr, hwn, hz]
  have hst : ∀ j, st.val j < 2 ^ W := by intro j; dsimp [st]; positivity
  have hone : 1 < 2 ^ W := Nat.one_lt_two_pow hW.ne'
  have hdo : TblDo A W w (.seq (.ins (.inc 2)) (.ins (.inc 6))) st
      (fun s => s = crtControlGenerateInitial st.acc) 2 := by
    apply TblDo.block [.inc 2] (.inc 6)
    · simp [tblFitsList, TblIns.fits, TblIns.exact, st, hone]
    · simp only [List.cons_append, List.nil_append, tblExactList, TblIns.exact]
      congr 1
      funext j
      fin_cases j <;> simp [st]
  obtain ⟨st', hs, hr⟩ := hdo.host (body := body) hrg wl nl hwl hnl hw hst
  subst st'
  have hrun := crtRuns_of_tbl hrg hr R₀ hR₀
  refine crtRuns_congr (crtRuns_seq hinit' hrun) ?_
  funext k
  by_cases hk : ∃ r, rg r = k
  · obtain ⟨r, rfl⟩ := hk
    simp [crtBankOverlay_on hrg, st]
  · have hk' : ∀ r, rg r ≠ k := by simpa using hk
    simp [crtBankOverlay_off _ _ _ _ hk', R₀, show ¬∃ i, rg (.v i) = k from by
      rintro ⟨i, hi⟩; exact hk' (.v i) hi]

/-- Complete provisioning from unary target index and three unary exponents. -/
def crtControlGenerateSetup (rg : TblR 10 → Fin T) (e : Fin 5 → Fin T) : Pr P T Q A U :=
  .seq (crtControlGenerateInit rg)
    (.seq (crtControlReadUnary rg (e 0) (e 4) 1)
      (.seq (crtControlBankPow2 rg (e 1) 3)
        (.seq (crtControlBankPow2 rg (e 2) 4) (crtControlBankPow2 rg (e 3) 9))))

def crtControlGenerateSetupState (i ai a0 lower : ℕ)
    (acc : List (Fin (A + 4))) : TblSt 10 A :=
  ⟨Function.update (Function.update (Function.update
    (Function.update (crtControlGenerateInitial acc).val 1 i) 3 (2 ^ ai)) 4 (2 ^ a0))
      9 (2 ^ lower), acc⟩

private lemma crtSetup_overlay_twice {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg) (R : Regs T A) (ρ σ : TblR 10 → List (Fin (A + 4))) :
    crtBankOverlay rg (crtBankOverlay rg R ρ) σ = crtBankOverlay rg R σ := by
  funext r
  by_cases hr : ∃ j, rg j = r
  · obtain ⟨j, rfl⟩ := hr; simp [crtBankOverlay_on hrg]
  · have h : ∀ j, rg j ≠ r := by simpa using hr
    simp [crtBankOverlay_off _ _ _ _ h]

/-- Exact provisioning budget, shared with the cost matcher. -/
def crtControlGenerateSetupCost (W w i ai a0 lower : ℕ) : ℕ :=
  (10 * (4 * W + 4) + 1 + 2 * tblC W w) +
    ((tblC W w + (i * (tblC W w + 3) + 2 * i + 4)) +
      ((12 * W + 8 * ai + 26) +
        ((12 * W + 8 * a0 + 26) + (12 * W + 8 * lower + 26))))

theorem crtControlGenerateSetup_runs {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg) (e : Fin 5 → Fin T) (he : Function.Injective e)
    (hrge : ∀ r j, rg r ≠ e j)
    {W w i ai a0 lower : ℕ} (hW : 0 < W) (hi : i < 2 ^ W)
    (hai : ai < W) (ha0 : a0 < W) (hlower : lower < W)
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (R : Regs T A) (hwr : R (rg .wr) = wl) (hwn : R (rg .wn) = nl)
    (hv : ∀ j, R (rg (.v j)) = []) (hz : ∀ j, R (rg (.z j)) = [])
    (hindex : (R (e 0)).length = i) (htarget : (R (e 1)).length = ai)
    (hzero : (R (e 2)).length = a0) (hlow : (R (e 3)).length = lower)
    (hsaved : R (e 4) = []) :
    crtRuns body (crtControlGenerateSetup rg e) R
      (crtBankOverlay rg R (tblRho W wl nl
        (crtControlGenerateSetupState i ai a0 lower (R (rg .acc)))))
      (crtControlGenerateSetupCost W w i ai a0 lower) := by
  let st₀ := crtControlGenerateInitial (R (rg .acc))
  let st₁ : TblSt 10 A := ⟨Function.update st₀.val 1 i, st₀.acc⟩
  let st₂ : TblSt 10 A := ⟨Function.update st₁.val 3 (2 ^ ai), st₁.acc⟩
  let st₃ : TblSt 10 A := ⟨Function.update st₂.val 4 (2 ^ a0), st₂.acc⟩
  let ρ := fun st : TblSt 10 A => crtBankOverlay rg R (tblRho W wl nl st)
  have hρ : ∀ st r, ρ st (rg r) = tblRho W wl nl st r :=
    fun st r => crtBankOverlay_on hrg _ _ r
  have hρe : ∀ st j, ρ st (e j) = R (e j) :=
    fun st j => crtBankOverlay_off _ _ _ _ (fun r => hrge r j)
  have hinit := crtControlGenerateInit_runs (body := body) hrg hW wl nl hwl hnl hw
    R hwr hwn hv hz
  have hfit : ∀ j, st₀.val j < 2 ^ W := by
    intro j
    simp only [st₀, crtControlGenerateInitial]
    split_ifs
    · exact Nat.one_lt_two_pow hW.ne'
    · positivity
  have hload := crtControlReadUnary_runs (body := body) hrg (e 0) (e 4)
    (he.ne (by decide)) (fun r => hrge r 0) (fun r => hrge r 4) 1
    wl nl hwl hnl hw st₀ hfit hi (ρ st₀) (hρ _)
    (by rw [hρe]; exact hindex) (by rw [hρe]; exact hsaved)
  have hpow₁ := crtControlBankPow2_runs (body := body) hrg (e 1) (fun r => hrge r 1)
    3 wl nl hwl hai st₁ (ρ st₁) (hρ _) (by rw [hρe]; exact htarget)
  have hpow₂ := crtControlBankPow2_runs (body := body) hrg (e 2) (fun r => hrge r 2)
    4 wl nl hwl ha0 st₂ (ρ st₂) (hρ _) (by rw [hρe]; exact hzero)
  have hpow₃ := crtControlBankPow2_runs (body := body) hrg (e 3) (fun r => hrge r 3)
    9 wl nl hwl hlower st₃ (ρ st₃) (hρ _) (by rw [hρe]; exact hlow)
  simp only [ρ, crtSetup_overlay_twice hrg] at hload hpow₁ hpow₂ hpow₃
  exact crtRuns_seq hinit (crtRuns_seq hload (crtRuns_seq hpow₁ (crtRuns_seq hpow₂ hpow₃)))

end IntegerMultBounds.MathlibTM2.Fast
