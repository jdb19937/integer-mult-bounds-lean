module

import IntegerMultBounds.MathlibTM2.Fast.CRTDirectMachineSetup
public import IntegerMultBounds.MathlibTM2.Fast.CRTDirectMachineFull
public import IntegerMultBounds.MathlibTM2.Fast.CRTDirectSetup
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! # Legacy entry and cleanup for the direct CRT machine -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q A : ℕ} {U F : Type} {body : F → Pr F T Q A U}

/-- Prepare runtime controls, execute the data transform, then release controls. -/
def crtDirectEntryWrap (rg : TblR 10 → Fin T) (e : Fin 40 → Fin T)
    (p : Pr F T Q A U) : Pr F T Q A U :=
  .seq (crtDirectSetup rg e) (.seq p (crtDirectSetupClear rg e))

/-- Composition helper; concrete forward and inverse entry theorems discharge
its middle-program execution premise. -/
theorem crtDirectEntryWrap_runs {d : ℕ}
    (rg : TblR 10 → Fin T) (e : Fin 40 → Fin T)
    (he : Function.Injective e) (hwr : ∀ j, rg .wr ≠ e j)
    (R : Regs T A) (a s : Fin (d + 1) → ℕ)
    (hw : R (e 31) = crtEnts ((crtRevAx (d + 1)).map a))
    (hs : R (e 32) = crtEnts ((crtRevAx (d + 1)).map s))
    (htotal : (R (e 8)).length = crtPre a (d + 1))
    (hz : ∀ j ∈ ([1, 2, 5, 12, 19, 20, 21, 39] : List (Fin 40)), R (e j) = [])
    (hbank : R (rg .wr) = []) (p : Pr F T Q A U) (data : List (Fin (A + 4))) (cost : ℕ)
    (hp : crtRuns body p (crtDirectSetupResult rg e R a s)
      (Function.update (crtDirectSetupResult rg e R a s) (e 0) data) cost) :
    crtRuns body (crtDirectEntryWrap rg e p) R (Function.update R (e 0) data)
      (crtDirectSetupCost (R (e 31)).length (R (e 32)).length (a 0)
        (crtPre a (d + 1)) (R (e 11)).length +
        (cost + crtDirectSetupClearCost a s (R (e 11)).length)) := by
  let R' := Function.update R (e 0) data
  have hz' : ∀ j ∈ ([1, 2, 5, 12, 39] : List (Fin 40)), R' (e j) = [] := by
    intro j hj
    have hj0 : j ≠ 0 := by intro h; subst j; norm_num at hj
    have hj' : j ∈ ([1, 2, 5, 12, 19, 20, 21, 39] : List (Fin 40)) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢
      tauto
    simpa [R', Function.update_of_ne (he.ne hj0)] using hz j hj'
  have hclear := crtDirectSetupClear_runs (body := body) rg e he hwr R' a s hz'
    (by simpa [R', Function.update_of_ne (hwr 0)] using hbank)
  have hclear' : crtRuns body (crtDirectSetupClear rg e)
      (Function.update (crtDirectSetupResult rg e R a s) (e 0) data) R'
      (crtDirectSetupClearCost a s (R (e 11)).length) := by
    simpa [R', crtDirectSetupResult_update_data rg e he hwr, he.eq_iff] using hclear
  exact crtRuns_seq (crtDirectSetup_legacy_runs rg e he hwr R a s hw hs htotal hz hbank)
    (crtRuns_seq hp hclear')


structure CrtDirectEntryInputs {d : ℕ} (rg : TblR 10 → Fin T) (e : Fin 40 → Fin T)
    (ι : Fin (swapT 6) → Fin T) (R : Regs T A) (a s m : Fin d → ℕ) (c : ℕ) : Prop where
  widths : R (e 31) = crtEnts ((crtRevAx d).map a)
  moduli : R (e 32) = crtEnts ((crtRevAx d).map s)
  multipliers : R (e 33) = crtEnts ((crtRevAx d).map m)
  sig : R (e 38) = binSyms (crtPre a d) (crtSig a s d)
  mask : R (e 8) = binSyms (crtPre a d) (crtMask a d)
  slot : (R (e 11)).length = c
  empty : ∀ j : Fin 40, j ∉ ([0, 8, 11, 31, 32, 33, 38] : List (Fin 40)) → R (e j) = []
  bank : ∀ q, R (rg q) = []
  swap : ∀ j, R (ι j) = []

lemma crtDirectEntry_stream_length {d A : ℕ} (a : Fin d → ℕ) :
    (crtEnts (A := A) ((crtRevAx d).map a)).length = crtPre a d + 2 * d := by
  rw [crtDirectEntriesLength]
  change crtW a (crtRevAx d) + 2 * (((crtRevAx d).map a).length) = _
  rw [crtW_revAx a d le_rfl]
  simp [crtRevAx]

noncomputable section
variable {K : ℕ} {bodyC : F → Pr F T Q (prime + K) U}

def crtDirectEntryCost {d : ℕ} (fwd : Bool) (T c : ℕ) (a s m : Fin (d + 1) → ℕ) : ℕ :=
  crtDirectSetupCost (crtPre a (d + 1) + 2 * (d + 1))
    (crtPre s (d + 1) + 2 * (d + 1)) (a 0) (crtPre a (d + 1)) c +
    ((if fwd then crtDirectMachineFullForwardCost (K := K) T (crtPre a (d + 1)) 0 c a s m
      else crtDirectMachineFullInverseCost (K := K) T (crtPre a (d + 1)) 0 c a s m) +
      crtDirectSetupClearCost a s c)

def crtDirectEntryForward
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (rg : TblR 10 → Fin T) (e : Fin 40 → Fin T) : Pr F T Q (prime + K) U :=
  crtDirectEntryWrap rg e (crtDirectMachineFullForward hQ ι hι hT rg e)

def crtDirectEntryInverse
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (rg : TblR 10 → Fin T) (e : Fin 40 → Fin T) : Pr F T Q (prime + K) U :=
  crtDirectEntryWrap rg e (crtDirectMachineFullInverse hQ ι hι hT rg e)

theorem crtDirectEntryForward_runs
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (rg : TblR 10 → Fin T) (hrg : Function.Injective rg)
    (e : Fin 40 → Fin T) (he : Function.Injective e)
    (hrge : ∀ r j, rg r ≠ e j) (hιe : ∀ j k, ι j ≠ e k) (hιrg : ∀ j q, ι j ≠ rg q)
    {d : ℕ} (a s m : Fin (d + 1) → ℕ)
    (hadj : ∀ j k, a j ≤ a k + 1) (hs : ∀ j, 0 < s j ∧ s j < 2 ^ a j)
    (hm : ∀ j, m j ≤ s j) (hd : d + 1 ≤ crtPre a (d + 1))
    (c : ℕ) (hc : 0 < c) (R : Regs T (prime + K))
    (hI : CrtDirectEntryInputs rg e ι R a s m c)
    (l : List (List (Fin (prime + K + 4)))) (z : List (Fin (prime + K + 4)))
    (hl : l.length = crtProd s (d + 1)) (hlc : ∀ x ∈ l, x.length = c) (hzc : z.length = c)
    (hl8 : ∀ x ∈ l, ∀ b ∈ x, b.val < 8) (hz8 : ∀ b ∈ z, b.val < 8)
    (hstr : R (e 0) = l.flatten) (hzr : R (e 11) = z) :
    crtRuns bodyC (crtDirectEntryForward hQ ι hι hT rg e) R
      (Function.update R (e 0) (crtBox a (List.finRange (d + 1)) (crtFwdC s m (crtPadC s l z) (d + 1)) 0).flatten)
      (crtDirectEntryCost (K := K) true T c a s m) := by
  let S := crtDirectSetupResult rg e R a s
  have hrev : ∀ j q, e j ≠ rg q := fun j q => (hrge q j).symm
  have hz : ∀ j ∈ ([1, 2, 5, 12, 19, 20, 21, 39] : List (Fin 40)), R (e j) = [] := by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hI.empty _ (by decide)
  have htotal : (R (e 8)).length = crtPre a (d + 1) := by simp [hI.mask, binSyms]
  have hready := crtDirectSetupResult_ready rg hrg e he hrge R a s c htotal hI.slot
    (fun j hj hj' => hI.empty j (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      intro h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at *)) hI.bank
  have hoff (j : Fin 40) (hj : j ∉ ([1, 2, 5, 12, 39] : List (Fin 40))) : S (e j) = R (e j) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    exact crtDirectSetupResult_off rg e R a s (e j) (he.ne hj.1) (he.ne hj.2.1)
      (he.ne hj.2.2.1) (he.ne hj.2.2.2.2) (he.ne hj.2.2.2.1) (hrev j .wr)
  have hswap : ∀ j, S (ι j) = [] := by
    intro j
    simp [S, crtDirectSetupResult, hιe, hιrg, hI.swap]
  have hscratch : ∀ j ∈ ([3, 4, 6, 7, 9, 10, 34, 35, 36, 37] : List (Fin 40)), S (e j) = [] := by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [hoff _ (by decide)]; exact hI.empty _ (by decide)
  have hsum : (∑ j, a j) ≤ crtPre a (d + 1) := by
    simp [crtPre, crtLow_of_le le_rfl]
  have hfull := crtDirectMachineFullForward_runs (body := bodyC) hQ ι hι hT rg hrg e he hrge hιe a s m hadj hs hm hsum hd c hc
    (List.replicate (3 * crtPre a (d + 1) + 1) tick) [] (by simp) rfl (Nat.zero_le _) S hready hswap
    (by rw [hoff _ (by decide)]; exact hI.widths)
    (by rw [hoff _ (by decide)]; exact hI.moduli)
    (by rw [hoff _ (by decide)]; exact hI.multipliers) hscratch
    (by simp [S, crtDirectSetupResult, he.eq_iff, hrev])
    (by rw [hoff _ (by decide)]; exact hI.sig)
    (by rw [hoff _ (by decide)]; exact hI.mask) l z hl hlc hzc hl8 hz8
    (by rw [hoff _ (by decide)]; exact hstr) (by rw [hoff _ (by decide)]; exact hzr)
  have h := crtDirectEntryWrap_runs (body := bodyC) rg e he (hrge .wr) R a s
    hI.widths hI.moduli htotal hz (hI.bank .wr) _ _ _ hfull
  simpa [crtDirectEntryForward, crtDirectEntryCost, hI.widths, hI.moduli, hI.slot,
    crtDirectEntry_stream_length] using h

theorem crtDirectEntryInverse_runs
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (rg : TblR 10 → Fin T) (hrg : Function.Injective rg)
    (e : Fin 40 → Fin T) (he : Function.Injective e)
    (hrge : ∀ r j, rg r ≠ e j) (hιe : ∀ j k, ι j ≠ e k) (hιrg : ∀ j q, ι j ≠ rg q)
    {d : ℕ} (a s m : Fin (d + 1) → ℕ)
    (hadj : ∀ j k, a j ≤ a k + 1) (hs : ∀ j, 0 < s j ∧ s j < 2 ^ a j)
    (hm : ∀ j, m j ≤ s j) (hd : d + 1 ≤ crtPre a (d + 1))
    (c : ℕ) (hc : 0 < c) (R : Regs T (prime + K))
    (hI : CrtDirectEntryInputs rg e ι R a s m c)
    (C : (Fin (d + 1) → ℕ) → List (Fin (prime + K + 4)))
    (hC : ∀ x, (C x).length = c) (h8 : ∀ x, ∀ b ∈ C x, b.val < 8)
    (hstr : R (e 0) = (crtBox a (List.finRange (d + 1)) C 0).flatten) :
    crtRuns bodyC (crtDirectEntryInverse hQ ι hι hT rg e) R
      (Function.update R (e 0) ((List.range (crtProd s (d + 1))).map fun k => crtInvC s m C (d + 1) (crtUnrank s k)).flatten)
      (crtDirectEntryCost (K := K) false T c a s m) := by
  let S := crtDirectSetupResult rg e R a s
  have hrev : ∀ j q, e j ≠ rg q := fun j q => (hrge q j).symm
  have hz : ∀ j ∈ ([1, 2, 5, 12, 19, 20, 21, 39] : List (Fin 40)), R (e j) = [] := by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hI.empty _ (by decide)
  have htotal : (R (e 8)).length = crtPre a (d + 1) := by simp [hI.mask, binSyms]
  have hready := crtDirectSetupResult_ready rg hrg e he hrge R a s c htotal hI.slot
    (fun j hj hj' => hI.empty j (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      intro h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at *)) hI.bank
  have hoff (j : Fin 40) (hj : j ∉ ([1, 2, 5, 12, 39] : List (Fin 40))) : S (e j) = R (e j) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    exact crtDirectSetupResult_off rg e R a s (e j) (he.ne hj.1) (he.ne hj.2.1)
      (he.ne hj.2.2.1) (he.ne hj.2.2.2.2) (he.ne hj.2.2.2.1) (hrev j .wr)
  have hswap : ∀ j, S (ι j) = [] := by
    intro j
    simp [S, crtDirectSetupResult, hιe, hιrg, hI.swap]
  have hscratch : ∀ j ∈ ([3, 4, 6, 7, 9, 10, 34, 35, 36, 37] : List (Fin 40)), S (e j) = [] := by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [hoff _ (by decide)]; exact hI.empty _ (by decide)
  have hsum : (∑ j, a j) ≤ crtPre a (d + 1) := by
    simp [crtPre, crtLow_of_le le_rfl]
  have hfull := crtDirectMachineFullInverse_runs (body := bodyC) hQ ι hι hT rg hrg e he hrge hιe a s m hadj hs hm hsum hd c hc
    (List.replicate (3 * crtPre a (d + 1) + 1) tick) [] (by simp) rfl (Nat.zero_le _) S hready hswap
    (by rw [hoff _ (by decide)]; exact hI.widths)
    (by rw [hoff _ (by decide)]; exact hI.moduli)
    (by rw [hoff _ (by decide)]; exact hI.multipliers) hscratch
    (by simp [S, crtDirectSetupResult, he.eq_iff, hrev])
    (by rw [hoff _ (by decide)]; exact hI.sig)
    (by rw [hoff _ (by decide)]; exact hI.mask) C hC h8 (by rw [hoff _ (by decide)]; exact hstr)
  have h := crtDirectEntryWrap_runs (body := bodyC) rg e he (hrge .wr) R a s
    hI.widths hI.moduli htotal hz (hI.bank .wr) _ _ _ hfull
  simpa [crtDirectEntryInverse, crtDirectEntryCost, hI.widths, hI.moduli, hI.slot,
    crtDirectEntry_stream_length] using h

end
end IntegerMultBounds.MathlibTM2.Fast
