module

public import IntegerMultBounds.MathlibTM2.Fast.CRTDirectMachine
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! # The concrete direct CRT driver -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {T Q K : ℕ} {U F : Type} {body : F → Pr F T Q (prime + K) U}

def crtDirectMachineForwardCore
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (rg : TblR 10 → Fin T) (e : Fin 38 → Fin T) (axes width : Fin T) : Pr F T Q (prime + K) U :=
  let r := e ∘ crtDirectMachineDriver
  let p := crtControlTarget hQ ι hι hT rg (e ∘ crtDirectMachineTarget) true
  .seq (crtDirectMachineForwardInit r axes width) (.seq (crtWhile (r .wT) (crtDirectStep true r p)) (crtDirectRestore r))

theorem crtDirectMachineForwardCore_runs
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (rg : TblR 10 → Fin T) (hrg : Function.Injective rg)
    (e : Fin 38 → Fin T) (he : Function.Injective e)
    (hrge : ∀ r j, rg r ≠ e j) (hιe : ∀ j k, ι j ≠ e k)
    {d B w : ℕ} (a s m : Fin (d + 1) → ℕ)
    (hadj : ∀ j k, a j ≤ a k + 1) (hs : ∀ j, 0 < s j ∧ s j ≤ 2 ^ a j)
    (hm : ∀ j, m j ≤ s j) (hB : (∑ j, a j) ≤ B) (hd : d + 1 ≤ B)
    (c : ℕ) (hc : 0 < c) (wl nl : List (Fin (prime + K + 4)))
    (hwl : wl.length = 3 * B + 1) (hnl : nl.length = w) (hw : w ≤ 3 * B + 1)
    (R : Regs T (prime + K)) (hR : CrtDirectMachineReady rg e a s c wl nl R)
    (hι0 : ∀ j, R (ι j) = []) (C : (Fin (d + 1) → ℕ) → List (Fin (prime + K + 4)))
    (hC : ∀ x, (C x).length = c) (h8 : ∀ x, ∀ z ∈ C x, z.val < 8)
    (axes width : Fin T)
    (ha : ∀ q, axes ≠ (e ∘ crtDirectMachineDriver) q)
    (hwidth : ∀ q, width ≠ (e ∘ crtDirectMachineDriver) q)
    (haxes : (R axes).length = d + 1) (htotal : (R width).length = crtPre a (d + 1))
    (hwt : R ((e ∘ crtDirectMachineDriver) .wT) = crtEnts ((crtRevAx (d + 1)).map a))
    (hst : R ((e ∘ crtDirectMachineDriver) .sT) = crtEnts ((crtRevAx (d + 1)).map s))
    (hmt : R ((e ∘ crtDirectMachineDriver) .mT) = crtEnts ((crtRevAx (d + 1)).map m))
    (hz : ∀ q ∈ [CrtDirectReg.wD, .sD, .mD, .lower, .upper, .index, .tmp, .aI, .sI, .muI],
      R ((e ∘ crtDirectMachineDriver) q) = [])
    (hstr : R ((e ∘ crtDirectMachineDriver) .str) = (crtBox a (crtRevAx (d + 1)) C 0).flatten) :
    crtRuns body (crtDirectMachineForwardCore hQ ι hι hT rg e axes width) R
      (Function.update R ((e ∘ crtDirectMachineDriver) .str)
        (crtBox a (crtRevAx (d + 1)) (crtFwdC s m C (d + 1)) 0).flatten)
      ((4 * (d + 1) + 4 * crtPre a (d + 1) + 8) + crtDirectMachineLoopCost (K := K) T B w c a s m +
        (2 * ((crtEnts (A := prime + K) ((List.finRange (d + 1)).map a)).length +
          (crtEnts (A := prime + K) ((List.finRange (d + 1)).map s)).length +
          (crtEnts (A := prime + K) ((List.finRange (d + 1)).map m)).length + crtW a (List.finRange (d + 1))) + 10)) := by
  let r := e ∘ crtDirectMachineDriver
  have hr := he.comp crtDirectMachineDriver_injective
  have hinit := crtDirectMachineForwardInit_runs (body := body) a s m r hr axes width ha hwidth R haxes htotal hwt hst hmt
    (by intro q hq; exact hz q (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢; tauto))
  rw [hstr] at hinit
  have hloop := crtDirectMachineForwardLoop_runs (body := body) hQ ι hι hT rg hrg e he hrge hιe a s m hadj hs hm hB hd
    c hc wl nl hwl hnl hw R hR hι0 C hC h8
    (by intro q hq; exact hz q (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢; tauto))
  have hclean := crtDirectRestore_runs (body := body) a s m hr R
    (crtBox a (crtRevAx (d + 1)) (crtFwdC s m C (d + 1)) 0).flatten hwt hst hmt
    (by intro q hq; exact hz q (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢; tauto))
  exact crtRuns_mono (crtRuns_seq hinit (crtRuns_seq hloop hclean)) (by omega)

def crtDirectMachineInverseCore
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (rg : TblR 10 → Fin T) (e : Fin 38 → Fin T) (_axes width : Fin T) : Pr F T Q (prime + K) U :=
  let r := e ∘ crtDirectMachineDriver
  let p := crtControlTarget hQ ι hι hT rg (e ∘ crtDirectMachineTarget) false
  .seq (crtDirectMachineInverseInit r width) (.seq (crtWhile (r .wD) (crtDirectStep false r p)) (crtDirectInverseCleanup r))

theorem crtDirectMachineInverseCore_runs
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (rg : TblR 10 → Fin T) (hrg : Function.Injective rg)
    (e : Fin 38 → Fin T) (he : Function.Injective e)
    (hrge : ∀ r j, rg r ≠ e j) (hιe : ∀ j k, ι j ≠ e k)
    {d B w : ℕ} (a s m : Fin (d + 1) → ℕ)
    (hadj : ∀ j k, a j ≤ a k + 1) (hs : ∀ j, 0 < s j ∧ s j ≤ 2 ^ a j)
    (hm : ∀ j, m j ≤ s j) (hB : (∑ j, a j) ≤ B) (hd : d + 1 ≤ B)
    (c : ℕ) (hc : 0 < c) (wl nl : List (Fin (prime + K + 4)))
    (hwl : wl.length = 3 * B + 1) (hnl : nl.length = w) (hw : w ≤ 3 * B + 1)
    (R : Regs T (prime + K)) (hR : CrtDirectMachineReady rg e a s c wl nl R)
    (hι0 : ∀ j, R (ι j) = []) (C : (Fin (d + 1) → ℕ) → List (Fin (prime + K + 4)))
    (hC : ∀ x, (C x).length = c) (h8 : ∀ x, ∀ z ∈ C x, z.val < 8)
    (axes width : Fin T)
    (_ha : ∀ q, axes ≠ (e ∘ crtDirectMachineDriver) q)
    (hwidth : ∀ q, width ≠ (e ∘ crtDirectMachineDriver) q)
    (_haxes : (R axes).length = d + 1) (htotal : (R width).length = crtPre a (d + 1))
    (hwt : R ((e ∘ crtDirectMachineDriver) .wT) = crtEnts ((crtRevAx (d + 1)).map a))
    (hst : R ((e ∘ crtDirectMachineDriver) .sT) = crtEnts ((crtRevAx (d + 1)).map s))
    (hmt : R ((e ∘ crtDirectMachineDriver) .mT) = crtEnts ((crtRevAx (d + 1)).map m))
    (hz : ∀ q ∈ [CrtDirectReg.wD, .sD, .mD, .lower, .upper, .index, .tmp, .aI, .sI, .muI],
      R ((e ∘ crtDirectMachineDriver) q) = [])
    (hstr : R ((e ∘ crtDirectMachineDriver) .str) = (crtBox a (crtRevAx (d + 1)) C 0).flatten) :
    crtRuns body (crtDirectMachineInverseCore hQ ι hι hT rg e axes width) R
      (Function.update R ((e ∘ crtDirectMachineDriver) .str)
        (crtBox a (crtRevAx (d + 1)) (crtInvC s m C (d + 1)) 0).flatten)
      ((4 * crtPre a (d + 1) + 2 * ((crtEnts (A := prime + K) ((crtRevAx (d + 1)).map a)).length +
          (crtEnts (A := prime + K) ((crtRevAx (d + 1)).map s)).length +
          (crtEnts (A := prime + K) ((crtRevAx (d + 1)).map m)).length) + 10) +
        crtDirectMachineLoopCost (K := K) T B w c a s m + (2 * crtPre a (d + 1) + 2 * (d + 1) + 4)) := by
  let r := e ∘ crtDirectMachineDriver
  have hr := he.comp crtDirectMachineDriver_injective
  have hinit := crtDirectMachineInverseInit_runs (body := body) a s m r hr width hwidth R htotal hwt hst hmt
    (by intro q hq; exact hz q (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢; tauto))
  rw [hstr] at hinit
  have hloop := crtDirectMachineInverseLoop_runs (body := body) hQ ι hι hT rg hrg e he hrge hιe a s m hadj hs hm hB hd
    c hc wl nl hwl hnl hw R hR hι0 C hC h8
    (by intro q hq; exact hz q (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢; tauto))
  have hclean := crtDirectInverseCleanup_runs (body := body) a s m hr R
    (crtBox a (crtRevAx (d + 1)) (crtInvC s m C (d + 1)) 0).flatten hwt hst hmt
    (by intro q hq; exact hz q (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢; tauto))
  exact crtRuns_mono (crtRuns_seq hinit (crtRuns_seq hloop hclean)) (by omega)

end
end IntegerMultBounds.MathlibTM2.Fast
