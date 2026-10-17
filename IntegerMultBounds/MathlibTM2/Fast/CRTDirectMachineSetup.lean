module

public import IntegerMultBounds.MathlibTM2.Fast.CRTDirectMachine
public import IntegerMultBounds.MathlibTM2.Fast.CRTDirectSetup
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! # Runtime setup supplies the direct machine contract -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {T A K : ℕ}

/-- Setup builds every immutable input and leaves the returned workspaces empty. -/
theorem crtDirectSetupResult_ready {d : ℕ}
    (rg : TblR 10 → Fin T) (hrg : Function.Injective rg)
    (e : Fin 40 → Fin T) (he : Function.Injective e)
    (hrge : ∀ r j, rg r ≠ e j)
    (R : Regs T (prime + K)) (a s : Fin (d + 1) → ℕ) (c : ℕ)
    (htotal : (R (e 8)).length = crtPre a (d + 1))
    (hslot : (R (e 11)).length = c)
    (hempty : ∀ j : Fin 40, 13 ≤ j.val → j.val ≤ 30 → R (e j) = [])
    (hbank : ∀ r, R (rg r) = []) :
    CrtDirectMachineReady rg (e ∘ crtDirectMachineCore) a s c
      (List.replicate (3 * crtPre a (d + 1) + 1) tick) []
      (crtDirectSetupResult rg e R a s) := by
  have hrev : ∀ j r, e j ≠ rg r := fun j r => (hrge r j).symm
  constructor
  · simp [crtDirectSetupResult, crtDirectMachineCore, he.eq_iff, hrev]
  · simp [crtDirectSetupResult, crtDirectMachineCore, he.eq_iff, hrev]
  · simp [crtDirectSetupResult, crtDirectMachineCore, he.eq_iff, hrev]
  · simpa [crtDirectSetupResult, crtDirectMachineCore, he.eq_iff, hrev] using htotal
  · simpa [crtDirectSetupResult, crtDirectMachineCore, he.eq_iff, hrev] using hslot
  · simp [crtDirectSetupResult, crtDirectMachineCore, hrev, hslot]
  · intro j hj hj'
    have hj1 : crtDirectMachineCore j ≠ 1 := by intro h; have := congrArg Fin.val h; simp [crtDirectMachineCore] at this; omega
    have hj2 : crtDirectMachineCore j ≠ 2 := by intro h; have := congrArg Fin.val h; simp [crtDirectMachineCore] at this; omega
    have hj5 : crtDirectMachineCore j ≠ 5 := by intro h; have := congrArg Fin.val h; simp [crtDirectMachineCore] at this; omega
    have hj12 : crtDirectMachineCore j ≠ 12 := by intro h; have := congrArg Fin.val h; simp [crtDirectMachineCore] at this; omega
    have hj39 : crtDirectMachineCore j ≠ 39 := by intro h; have := congrArg Fin.val h; simp [crtDirectMachineCore] at this; omega
    simpa [crtDirectSetupResult, he.eq_iff, hrev, hj1, hj2, hj5, hj12, hj39]
      using hempty (crtDirectMachineCore j) hj hj'
  · simp [crtDirectSetupResult]
  · simp [crtDirectSetupResult, hrg.eq_iff, hrge, hbank]
  · intro j; simp [crtDirectSetupResult, hrg.eq_iff, hrge, hbank]
  · intro j; simp [crtDirectSetupResult, hrg.eq_iff, hrge, hbank]
  · simp [crtDirectSetupResult, hrg.eq_iff, hrge, hbank]

/-- Changing only data commutes with setup, enabling exact legacy cleanup. -/
theorem crtDirectSetupResult_update_data {d : ℕ}
    (rg : TblR 10 → Fin T) (e : Fin 40 → Fin T)
    (he : Function.Injective e) (hwr : ∀ j, rg .wr ≠ e j)
    (R : Regs T A) (a s : Fin (d + 1) → ℕ) (data : List (Fin (A + 4))) :
    crtDirectSetupResult rg e (Function.update R (e 0) data) a s =
      Function.update (crtDirectSetupResult rg e R a s) (e 0) data := by
  funext r
  by_cases hr : r = e 0
  · subst r
    simp [crtDirectSetupResult, he.eq_iff, fun j => (hwr j).symm]
  · simp only [Function.update_of_ne hr]
    simp [crtDirectSetupResult, he.eq_iff, Function.update_apply, hr]

end
end IntegerMultBounds.MathlibTM2.Fast
