module

public import IntegerMultBounds.MathlibTM2.Node.CompactBasisRefreshPlacement
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! A blank refresh bank gives the same source view as the legacy placement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {A : ℕ}

private lemma compactBasisRefreshReg_off (x : LReg SXReg)
    (hx : ∀ i : Fin 7,x≠.wire (synWire (compactBasisOutputWire i))) :
    compactBasisRefreshReg (reg x)=compactLegacyReg (reg x) := by
  have h15 := hx 0; have h6 := hx 1; have h26 := hx 2; have h11 := hx 3
  have h16 := hx 4; have h18 := hx 5; have h19 := hx 6
  simp only [compactBasisOutputWire,Matrix.cons_val_zero] at h15 h6 h26 h11 h16 h18 h19
  cases x <;> simp_all [compactBasisRefreshReg_reg,compactLegacyReg,compactMapReg_reg,
    compactMapRegName,compactBasisRefreshPerm,Equiv.swap_apply_def]

/-- The refresh's seven redirected blank outputs agree with the blank synthetic output wires. -/
theorem compactBasisRefresh_input
    (Rbig : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (hlegacy : Rbig ∘ compactLegacyReg=synG R v)
    (hblank : ∀ i,Rbig (compactBasisRefreshDst i)=[])
    (hwire : ∀ i,v (compactBasisOutputWire i)=[]) :
    Rbig ∘ compactBasisRefreshReg=synG R v := by
  funext i
  obtain ⟨x,hx⟩ := (regEquiv SXReg).surjective i
  change reg x=i at hx
  subst i
  by_cases hout : ∃ j : Fin 7,x=.wire (synWire (compactBasisOutputWire j))
  · obtain ⟨j,rfl⟩ := hout
    change Rbig (compactBasisRefreshReg (sreg (compactBasisOutputWire j)))=
      synG R v (sreg (compactBasisOutputWire j))
    rw [compactBasisRefreshReg_output,synG_sreg,hwire]
    exact hblank j
  · have hoff : ∀ j : Fin 7,x≠.wire (synWire (compactBasisOutputWire j)) := by simpa using hout
    change Rbig (compactBasisRefreshReg (reg x))=synG R v (reg x)
    rw [compactBasisRefreshReg_off x hoff]
    exact congrFun hlegacy (reg x)

end
end IntegerMultBounds.MathlibTM2.LayerMachine
