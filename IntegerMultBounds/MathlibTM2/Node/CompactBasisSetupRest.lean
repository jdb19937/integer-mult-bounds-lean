module
public import IntegerMultBounds.MathlibTM2.Node.CompactBasisSetupFrame
public import IntegerMultBounds.MathlibTM2.Node.CompactLayerPlaced
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.ENatToNat


/-! Actual persistent compact bank setup, with original source words and all scratch restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open CompactGadgetReservationCapacity
open CompactGadgetReservationShape (Shape)
open IntegerMultBounds.MathlibTM2.Layer
noncomputable section
variable {Q A : ℕ} {U P : Type}

lemma compactSetupUpdate7_get {T : ℕ} (e : Fin 7 → Fin T) (he : Function.Injective e)
    (R : Fin T → List (Fin (A+4))) (values : Fin 7 → ℕ) (i : Fin 7) :
    compactSetupUpdate7 R e values (e i)=List.replicate (values i) tick := by
  fin_cases i <;> simp [compactSetupUpdate7,he.eq_iff]

lemma compactSetupUpdate7_off {T : ℕ} (e : Fin 7 → Fin T)
    (R : Fin T → List (Fin (A+4))) (values : Fin 7 → ℕ) (x : Fin T)
    (hx : ∀ i,x≠e i) : compactSetupUpdate7 R e values x=R x := by
  simp [compactSetupUpdate7,Function.update_of_ne,hx]

lemma compactBasisPersistent_injective : Function.Injective compactBasisPersistent := by
  intro i j h
  have hh : compactBasisOutputWork i=compactBasisOutputWork j := by
    simpa only [compactBasisPersistent,reg_inj,LReg.bc.injEq,Sum.inl.injEq,CompactBReg.work.injEq] using h
  exact (show Function.Injective compactBasisOutputWork by decide) hh

/-- The computed counters establish the fixed basis rest invariant for any compatible shape. -/
theorem compactBasisSetup_rest {shape : Shape} (R : Fin (nT CompactHostBReg) → List (Fin (A+4)))
    (d g K D q o r : ℕ)
    (hblank : ∀ z : CompactBReg,R (reg (.bc (.inl z)))=[])
    (hback : shape.H+shape.B=K*backChunks d g K)
    (hactive : shape.active=D-q-frontChunks d g K-backChunks d g K)
    (hbits : shape.bits=K*(D-q))
    (haxes : shape.axes=d) (hguard : shape.guard=g) :
    ∀ z, compactHostBasisRest shape o r z
      (compactSetupUpdate7 R compactBasisPersistent ![o,K*backChunks d g K,D-q-frontChunks d g K-backChunks d g K,K*(D-q),r,d,g] (reg (.bc z))) := by
  let values : Fin 7 → ℕ := ![o,K*backChunks d g K,D-q-frontChunks d g K-backChunks d g K,K*(D-q),r,d,g]
  have hget := compactSetupUpdate7_get compactBasisPersistent compactBasisPersistent_injective R values
  have hoff (z : CompactBReg) (hz : ∀ j : Fin 7,z≠.work (compactBasisOutputWork j)) :
      compactSetupUpdate7 R compactBasisPersistent values (reg (.bc (.inl z)))=[] := by
    rw [compactSetupUpdate7_off compactBasisPersistent R values _]
    · exact hblank z
    · intro i
      simpa only [compactBasisPersistent,ne_eq,reg_inj,LReg.bc.injEq,Sum.inl.injEq] using hz i
  intro z
  cases z with
  | inr z => trivial
  | inl z =>
    cases z with
    | slot z => exact hoff (.slot z) (fun _ => by simp)
    | work i =>
      by_cases h3 : i=3
      · subst i
        change (compactSetupUpdate7 R compactBasisPersistent values (compactBasisPersistent 0)).length=_
        rw [hget 0,List.length_replicate]
        rfl
      by_cases h4 : i=4
      · subst i
        change (compactSetupUpdate7 R compactBasisPersistent values (compactBasisPersistent 1)).length=_
        rw [hget 1,List.length_replicate]
        exact hback.symm
      by_cases h5 : i=5
      · subst i
        change (compactSetupUpdate7 R compactBasisPersistent values (compactBasisPersistent 2)).length=_
        rw [hget 2,List.length_replicate]
        exact hactive.symm
      by_cases h7 : i=7
      · subst i
        change (compactSetupUpdate7 R compactBasisPersistent values (compactBasisPersistent 3)).length=_
        rw [hget 3,List.length_replicate]
        exact hbits.symm
      by_cases h9 : i=9
      · subst i
        change (compactSetupUpdate7 R compactBasisPersistent values (compactBasisPersistent 4)).length=_
        rw [hget 4,List.length_replicate]
        rfl
      by_cases h13 : i=13
      · subst i
        change (compactSetupUpdate7 R compactBasisPersistent values (compactBasisPersistent 5)).length=_
        rw [hget 5,List.length_replicate]
        exact haxes.symm
      by_cases h14 : i=14
      · subst i
        change (compactSetupUpdate7 R compactBasisPersistent values (compactBasisPersistent 6)).length=_
        rw [hget 6,List.length_replicate]
        exact hguard.symm
      have hz : ∀ j : Fin 7,CompactBReg.work i≠.work (compactBasisOutputWork j) := by
        intro j
        fin_cases j <;> simp [compactBasisOutputWork,h3,h4,h5,h7,h9,h13,h14]
      simpa only [compactHostBasisRest,compactBasisRest,h3,h4,h5,h7,h9,h13,h14,↓reduceIte] using hoff (.work i) hz

/-- Specialization to the original row count; all substantial reasoning uses abstract q. -/
theorem compactBasisSetup_actual_rest {shape : Shape}
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4))) (d g K D o r : ℕ)
    (hblank : ∀ z : CompactBReg,R (reg (.bc (.inl z)))=[])
    (hback : shape.H+shape.B=K*backChunks d g K)
    (hactive : shape.active=D-CompactGlobalRowPadding.rowAxes Layer.NW m d-frontChunks d g K-backChunks d g K)
    (hbits : shape.bits=K*(D-CompactGlobalRowPadding.rowAxes Layer.NW m d))
    (haxes : shape.axes=d) (hguard : shape.guard=g) :
    ∀ z,compactHostBasisRest shape o r z
      (compactSetupUpdate7 R compactBasisPersistent (compactBasisSetupValues d g K D o r) (reg (.bc z))) :=
  compactBasisSetup_rest R d g K D (CompactGlobalRowPadding.rowAxes Layer.NW m d) o r
    hblank hback hactive hbits haxes hguard

end
end IntegerMultBounds.MathlibTM2.LayerMachine
