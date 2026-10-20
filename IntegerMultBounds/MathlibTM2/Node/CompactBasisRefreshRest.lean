module

public import IntegerMultBounds.MathlibTM2.Node.CompactBasisRefresh
import IntegerMultBounds.MathlibTM2.Node.CompactBasisSetupRest
public import IntegerMultBounds.MathlibTM2.Node.CompactLayerPlaced
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Five-counter refresh establishes the compact invariant while retaining original global d/g. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open CompactGadgetReservationCapacity
open CompactGadgetReservationShape (Shape)
open IntegerMultBounds.MathlibTM2.Layer
noncomputable section
variable {A : ℕ}

theorem compactBasisRefresh_rest {shape : Shape}
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4))) (d g K D q o r : ℕ)
    (hblank : ∀ z : CompactBReg,z≠.work 13 → z≠.work 14 → R (reg (.bc (.inl z)))=[])
    (hdepth : (R (reg (.bc (.inl (.work 13))))).length=d)
    (hglobalGuard : (R (reg (.bc (.inl (.work 14))))).length=g)
    (hback : shape.H+shape.B=K*backChunks d g K)
    (hactive : shape.active=D-q-frontChunks d g K-backChunks d g K)
    (hbits : shape.bits=K*(D-q)) (haxes : shape.axes=d) (hguard : shape.guard=g) :
    ∀ z,compactHostBasisRest shape o r z
      (compactSetupUpdate7 R compactBasisRefreshDst
        (compactZeroTail ![o,K*backChunks d g K,D-q-frontChunks d g K-backChunks d g K,K*(D-q),r,d,g])
        (reg (.bc z))) := by
  let values : Fin 7 → ℕ := ![o,K*backChunks d g K,D-q-frontChunks d g K-backChunks d g K,K*(D-q),r,d,g]
  have hget := compactSetupUpdate7_get compactBasisRefreshDst compactBasisRefreshDst_injective R (compactZeroTail values)
  have hoff (z : CompactBReg) (hz : ∀ j : Fin 7,z≠.work (compactBasisRefreshWork j)) :
      compactSetupUpdate7 R compactBasisRefreshDst (compactZeroTail values) (reg (.bc (.inl z)))=
        R (reg (.bc (.inl z))) := by
    apply compactSetupUpdate7_off
    intro j
    simpa only [compactBasisRefreshDst,ne_eq,reg_inj,LReg.bc.injEq,Sum.inl.injEq] using hz j
  intro z
  cases z with
  | inr z => trivial
  | inl z =>
    cases z with
    | slot z =>
      exact (hoff (.slot z) (fun _ => by simp)).trans (hblank (.slot z) (by simp) (by simp))
    | work i =>
      by_cases h3 : i=3
      · subst i
        change (compactSetupUpdate7 R compactBasisRefreshDst (compactZeroTail values) (compactBasisRefreshDst 0)).length=o
        rw [hget 0,List.length_replicate]
        rfl
      by_cases h4 : i=4
      · subst i
        change (compactSetupUpdate7 R compactBasisRefreshDst (compactZeroTail values) (compactBasisRefreshDst 1)).length=shape.H+shape.B
        rw [hget 1,List.length_replicate]
        exact hback.symm
      by_cases h5 : i=5
      · subst i
        change (compactSetupUpdate7 R compactBasisRefreshDst (compactZeroTail values) (compactBasisRefreshDst 2)).length=shape.active
        rw [hget 2,List.length_replicate]
        exact hactive.symm
      by_cases h7 : i=7
      · subst i
        change (compactSetupUpdate7 R compactBasisRefreshDst (compactZeroTail values) (compactBasisRefreshDst 3)).length=shape.bits
        rw [hget 3,List.length_replicate]
        exact hbits.symm
      by_cases h9 : i=9
      · subst i
        change (compactSetupUpdate7 R compactBasisRefreshDst (compactZeroTail values) (compactBasisRefreshDst 4)).length=r
        rw [hget 4,List.length_replicate]
        rfl
      by_cases h13 : i=13
      · subst i
        change (compactSetupUpdate7 R compactBasisRefreshDst (compactZeroTail values) (reg (.bc (.inl (.work 13))))).length=shape.axes
        rw [compactBasisRefresh_preserves_global R _ 13 (Or.inl rfl),hdepth,haxes]
      by_cases h14 : i=14
      · subst i
        change (compactSetupUpdate7 R compactBasisRefreshDst (compactZeroTail values) (reg (.bc (.inl (.work 14))))).length=shape.guard
        rw [compactBasisRefresh_preserves_global R _ 14 (Or.inr rfl),hglobalGuard,hguard]
      by_cases h0 : i=0
      · subst i
        exact hget 5
      by_cases h11 : i=11
      · subst i
        exact hget 6
      have hz : ∀ j : Fin 7,CompactBReg.work i≠.work (compactBasisRefreshWork j) := by
        intro j
        fin_cases j <;> simp [compactBasisRefreshWork,h3,h4,h5,h7,h9,h0,h11]
      have hb := (hoff (.work i) hz).trans (hblank (.work i) (by simpa using h13) (by simpa using h14))
      simpa only [compactHostBasisRest,compactBasisRest,h3,h4,h5,h7,h9,h13,h14,↓reduceIte] using hb

theorem compactBasisRefresh_actual_rest {shape : Shape}
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4))) (d g K D o r : ℕ)
    (hblank : ∀ z : CompactBReg,z≠.work 13 → z≠.work 14 → R (reg (.bc (.inl z)))=[])
    (hdepth : (R (reg (.bc (.inl (.work 13))))).length=d)
    (hglobalGuard : (R (reg (.bc (.inl (.work 14))))).length=g)
    (hback : shape.H+shape.B=K*backChunks d g K)
    (hactive : shape.active=D-CompactGlobalRowPadding.rowAxes NW m d-frontChunks d g K-backChunks d g K)
    (hbits : shape.bits=K*(D-CompactGlobalRowPadding.rowAxes NW m d))
    (haxes : shape.axes=d) (hguard : shape.guard=g) :
    ∀ z,compactHostBasisRest shape o r z
      (compactSetupUpdate7 R compactBasisRefreshDst (compactZeroTail (compactBasisSetupValues d g K D o r)) (reg (.bc z))) :=
  compactBasisRefresh_rest R d g K D (CompactGlobalRowPadding.rowAxes NW m d) o r
    hblank hdepth hglobalGuard hback hactive hbits haxes hguard

end
end IntegerMultBounds.MathlibTM2.LayerMachine
