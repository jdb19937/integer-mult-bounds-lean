module

public import IntegerMultBounds.MathlibTM2.Node.CompactTopProcKernel
public import IntegerMultBounds.MathlibTM2.Node.CompactBasisRegisters

/-! Fully executed top kernels for the compact bank. The level-zero layer is the
existing generic leaf machine; no recursive layer-call premise remains. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {BReg : Type} [Fintype BReg] {A Q : ℕ} {U P : Type}

/-- Actual top kernels, preserving an arbitrary persistent basis-rest state. -/
theorem compactTopLeafKerS_exec (body : P → Pr P (nT BReg) Q A U)
    (bc : BReg → List (Fin (A+4)) → Prop) (ds : ComplexFramedExecution.Directions)
    (hA : 9^4≤A+4)
    {cfg pfs : List ℕ} {N R r w K ρ q aT : ℕ} (h3 : cfg[3]?=some R) (h5 : cfg[5]?=some q)
    (h6 : cfg[6]?=some aT) (h7 : cfg[7]?=some (K*q)) (hr : 1≤r) (hw : 1≤w)
    (hfitT : ∀ i<q,aT+ρ+K*i<N) (Z : ZArr (Fin R × Fin r) N)
    (v : HS (nT BReg) Q A U) (S : Stacks (nT BReg) A)
    (hL : ∀ y,S.L y=[]) (hT : CompactTopRegs bc S.R N r w K ρ)
    (hI : CompactTopIn (BReg := BReg) S.R cfg pfs) (hio : S.R (reg .io)=encZ A w Z) :
    ∃ (v' : HS (nT BReg) Q A U) (c : ℕ), v'.user=v.user ∧
      c ≤ compactTopKerSCost cfg K R q aT (leafCost q K ρ aT R N r w) ∧
      Exec body (compactTopKerS leafP) (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io)
            (encZ A w (k2s ((List.finRange q).map (actMap aT ρ K q N hfitT)) Z))}) := by
  apply compactTopKerS_exec body leafP bc ds (leafCost q K ρ aT R N r w)
    h3 h5 h6 h7 hfitT ?_ Z v S hL hT hI hio
  intro _ Z' v' S' _ hpar hrest hio'
  exact leafP_exec body hA hr hw hfitT Z' v' S' hpar hrest hio'


/-- The actual top-kernel executor on CompactBReg with its seven persistent
basis inputs preserved. -/
theorem compactBasisTopLeaf_exec (body : P → Pr P (nT CompactBReg) Q A U)
    (shape : CompactGadgetReservationShape.Shape) (o : ℕ) (ds : ComplexFramedExecution.Directions)
    (hA : 9^4≤A+4)
    {cfg pfs : List ℕ} {N R r w K ρ q aT : ℕ} (h3 : cfg[3]?=some R) (h5 : cfg[5]?=some q)
    (h6 : cfg[6]?=some aT) (h7 : cfg[7]?=some (K*q)) (hr : 1≤r) (hw : 1≤w)
    (hfitT : ∀ i<q,aT+ρ+K*i<N) (Z : ZArr (Fin R × Fin r) N)
    (v : HS (nT CompactBReg) Q A U) (S : Stacks (nT CompactBReg) A)
    (hL : ∀ y,S.L y=[]) (hT : CompactTopRegs (compactBasisRest shape o r) S.R N r w K ρ)
    (hI : CompactTopIn (BReg := CompactBReg) S.R cfg pfs) (hio : S.R (reg .io)=encZ A w Z) :
    ∃ (v' : HS (nT CompactBReg) Q A U) (c : ℕ), v'.user=v.user ∧
      c ≤ compactTopKerSCost cfg K R q aT (leafCost q K ρ aT R N r w) ∧
      Exec body (compactTopKerS leafP) (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io)
            (encZ A w (k2s ((List.finRange q).map (actMap aT ρ K q N hfitT)) Z))}) := by
  exact compactTopLeafKerS_exec body (compactBasisRest shape o r) ds hA h3 h5 h6 h7 hr hw
    hfitT Z v S hL hT hI hio

end
end IntegerMultBounds.MathlibTM2.LayerMachine
