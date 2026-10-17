module

public import IntegerMultBounds.MathlibTM2.Cost.CompactStoppedReservation
public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedGeometry

/-! The separate reservation charge with validity discharged from stopped
geometry and the newly computed exponent sum. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast
noncomputable section

theorem compactStopped_reserved_cost_from_geometry (T : ℕ)
    (ds : ComplexFramedExecution.Directions)
    (D K active oS activeOffset B J globalD R n o r w ρ : ℕ)
    (s : CompactGadgetReservationShape.Shape)
    (hr : 1≤r) (hw : 1≤w) (hρ : ρ<s.chunk) (hN : o+n≤r*w)
    (hK : K=s.chunk) (hR : 0<R) (hdiv : NW^J ∣ R)
    (hlevels : synJ active active-1≤J) (hback : oS+K*B≤n)
    (hactive : activeOffset+K*active≤n)
    (hprecision : (((synPcs K 0 active activeOffset J active).map
      (compactStoppedPiece (compactGlobalCutoff globalD))).map
      (fun pc => expZ pc.u ds pc.j)).sum+active≤w) :
    (((compactStoppedReservedPcs K 0 oS B activeOffset J active globalD).map
      (compactRebasePc R)).map (compactPieceCostWith T ds D s n o r w ρ)).sum ≤
    512*B*(R*2^(o+n)*(r*w))+
      ((((synPcs K 0 active activeOffset J active).map
        (compactStoppedPiece (compactGlobalCutoff globalD))).map
        (compactRebasePc R)).map (compactPieceCostWith T ds D s n o r w ρ)).sum := by
  apply compactStopped_reserved_cost_split T ds D K 0 active oS activeOffset B J globalD R n o r w ρ s
    hr hw hρ hN
  rw [←hK]
  exact compactStoppedRebasedPcs_ok ds hR hdiv hlevels hback hactive hprecision

end
end IntegerMultBounds.MathlibTM2.Cost
