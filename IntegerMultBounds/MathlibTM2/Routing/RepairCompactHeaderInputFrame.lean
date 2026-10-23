module

public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactHeaderData
public import IntegerMultBounds.MathlibTM2.Routing.RepairHeaderInputFrame

/-! Header-free configuration and generator inputs survive stream placement. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {A : ℕ} (p : Par) (X rb : ℕ)

theorem RepairPendingHeaderData.updateCompactHeaderStream {wb wm wp wk R B : ℕ}
    {bank : Fin repairCompactHeaderT → List (Fin (A + 4))}
    (data : RepairPendingHeaderData p X rb wb wm wp wk R B (fun i => bank (repairCompactHeaderRawCore i)))
    (out : List (Fin (A + 4))) :
    RepairPendingHeaderData p X rb wb wm wp wk R B
      (fun i => Function.update bank (repairCompactHeaderRawCore repairHost.src) out (repairCompactHeaderRawCore i)) := by
  apply data.congr p X rb
  intro key
  have hraw : repairSetupSource key ≠ repairHost.src := by
    intro he
    exact repairCompactConfigurationSource_src key (congrArg repairCompactConfigurationCore he)
  have hne : repairCompactHeaderRawCore (repairSetupSource key) ≠ repairCompactHeaderRawCore repairHost.src :=
    repairCompactHeaderRawCore_injective.ne hraw
  exact Function.update_of_ne hne _ _

theorem compactHeaderWork_updateStream (bank : Fin repairCompactHeaderT → List (Fin (A + 4)))
    (out : List (Fin (A + 4))) (r : HeaderWorkRole) :
    Function.update bank (repairCompactHeaderRawCore repairHost.src) out (sharedHeaderWork r) =
      bank (sharedHeaderWork r) :=
  Function.update_of_ne (sharedHeaderCore_work _ r).symm _ _

end
end IntegerMultBounds.MathlibTM2.Routing
