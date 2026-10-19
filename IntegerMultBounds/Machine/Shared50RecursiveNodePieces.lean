module

public import IntegerMultBounds.Machine.Shared50RecursiveNodeBinary
public import IntegerMultBounds.Machine.RecursiveScalarIndex
public import IntegerMultBounds.Machine.Shared50NodePieceTransport

/-! Actual segment/gate/recursive-call array execution produces the exact node
merge input. The only recursive premise is the explicit child interchange
contract at its selected wire; no replacement schedule or frame oracle. -/

@[expose] public section

namespace IntegerMultBounds.Machine.Shared50RecursiveNodePieces
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50TapeGlobal (roleCount roleEquiv)
open RecursiveInterchangeLayout (Descriptor volume role)
open Shared50RecursiveNodeLayout (wires)
open Shared50RecursiveNodeSemantics (encoded networkData)
open Shared50RecursiveNodeBinary (splitWorld networkWorld)
open Shared50NodePieceTransport (Child ChildSpec run worldSlot)
variable {b u : ℕ} {v : Descriptor}

theorem run_network (hw : v.width=125000*b) (hd : roleCount ∣ v.rows)
    (child : Child (role v roleCount)) (hc : ChildSpec (v := role v roleCount) hw child)
    (x : Fin (volume prime v) → ZMod 2) :
    Shared50NodePieceTransport.run (v := role v roleCount) hw child Shared50PieceSchedule.pieces
      (RecursiveRowsSerialization.roleData wires (Equiv.refl _) hd (encoded x)) = networkData hw hd x := by
  rw [Shared50RecursiveNodeBinary.splitData_encoded,Shared50RecursiveNodeBinary.networkData_encoded]
  funext i z
  induction i using Fin.addCases with
  | left i =>
    obtain ⟨a,rfl⟩ := RecursiveScalarIndex.surjective (v := role v roleCount) hw z
    have he := Shared50NodePieceTransport.run_entry (v := role v roleCount) hw child hc (splitWorld hd x) (fun _ => blank) (roleEquiv i) a
    rw [← Shared50RecursiveNodeBinary.networkWorld_scalar hw hd x (roleEquiv i) a] at he
    simpa only [worldSlot,Equiv.symm_apply_apply,Shared50NodeGates.encoded,Shared50NodeGates.extend,
      Fin.addCases_left,Shared50RecursiveGates.encoded] using he
  | right i =>
    fin_cases i
    have he := congrFun (Shared50NodePieceTransport.run_io (v := role v roleCount) hw child hc Shared50PieceSchedule.pieces
      (Shared50NodeGates.encoded (splitWorld hd x) (fun _ => blank))) z
    exact he

end
end IntegerMultBounds.Machine.Shared50RecursiveNodePieces
