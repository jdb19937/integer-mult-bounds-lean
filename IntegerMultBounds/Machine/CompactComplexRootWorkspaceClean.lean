module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafFinalPorts

/-! Explicit clean private workspace at the actual nonleaf root endpoint.
All current-node role payloads, the seven-tape entry frame, complete leaf
workspace and ten-tape work suffix have blank tapes and origin heads. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexRootWorkspaceClean
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexSourceReadyWorkspace (publicTapes leafTapes tapes)
variable {stackCount roles : ℕ}

def Clean (outputBank : Tapes (tapes stackCount roles) 2) : Prop :=
  (∀ leafPort : Fin leafTapes,
    outputBank.head (Fin.castAdd 10 (Fin.natAdd (publicTapes stackCount roles) leafPort))=0 ∧
    outputBank.tape (Fin.castAdd 10 (Fin.natAdd (publicTapes stackCount roles) leafPort))=(fun _ => blank)) ∧
  (∀ workPort : Fin 10,
    outputBank.head (Fin.natAdd (publicTapes stackCount roles+leafTapes) workPort)=0 ∧
    outputBank.tape (Fin.natAdd (publicTapes stackCount roles+leafTapes) workPort)=(fun _ => blank)) ∧
  (∀ framePort : Fin 7,
    outputBank.head (Fin.castAdd 10 (Fin.castAdd leafTapes
      (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes (10+stackCount) roles) framePort)))=0 ∧
    outputBank.tape (Fin.castAdd 10 (Fin.castAdd leafTapes
      (Fin.natAdd (CompactComplexNonleafRoleEntry.tapes (10+stackCount) roles) framePort)))=(fun _ => blank)) ∧
  (∀ rolePort : Fin roles,
    outputBank.head (Fin.castAdd 10 (Fin.castAdd leafTapes
      (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.roleTape rolePort))))=0 ∧
    outputBank.tape (Fin.castAdd 10 (Fin.castAdd leafTapes
      (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.roleTape rolePort))))=(fun _ => blank))

/-- The literal physical root final endpoint reclaims all private node
workspace and vacates every original role payload, with all heads at zero. -/
theorem endpoint_clean (shape : Shape) (rows ell precision phase left count slots right source target : ℕ)
    (outputArray : CompactSpectatorVisitGeometry.Array shape rows ell)
    (entryBank : Tapes (CompactComplexNonleafRoleEntry.tapes (10+stackCount) roles) 2) :
    Clean (CompactComplexSourceReadyNonleafFinalPorts.endpoint shape rows ell precision phase left count slots right source target
      outputArray entryBank (SharedBank.empty leafTapes 2)) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro leafPort
    simp only [CompactComplexSourceReadyNonleafFinalPorts.endpoint,CompactComplexSourceReadyWorkspace.bank,
      Tapes.append,Fin.addCases_left,Fin.addCases_right,SharedBank.empty,and_self]
  · intro workPort
    simp only [CompactComplexSourceReadyNonleafFinalPorts.endpoint,CompactComplexSourceReadyWorkspace.bank,
      Tapes.append,Fin.addCases_right,SharedBank.empty,and_self]
  · intro framePort
    simp only [CompactComplexSourceReadyNonleafFinalPorts.endpoint,CompactComplexSourceReadyWorkspace.bank,
      Tapes.append,Fin.addCases_left,Fin.addCases_right,SharedBank.empty,and_self]
  · intro rolePort
    have roleBlank := CompactComplexNonleafRoleMergeCurrent.output_roles_blank
      shape rows ell precision phase left count slots right source target outputArray entryBank rolePort
    simpa only [CompactComplexSourceReadyNonleafFinalPorts.endpoint,CompactComplexSourceReadyWorkspace.bank,
      CompactComplexNonleafRoleMergeCurrent.bank,Tapes.append,Fin.addCases_left] using roleBlank

end
end IntegerMultBounds.Machine.CompactComplexRootWorkspaceClean
