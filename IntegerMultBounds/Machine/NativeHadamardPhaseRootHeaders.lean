module

public import IntegerMultBounds.Machine.NativeEndpointCharacterCopy
public import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafFinalPorts
public import IntegerMultBounds.Machine.CompactComplexSourceReadyScalarWorkspace

/-! The actual root merger retains every original numeric word needed by the
fixed output-phase correction. Readiness is derived from its literal endpoint. -/

@[expose] public section
namespace IntegerMultBounds.Machine.NativeHadamardPhaseRootHeaders
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactComplexSourceReadyWorkspace (tapes leafTapes)
variable {stackCount : ℕ} {shape : Shape}
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount

def slot (header : Fin 15) : Fin (tapes stackCount roles) :=
  Fin.castAdd 10 (Fin.castAdd leafTapes (Fin.castAdd 7
    (CompactComplexNonleafRoleEntry.numeric (s:=10+stackCount) (c:=roles)
      (Fin.castAdd 15 (NativeEndpointCharacterCopy.index header)))))

/-- Exact original header words at the same physical ports, with their retained
head positions. No caller-provided header or phase compatibility is assumed. -/
def Ready (stage : Stage shape) (rows ell metadataPrecision : ℕ)
    (outputBank : Tapes (tapes stackCount roles) 2) : Prop :=
  ∀ header : Fin 15, outputBank.head (slot header)=1 ∧
    outputBank.tape (slot header)=RadixZeroFill.encodedBinary
      (NativeEndpointCharacterCopy.words stage rows ell metadataPrecision header)

theorem endpoint_ready (stage : Stage shape) (rows ell metadataPrecision : ℕ)
    (outputArray : CompactSpectatorVisitGeometry.Array shape rows ell)
    (entryBank : Tapes (CompactComplexNonleafRoleEntry.tapes (10+stackCount) roles) 2)
    (leaf : Tapes leafTapes 2) :
    Ready stage rows ell metadataPrecision
      (CompactComplexSourceReadyNonleafFinalPorts.endpoint shape rows ell metadataPrecision
        stage.rho stage.left stage.f stage.slots stage.right stage.source.val stage.target.val outputArray entryBank leaf) := by
  intro header
  have retained := CompactComplexNonleafRoleMergeCurrent.output_headers
    shape rows ell metadataPrecision stage.rho stage.left stage.f stage.slots stage.right
    stage.source.val stage.target.val outputArray entryBank
    (Fin.castAdd 15 (NativeEndpointCharacterCopy.index header))
  rw [CompactComplexNonleafRoleMergeCurrent.output_eq_append] at retained
  have headerReady :
      (ActiveRepairRankHeadersCommands.bank (a:=2)
        (CompactSpectatorLeafSetup.raw shape rows ell metadataPrecision stage.rho stage.left stage.f stage.slots
          stage.right stage.source.val stage.target.val)).head
        (Fin.castAdd 15 (NativeEndpointCharacterCopy.index header))=1 ∧
      (ActiveRepairRankHeadersCommands.bank (a:=2)
        (CompactSpectatorLeafSetup.raw shape rows ell metadataPrecision stage.rho stage.left stage.f stage.slots
          stage.right stage.source.val stage.target.val)).tape
        (Fin.castAdd 15 (NativeEndpointCharacterCopy.index header))=RadixZeroFill.encodedBinary
          (NativeEndpointCharacterCopy.words stage rows ell metadataPrecision header) := by
    fin_cases header <;> constructor <;> rfl
  have endpointRetained :
      (CompactComplexSourceReadyNonleafFinalPorts.endpoint shape rows ell metadataPrecision
        stage.rho stage.left stage.f stage.slots stage.right stage.source.val stage.target.val outputArray entryBank leaf).head
        (slot header)=
      (ActiveRepairRankHeadersCommands.bank (a:=2)
        (CompactSpectatorLeafSetup.raw shape rows ell metadataPrecision stage.rho stage.left stage.f stage.slots
          stage.right stage.source.val stage.target.val)).head
        (Fin.castAdd 15 (NativeEndpointCharacterCopy.index header)) ∧
      (CompactComplexSourceReadyNonleafFinalPorts.endpoint shape rows ell metadataPrecision
        stage.rho stage.left stage.f stage.slots stage.right stage.source.val stage.target.val outputArray entryBank leaf).tape
        (slot header)=
      (ActiveRepairRankHeadersCommands.bank (a:=2)
        (CompactSpectatorLeafSetup.raw shape rows ell metadataPrecision stage.rho stage.left stage.f stage.slots
          stage.right stage.source.val stage.target.val)).tape
        (Fin.castAdd 15 (NativeEndpointCharacterCopy.index header)) := by
    simpa only [slot,CompactComplexSourceReadyNonleafFinalPorts.endpoint,CompactComplexSourceReadyWorkspace.bank,
      Tapes.append,Fin.addCases_left] using retained
  exact ⟨endpointRetained.1.trans headerReady.1,endpointRetained.2.trans headerReady.2⟩

end
end IntegerMultBounds.Machine.NativeHadamardPhaseRootHeaders
