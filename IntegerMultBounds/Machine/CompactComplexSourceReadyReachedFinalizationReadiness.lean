module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedChildBoundary
public import IntegerMultBounds.Machine.CompactComplexSourceReadyFinalCapacity

/-! Literal finalization input readiness from the actual reached bank.
Source blankness and role words reconstruct the exact sink-input payload;
canonical source-ready framing provides the physical empty leaf/private banks
required by the unchanged corrected-final program. No execution premise is used. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedFinalizationReadiness
noncomputable section
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes ready)
open CompactComplexSourceReadyReachedEventInvariant (Reached canonical)
open CompactComplexSourceReadyCompletedChildBoundary (before)
open CompactComplexNativeCodecFrame (bank permanentTapes)
variable {stackTapeCount : ℕ} {shape : CompactGadgetReservationShape.Shape}
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  CompactComplexRolePhaseSite.roleCount Networks.ComplexFramedExecution.rows CompactComplexCompletedLiveLower.schedule

private theorem role_index_encoding (wire : Networks.ComplexFramedExecution.Wire) :
    CompactComplexScalarRolePorts.roleIndex (CompactComplexScalarIntegerRows.wireIndex wire)=
      CompactComplexRolePhaseSite.roleEncoding wire := by
  simp only [CompactComplexScalarRolePorts.roleIndex,Equiv.trans_apply,Equiv.symm_apply_apply]

private theorem entry_append {roleCount : ℕ}
    (permanentBank : Tapes (permanentTapes (10+stackTapeCount) roleCount) 2)
    (auxiliaryBank : Tapes 2 2) (frameBank : Tapes 7 2) :
    CompactComplexNonleafSpectatorTargetRestore.entry permanentBank (auxiliaryBank.append frameBank)=
      (CompactComplexSourceReadyScalarChildReadiness.entryBank permanentBank auxiliaryBank).append frameBank := by
  apply congrArg₂ Tapes.mk <;> funext port
  all_goals induction port using Fin.addCases (m:=permanentTapes (10+stackTapeCount) roleCount+2) (n:=7) with
  | left port =>
    induction port using Fin.addCases (m:=permanentTapes (10+stackTapeCount) roleCount) (n:=2) with
    | left port =>
      have portEquation : CompactComplexNonleafSpectatorTargetRestore.entryEquiv stackTapeCount roleCount
          (Fin.castAdd 7 (Fin.castAdd 2 port))=Fin.castAdd 9 port := Fin.ext rfl
      simp only [Equiv.symm_symm,portEquation,CompactComplexSourceReadyScalarChildReadiness.entryBank,Tapes.append,Fin.addCases_left]
    | right port =>
      have portEquation : CompactComplexNonleafSpectatorTargetRestore.entryEquiv stackTapeCount roleCount
          (Fin.castAdd 7 (Fin.natAdd (permanentTapes (10+stackTapeCount) roleCount) port))=
          Fin.natAdd (permanentTapes (10+stackTapeCount) roleCount) (Fin.castAdd 7 port) := Fin.ext rfl
      simp only [Equiv.symm_symm,portEquation,CompactComplexSourceReadyScalarChildReadiness.entryBank,
        Tapes.append,Fin.addCases_left,Fin.addCases_right]
  | right port =>
    have portEquation : CompactComplexNonleafSpectatorTargetRestore.entryEquiv stackTapeCount roleCount
        (Fin.natAdd (permanentTapes (10+stackTapeCount) roleCount+2) port)=
        Fin.natAdd (permanentTapes (10+stackTapeCount) roleCount) (Fin.natAdd 2 port) := by
      apply Fin.ext
      change permanentTapes (10+stackTapeCount) roleCount+2+port.val=
        permanentTapes (10+stackTapeCount) roleCount+(2+port.val)
      omega
    simp only [Equiv.symm_symm,portEquation,Tapes.append,Fin.addCases_right]

private theorem contraction_canonical
    (permanentBank : Tapes (permanentTapes (10+stackTapeCount) roles) 2) (auxiliaryBank : Tapes 2 2) :
    CompactComplexSourceReadyNonleafContraction.ready permanentBank
      (auxiliaryBank.append (SharedBank.empty 7 2))
      (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2)=canonical permanentBank auxiliaryBank := by
  unfold CompactComplexSourceReadyNonleafContraction.ready
  rw [entry_append]
  rfl

section Reached
variable {stage : ActivePrefixStageParameters.Stage shape}
    {rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes baselineLive
      dependencyLevels frameVolume returnedVolume scalarPrefix live : ℕ}
    {pcStack : Fin stackTapeCount} {stackOrigin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
    {nodeBank : Tapes (nodeTapes stackTapeCount roles) 2}
    (reached : Reached stage rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume returnedVolume scalarPrefix live pcStack stackOrigin savedCalls nodeBank)

/-- Source and role readiness determine the entire literal payload used by
sink correction, in the original named-wire enumeration. -/
theorem payload_eq : reached.payload=CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0 (before reached) := by
  have rolePorts (role : Fin roles) : reached.payload.head (Fin.natAdd 1 role)=0 ∧
      reached.payload.tape (Fin.natAdd 1 role)=NativeZeroPadding.word
        (NativeZeroPaddingArray.word (before reached (CompactComplexRolePhaseSite.roleEncoding.symm role))) := by
    have physicalRole := CompactComplexSpectatorTargetBank.role_bank reached.control reached.queue reached.scalar
      (CompactComplexNativeCodec.raw stage rowCount polynomialExponent metadataPrecision) reached.tail reached.storage reached.payload role
    have representedRole := reached.role_words
      (CompactComplexScalarIntegerRows.wireIndex (CompactComplexRolePhaseSite.roleEncoding.symm role))
    rw [role_index_encoding,Equiv.apply_symm_apply] at representedRole
    exact ⟨physicalRole.1.symm.trans representedRole.1,physicalRole.2.symm.trans representedRole.2⟩
  apply congrArg₂ Tapes.mk <;> funext port
  all_goals induction port using Fin.addCases (m:=1) (n:=roles) with
  | left port =>
    have sourcePort : port=(0 : Fin 1) := Fin.ext (by have portBound := port.isLt;omega)
    subst port
    first
    | simpa only [CompactComplexEndpointRoleExchange.payload,CyclicRowCopy.payload,Tapes.append,Fin.addCases_left]
        using reached.source_blank.1
    | simpa only [CompactComplexEndpointRoleExchange.payload,CyclicRowCopy.payload,Tapes.append,Fin.addCases_left]
        using reached.source_blank.2
  | right port =>
    first
    | simpa only [CompactComplexEndpointRoleExchange.payload,CyclicRowCopy.payload,Tapes.append,Fin.addCases_right]
        using (rolePorts port).1
    | simpa only [CompactComplexEndpointRoleExchange.payload,CyclicRowCopy.payload,Tapes.append,Fin.addCases_right]
        using (rolePorts port).2

/-- The actual reached source-ready bank, with its real empty scalar suffix,
is exactly the prebank required by corrected-final compose_runs_capacity. -/
theorem actual_final_input : ready nodeBank=
    (CompactComplexSourceReadyNonleafContraction.ready
      (bank reached.control reached.queue reached.scalar (CompactComplexNativeCodec.raw stage rowCount polynomialExponent metadataPrecision)
        reached.tail reached.storage (CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0 (before reached)))
      (reached.aux.append (SharedBank.empty 7 2))
      (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2)).append
      (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2) := by
  rw [contraction_canonical]
  unfold ready
  exact congrArg (fun actualBank : Tapes (nodeTapes stackTapeCount roles) 2 =>
    actualBank.append (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2))
    (reached.canonical_bank.trans (congrArg
    (fun payload => canonical (bank reached.control reached.queue reached.scalar
      (CompactComplexNativeCodec.raw stage rowCount polynomialExponent metadataPrecision)
      reached.tail reached.storage payload) reached.aux) (payload_eq reached)))

/-- The actual sink-input family retains its physical reserved record widths. -/
theorem before_width : ∀ wire coefficient,
    (before reached wire coefficient).1.length=CompactNativeRoleHeaders.recordWidth shape metadataPrecision ∧
    (before reached wire coefficient).2.length=CompactNativeRoleHeaders.recordWidth shape metadataPrecision := by
  intro wire coefficient
  exact reached.width (CompactComplexScalarIntegerRows.wireIndex wire) coefficient

end Reached

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedFinalizationReadiness
