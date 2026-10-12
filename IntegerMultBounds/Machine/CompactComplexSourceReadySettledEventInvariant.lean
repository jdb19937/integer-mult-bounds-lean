module

public import IntegerMultBounds.Machine.CompactComplexSourceReadySettledFrames
public import IntegerMultBounds.Machine.CompactComplexSourceReadyCompletedChildBoundary

/-! The actual scalar and native basis successors retain completed dormant
frames. The storage and auxiliary fields are recovered from each returned
Reached witness's literal canonical bank, rather than supplied as endpoint
assumptions. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexSourceReadySettledEventInvariant
noncomputable section
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes permanent ready output permanentTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached canonical nextCaller)
open CompactComplexSourceReadyReachedDormantFrameInvariant (Snapshot Settled storageOf)
open CompactComplexScalarIntegerRows (GroupIndex gates guardBits)
open CompactComplexScalarSegmentRows (block)
open CompactComplexScalarPolynomialSequence (execute)
open CompactComplexDenominatorCapacity (scalarRows)
variable {s : ℕ} {sh : CompactGadgetReservationShape.Shape}
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount
  Networks.ComplexRank25.program Networks.ComplexFramedExecution.rows
  CompactComplexScalarIntegerRows.gates CompactComplexCompletedLiveLower.schedule

/-- Read the actual auxiliary pair beyond the permanent caller prefix. -/
def auxiliary (v : Tapes (nodeTapes s roles) 2) : Tapes 2 2 :=
  ⟨fun i => v.head (Fin.castAdd 10
    (Fin.castAdd CompactComplexSourceReadyWorkspace.leafTapes
      (Fin.castAdd 7 (Fin.natAdd (permanentTapes s roles) i)))),
   fun i => v.tape (Fin.castAdd 10
    (Fin.castAdd CompactComplexSourceReadyWorkspace.leafTapes
      (Fin.castAdd 7 (Fin.natAdd (permanentTapes s roles) i))))⟩

theorem auxiliary_canonical (w : Tapes (permanentTapes s roles) 2) (aux : Tapes 2 2) :
    auxiliary (canonical w aux)=aux := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [canonical,CompactComplexSourceReadyWorkspace.ready,
    CompactComplexSourceReadyWorkspace.bank,CompactComplexSourceReadyScalarChildReadiness.entryBank,
    Tapes.append,Fin.addCases_left,Fin.addCases_right]

section Fields
variable {stage : ActivePrefixStageParameters.Stage sh}
  {rows ell metadataP e p C axes baseline levels frames returned pref n : ℕ}
  {pcStack : Fin s} {origin : ℤ} {calls : List Networks.ComplexRecursiveCallSchema.Call}
  {v : Tapes (nodeTapes s roles) 2}

/-- A canonical physical endpoint determines the storage and auxiliary fields
of its actual reached witness, independently of its numerical data proofs. -/
theorem canonical_fields
    (h : Reached stage rows ell metadataP e p C axes baseline levels frames returned pref n pcStack origin calls v)
    (w : Tapes (permanentTapes s roles) 2) (aux : Tapes 2 2)
    (hv : v=canonical w aux) : h.storage=storageOf w ∧ h.aux=aux := by
  have he := h.canonical_bank.symm.trans hv
  have hp := congrArg permanent he
  rw [CompactComplexSourceReadyReachedEventInvariant.canonical_permanent,
    CompactComplexSourceReadyReachedEventInvariant.canonical_permanent] at hp
  have hs := congrArg storageOf hp
  rw [CompactComplexSourceReadyReachedDormantFrameInvariant.storageOf_bank] at hs
  have ha := congrArg auxiliary he
  rw [auxiliary_canonical,auxiliary_canonical] at ha
  exact ⟨hs,ha⟩

end Fields

/-- The actual corrected source endpoint initializes a reached witness
while retaining Settled for every already captured ancestor frame. -/
theorem of_corrected_entry_settled {left k levels frames returned : ℕ}
    (stage : ActivePrefixStageParameters.Stage sh)
    (hslots : stage.slots=CompactComplexRecursiveGeometry.arity)
    (rows ell q p C baseline n : ℕ) (hd : roles∣rows) (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (path : CompactRecursiveDependencyBudget.Path sh.active left (k+1) levels frames returned)
    (hp : p≤q) (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (hw : CompactSpectatorInheritedGrid.Width sh rows ell q f)
    (hg : CompactSpectatorInheritedGrid.Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) f)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (old : Tapes (10+s) 2) (aux : Tapes 2 2)
    (snapshot : Snapshot s) (hsettled : Settled snapshot old aux)
    (hblank : old.head ⟨0,by omega⟩=0 ∧ old.tape ⟨0,by omega⟩=(fun _ => blank))
    (hlive : old.head ⟨7,by omega⟩=1 ∧ old.tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits n))
    (hclock : aux.head 1=0 ∧ aux.tape 1=(fun _ => blank))
    (hfree : CompactComplexSourceReadyPrefixReadiness.BlankAfter aux 0)
    (he : control.head 1=1 ∧ control.tape 1=
      BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits (k+1)))
    (h28 : control.head 28=0 ∧ control.tape 28=(fun _ => blank))
    (h29 : control.head 29=0 ∧ control.tape 29=(fun _ => blank))
    (hledger : n≤CompactComplexDenominatorCapacity.ledger scalarRows baseline levels frames returned (CompactFramedScalarGrid.rows 0).length)
    (pcStack : Fin s) (origin : ℤ) (calls : List Networks.ComplexRecursiveCallSchema.Call)
    (hCalls : CompactComplexSourceReadySavedCallHistory.Associated origin calls
      (old.tape (Fin.natAdd 10 pcStack)) (old.head (Fin.natAdd 10 pcStack))) :
    let metadataP := ButterflyIndependentGuardHeaders.reservation sh.bits q
    let w := CompactComplexCorrectedEntryGeometryReadiness.permanent stage hslots rows ell metadataP n k hd f
      control queue scalar tail old
    ∃ h : Reached stage rows ell metadataP (k+1) p C 0 baseline levels frames returned 0 n pcStack origin calls
      (canonical w aux),
      h.data=(fun a => CompactComplexCorrectedEntryGeometryReadiness.array stage hslots rows ell metadataP hd f
        (CompactComplexScalarRolePorts.roleIndex a)) ∧ Settled snapshot h.storage h.aux := by
  dsimp only
  obtain ⟨h,hd⟩ := CompactComplexSourceReadyReachedEventInvariant.initial
    stage hslots rows ell q p C baseline n hd f path hp hchunk hw hg
    control queue scalar tail old aux hblank hlive hclock hfree he h28 h29 hledger
    pcStack origin calls hCalls
  obtain ⟨hs,haux⟩ := canonical_fields h _ aux rfl
  simp only [CompactComplexCorrectedEntryGeometryReadiness.permanent,
    CompactComplexSourceReadyReachedDormantFrameInvariant.storageOf_bank] at hs
  refine ⟨h,hd,?_⟩
  rw [hs,haux]
  exact CompactComplexSourceReadySettledFrames.corrected_entry_storage_settled hsettled _

section Scalar
variable {stage : ActivePrefixStageParameters.Stage sh}
  {rows ell metadataP nodeExponent p C axes baseline levels frames returned n : ℕ}
  {pcStack : Fin s} {origin : ℤ} {calls : List Networks.ComplexRecursiveCallSchema.Call}
  {v : Tapes (nodeTapes s roles) 2}

/-- The genuine scalar lifecycle returns a numerical reached witness and a
Settled proof about that same witness's actual physical frame fields. -/
theorem scalar_successor_settled {left : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left nodeExponent levels frames returned)
    (g : GroupIndex)
    (h : Reached stage rows ell metadataP nodeExponent p C axes baseline levels frames returned g.val n pcStack origin calls v)
    (snapshot : Snapshot s) (hsettled : Settled snapshot h.storage h.aux)
    (hrows : 0<rows/roles) (hG : 0<sh.guard) (hK : 0<sh.chunk)
    (ha : 0<sh.active) (hp : p+2*sh.bits≤metadataP) (haxes : axes≤sh.bits)
    (hroom : CompactSpectatorInheritedGrid.dependencyCoefficient C+Nat.clog 2 (C+1)+(gates g).length*guardBits≤sh.chunk)
    (hC : CompactFramedScalarGrid.growthConstant≤C) (hbase : baseline≤p)
    (hdenRoom : CompactComplexDenominatorCapacity.room scalarRows≤sh.chunk) :
    HoareTime (CompactComplexSourceReadyActualTable.scalar (s:=s) g).2
      (fun z => z=ready v) (fun z => z=ready (output v (nextCaller h g)))
      (CompactComplexScalarCountLifecycle.roleTimeConstant (block g)*
        (rows*2^sh.bits*2^ell)*(ButterflyGuard.halfWidth metadataP sh.bits+2)) ∧
    ∃ hn : Reached stage rows ell metadataP nodeExponent p C axes baseline levels frames returned (g.val+1)
      (n+(gates g).length) pcStack origin calls (output v (nextCaller h g)),
      hn.data=execute (block g) h.data ∧ Settled snapshot hn.storage hn.aux := by
  obtain ⟨hr,hn,hd⟩ := CompactComplexSourceReadyReachedEventInvariant.scalar_successor
    path g h hrows hG hK ha hp haxes hroom hC hbase hdenRoom
  have hv : output v (nextCaller h g)=canonical (nextCaller h g) h.aux :=
    (congrArg (fun z => output z (nextCaller h g)) h.canonical_bank).trans
      (CompactComplexSourceReadyReachedEventInvariant.canonical_output _ _ _)
  obtain ⟨hs,haux⟩ := canonical_fields hn (nextCaller h g) h.aux hv
  simp only [nextCaller,CompactComplexSourceReadyReachedDormantFrameInvariant.storageOf_bank] at hs
  refine ⟨hr,hn,hd,?_⟩
  rw [hs,haux]
  exact CompactComplexSourceReadySettledFrames.scalar_storage_settled hsettled _

end Scalar

section Basis
variable {stage : ActivePrefixStageParameters.Stage sh}
  {m ell metadataP e p C axes baseline levels frames returned pref n : ℕ}
  {pcStack : Fin s} {origin : ℤ} {calls : List Networks.ComplexRecursiveCallSchema.Call}
  {v : Tapes (nodeTapes s roles) 2}

/-- Both directions of the actual native basis permutation retain Settled on
the same reached witness, including the literal payload-stack auxiliary pair. -/
theorem basis_reached_settled
    (h : Reached stage m ell metadataP e p C axes baseline levels frames returned pref n pcStack origin calls v)
    (snapshot : Snapshot s) (hsettled : Settled snapshot h.storage h.aux)
    (j : Fin roles) (hG : 1≤sh.guard) (hGK : sh.guard+1≤sh.chunk) (hm : 0<m/roles)
    (hslots : stage.slots=25^3) (pc : Fin CompactAllAxisPhaseDispatch.count) (reverse : Bool) :
    let after := CompactComplexSourceReadyReachedBasisInvariant.basisArray
      stage (m/roles) ell metadataP hG hGK hm hslots pc reverse
      (h.data (CompactComplexScalarRolePorts.roleIndex.symm j))
    ∃ hn : Reached stage m ell metadataP e p C axes baseline levels frames returned pref n pcStack origin calls
      (canonical (CompactComplexSourceReadyReachedBasisInvariant.replacementCaller h j after) h.aux),
      hn.data=CompactComplexSourceReadyReachedBasisInvariant.replacementData h j after ∧
      Settled snapshot hn.storage hn.aux := by
  dsimp only
  obtain ⟨hn,hd⟩ := CompactComplexSourceReadyReachedBasisInvariant.basis_reached
    h j hG hGK hm hslots pc reverse
  obtain ⟨hs,haux⟩ := canonical_fields hn _ h.aux rfl
  simp only [CompactComplexSourceReadyReachedBasisInvariant.replacementCaller,
    CompactComplexSourceReadyReachedDormantFrameInvariant.storageOf_bank] at hs
  refine ⟨hn,hd,?_⟩
  rw [hs,haux]
  exact hsettled

end Basis

section Completion
variable {stage : ActivePrefixStageParameters.Stage sh}
  {rows ell metadataP e p C axes baseline levels frames returned pref n : ℕ}
  {pcStack : Fin s} {origin : ℤ} {calls : List Networks.ComplexRecursiveCallSchema.Call}
  {v : Tapes (nodeTapes s roles) 2}

/-- Actual sink correction, contraction, row rejoin and saved-call orientation
retain settled frames on the computed completed bank's physical ports. -/
theorem completed_settled
    (h : Reached stage rows ell metadataP e p C axes baseline levels frames returned pref n pcStack origin calls v)
    (snapshot : Snapshot s) (hsettled : Settled snapshot h.storage h.aux)
    (hslots : stage.slots=NativeEndpointCharacterRoles.arity) (hd : roles∣rows)
    (call : Networks.ComplexRecursiveCallSchema.Call) :
    Settled snapshot
      (SharedBank.payload (CompactComplexSourceReadyCompletedChildBoundary.completed h hslots hd call)
        CompactComplexNonleafRoleChildBank.storage)
      (SharedBank.payload (CompactComplexSourceReadyCompletedChildBoundary.completed h hslots hd call)
        CompactComplexNonleafRoleParentPayloadContinuation.extra) := by
  have ports := CompactComplexSourceReadyCompletedChildBoundary.completed_dormant
    h hslots hd call snapshot hsettled
  apply CompactComplexSourceReadySettledFrames.settled_of_port_eq
    (CompactComplexSourceReadySettledFrames.captured_settled snapshot
      hsettled.reference_clean hsettled.aux_reference_clean)
  · exact ports.1
  · exact ports.2

end Completion

end
end IntegerMultBounds.Machine.CompactComplexSourceReadySettledEventInvariant
