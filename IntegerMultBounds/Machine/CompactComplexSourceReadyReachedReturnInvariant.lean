module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedBasisInvariant
public import IntegerMultBounds.Machine.CompactComplexSourceReadyNormalizedChildReturnPath

/-! Numerical return preservation for the literal normalized spectator
payload. A returned child's grid is a recursive invariant, not a completed
network equality. The original scalar prefix, node target and saved calls are
retained, while the actual live advance is charged to the returned ledger. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedReturnInvariant
noncomputable section
open ActivePrefixStageParameters (Stage)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Width Grid decoded half)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes ready permanent)
open CompactComplexSourceReadyReachedEventInvariant (Reached canonical)
open Networks.GaussianPrecision (BoundedGrid)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {s : ℕ} {sh : CompactGadgetReservationShape.Shape}
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount Networks.ComplexRank25.program
  Networks.ComplexFramedExecution.rows CompactComplexCompletedLiveLower.schedule
  CompactComplexScalarIntegerRows.wireIndex CompactComplexScalarRolePorts.roleIndex

section Return
variable {stage : Stage sh} {rows ell metadataP e p C axes baseline levels frames returned pref n : ℕ}
    {pcStack : Fin s} {origin : ℤ} {calls : List Networks.ComplexRecursiveCallSchema.Call}
    {v : Tapes (nodeTapes s roles) 2}
    (h : Reached stage rows ell metadataP e p C axes baseline levels frames returned pref n pcStack origin calls v)

def roleData := fun j : Fin roles => h.data (CompactComplexScalarRolePorts.roleIndex.symm j)

def returnedData (selected : Fin roles) (gap : ℕ) (child : Array sh (rows/roles) ell) :=
  fun a => CompactComplexNormalizedSpectatorHandoff.aligned sh (rows/roles) ell gap selected
    (roleData h) child (CompactComplexScalarRolePorts.roleIndex a)

theorem inherited_half_eq (hmetadata : 2*sh.bits≤metadataP) :
    half sh (metadataP-2*sh.bits)=ButterflyGuard.halfWidth metadataP sh.bits := by
  unfold half ButterflyGuard.halfWidth
  omega

theorem role_width (hmetadata : 2*sh.bits≤metadataP) :
    ∀ j,Width sh (rows/roles) ell (metadataP-2*sh.bits) (roleData h j) := by
  intro j i
  have hw := h.width (CompactComplexScalarRolePorts.roleIndex.symm j) i
  simpa only [roleData,Width,ButterflyGuard.width,
    ButterflyIndependentGuardSemantics.half_eq,
    inherited_half_eq hmetadata] using hw

theorem role_grid (hmetadata : 2*sh.bits≤metadataP) : ∀ j,Grid sh (rows/roles) ell (metadataP-2*sh.bits) n
    (CompactFramedScalarGrid.bound pref
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes))) (roleData h j) := by
  intro j i
  simpa only [roleData,CompactComplexScalarSequenceSemantics.values,Equiv.apply_symm_apply,
    decoded,inherited_half_eq hmetadata,ButterflyStreamSemantics.decode] using
    h.grid (CompactComplexScalarIntegerRows.wireIndex.symm
      (CompactComplexScalarRolePorts.roleIndex.symm j)) i

/-- Literal spectator promotion retains stored widths; the selected stream
uses the width supplied by the returned child invariant. -/
theorem returned_width (selected : Fin roles) (gap : ℕ) (child : Array sh (rows/roles) ell)
    (hw : ∀ i,(child i).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (child i).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1) :
    ∀ a i,(returnedData h selected gap child a i).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (returnedData h selected gap child a i).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1 := by
  intro a i
  unfold returnedData CompactComplexNormalizedSpectatorHandoff.aligned
  split_ifs
  · exact hw i
  · have hp := CompactComplexChildGridPromoted.coefficient_width gap (roleData h (CompactComplexScalarRolePorts.roleIndex a) i)
    exact ⟨hp.1.trans (h.width _ i).1,hp.2.trans (h.width _ i).2⟩

/-- A genuine dependency path derives the signed promotion guard. -/
theorem promotion_guard {left : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left e levels frames returned)
    (gap : ℕ) (ha : 0<sh.active) (hp : p+2*sh.bits≤metadataP)
    (haxes : axes+gap≤sh.bits) (hC : CompactFramedScalarGrid.growthConstant≤C)
    (hroom : CompactSpectatorInheritedGrid.dependencyCoefficient C+Nat.clog 2 (C+1)+
      CompactComplexScalarIntegerRows.guardBits≤sh.chunk) :
    gap≤half sh (metadataP-2*sh.bits)+1 ∧
    CompactFramedScalarGrid.bound pref
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes))*2^gap<
      2^(half sh (metadataP-2*sh.bits)) := by
  have hg := CompactComplexStoppedEventProgress.prefix_guard_from_path path pref p C axes
    gap metadataP ha hp haxes hC hroom
  constructor
  · unfold half ButterflyGuard.halfWidth
    omega
  · have hm := Nat.mul_le_mul_left
      (CompactFramedScalarGrid.bound pref
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)))
      (Nat.pow_le_pow_left (show 2≤4 by decide) gap)
    exact (hm.trans (by omega)).trans_lt hg

/-- The actual selected child grid and literal spectator shifts retain the
parent's exact scalar prefix. No network execution equality is required. -/
theorem returned_grid (selected : Fin roles) (gap volume : ℕ) (child : Array sh (rows/roles) ell)
    (hmetadata : 2*sh.bits≤metadataP) (hgap : gap≤2*volume)
    (hc : Grid sh (rows/roles) ell (metadataP-2*sh.bits) (n+gap)
      (CompactFramedScalarGrid.bound pref
        (CompactRecursiveGridBudget.bound p C levels (frames+2*(returned+volume)+axes))) child)
    (hcapacity : gap≤half sh (metadataP-2*sh.bits)+1)
    (hguard : CompactFramedScalarGrid.bound pref
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes))*2^gap<
        2^(half sh (metadataP-2*sh.bits))) :
    (∀ a i,BoundedGrid (n+gap)
      (CompactFramedScalarGrid.bound pref
        (CompactRecursiveGridBudget.bound p C levels (frames+2*(returned+volume)+axes)))
      (CompactComplexScalarSequenceSemantics.values (ButterflyGuard.halfWidth metadataP sh.bits)
        (n+gap) (returnedData h selected gap child) i a)) ∧
    (∀ j,j≠selected → decoded sh (rows/roles) ell (metadataP-2*sh.bits) (n+gap)
      (CompactComplexNormalizedSpectatorHandoff.aligned sh (rows/roles) ell gap selected (roleData h) child j)=
      decoded sh (rows/roles) ell (metadataP-2*sh.bits) n (roleData h j)) := by
  have hs : ∀ j,j≠selected → decoded sh (rows/roles) ell (metadataP-2*sh.bits) (n+gap)
      (CompactComplexNormalizedSpectatorHandoff.aligned sh (rows/roles) ell gap selected (roleData h) child j)=
      decoded sh (rows/roles) ell (metadataP-2*sh.bits) n (roleData h j) := by
    intro j hj
    funext i
    simp only [CompactComplexNormalizedSpectatorHandoff.aligned,ite_eq_right hj]
    exact CompactComplexChildGridAlignment.decode_promotes _ n gap _ _
      (CompactComplexChildGridPromoted.promotes sh (rows/roles) ell (metadataP-2*sh.bits) n _ gap
        (roleData h j) (role_width h hmetadata j) (role_grid h hmetadata j) hcapacity hguard i)
  refine ⟨?_,hs⟩
  intro a i
  rw [←inherited_half_eq hmetadata]
  change BoundedGrid (n+gap) _ (decoded sh (rows/roles) ell (metadataP-2*sh.bits) (n+gap)
    (CompactComplexNormalizedSpectatorHandoff.aligned sh (rows/roles) ell gap selected
      (roleData h) child (CompactComplexScalarRolePorts.roleIndex (CompactComplexScalarIntegerRows.wireIndex a))) i)
  by_cases hj : CompactComplexScalarRolePorts.roleIndex (CompactComplexScalarIntegerRows.wireIndex a)=selected
  · simpa only [CompactComplexNormalizedSpectatorHandoff.aligned,hj,ite_true] using hc i
  · rw [hs _ hj]
    apply Networks.GaussianPrecision.bound_mono _ (Networks.GaussianPrecision.bounded_raise (role_grid h hmetadata _ i) gap)
    rw [←CompactComplexNonleafEventProgress.prefix_bound pref p C levels frames returned axes volume]
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (show 2≤4 by decide) gap).trans
      (Nat.pow_le_pow_right (show 1≤4 by decide) hgap))

include h in
/-- The physical common-live update is paid by the original returned ledger. -/
theorem returned_ledger (gap volume : ℕ) (hgap : gap≤2*volume) :
    n+gap≤CompactComplexDenominatorCapacity.ledger CompactComplexDenominatorCapacity.scalarRows baseline
      levels frames (returned+volume) (CompactFramedScalarGrid.rows pref).length :=
  CompactComplexDenominatorCapacity.returned_advance CompactComplexDenominatorCapacity.scalarRows baseline levels frames returned
    (CompactFramedScalarGrid.rows pref).length n (n+gap) volume h.upper_ledger (by omega)

/-- Physical return fragments are individual tape assertions. They permit
the actual decoded return projections, without equating them to a fictional
restored copy of the old parent bank or assuming a machine execution. -/
structure Restored (e advanced target : ℕ) (pcStack : Fin s) (origin : ℤ)
    (calls : List Networks.ComplexRecursiveCallSchema.Call)
    (control : Tapes 43 2) (storage : Tapes (10+s) 2) (aux : Tapes 2 2) : Prop where
  count_blank : storage.head CompactComplexSourceReadyActualTable.countHeader=0 ∧
    storage.tape CompactComplexSourceReadyActualTable.countHeader=(fun _ => blank)
  exponent : control.head 1=1 ∧ control.tape 1=BinaryDescriptorStack.descriptor (bits e)
  control28_blank : control.head 28=0 ∧ control.tape 28=(fun _ => blank)
  control29_blank : control.head 29=0 ∧ control.tape 29=(fun _ => blank)
  live : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits advanced)
  target_word : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=RadixZeroFill.encodedBinary (bits target)
  clock_blank : aux.head 1=0 ∧ aux.tape 1=(fun _ => blank)
  aux_free : CompactComplexSourceReadyPrefixReadiness.BlankAfter aux 0
  saved : CompactComplexSourceReadySavedCallHistory.Associated origin calls
    (storage.tape (Fin.natAdd 10 pcStack)) (storage.head (Fin.natAdd 10 pcStack))

def returnedPayload (selected : Fin roles) (gap : ℕ) (child : Array sh (rows/roles) ell) :=
  CompactComplexStoppedGridHandoff.payload sh (rows/roles) ell (fun _ => blank) 0
    (CompactComplexNormalizedSpectatorHandoff.aligned sh (rows/roles) ell gap selected (roleData h) child)

def returnedCaller (selected : Fin roles) (gap : ℕ) (child : Array sh (rows/roles) ell)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+s) 2) :=
  CompactComplexNativeCodecFrame.bank control queue scalar (CompactComplexNativeCodec.raw stage rows ell metadataP)
    tail storage (returnedPayload h selected gap child)

/-- The exact decoded-return payload, with its genuinely restored physical
fragments, is a next parent Reached. All width, grid and denominator-budget
facts are derived from the old parent and the returned child's numerical grid.
Only local physical tape facts remain in Restored. -/
theorem returned_reached (selected : Fin roles) (gap volume : ℕ) (child : Array sh (rows/roles) ell)
    (hmetadata : 2*sh.bits≤metadataP) (hgap : gap≤2*volume)
    (hw : ∀ i,(child i).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (child i).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1)
    (hc : Grid sh (rows/roles) ell (metadataP-2*sh.bits) (n+gap)
      (CompactFramedScalarGrid.bound pref
        (CompactRecursiveGridBudget.bound p C levels (frames+2*(returned+volume)+axes))) child)
    (hcapacity : gap≤half sh (metadataP-2*sh.bits)+1)
    (hguard : CompactFramedScalarGrid.bound pref
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes))*2^gap<
        2^(half sh (metadataP-2*sh.bits)))
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+s) 2) (aux : Tapes 2 2)
    (physical : Restored e (n+gap) h.targetValue pcStack origin calls control storage aux) :
    ∃ hn : Reached stage rows ell metadataP e p C axes baseline levels frames (returned+volume) pref
      (n+gap) pcStack origin calls (canonical (returnedCaller h selected gap child control queue scalar tail storage) aux),
      hn.data=returnedData h selected gap child := by
  let w := returnedCaller h selected gap child control queue scalar tail storage
  have hsave : CompactComplexSourceReadySavedCallHistory.Reached pcStack origin calls
      (ready (canonical w aux)) := by
    have hs := CompactComplexSourceReadyScalarSavedCallHistory.saved_permanent pcStack (canonical w aux)
    unfold CompactComplexSourceReadySavedCallHistory.Reached
    rw [hs.1,hs.2,CompactComplexSourceReadyReachedEventInvariant.canonical_permanent]
    have hb := CompactComplexSpectatorTargetBank.old_bank control queue scalar
      (CompactComplexNativeCodec.raw stage rows ell metadataP) tail storage
      (returnedPayload h selected gap child) (Fin.natAdd 10 pcStack)
    change CompactComplexSourceReadySavedCallHistory.Associated origin calls
      (w.tape (CompactComplexScalarCountRootBank.countSlot (Fin.natAdd 10 pcStack)))
      (w.head (CompactComplexScalarCountRootBank.countSlot (Fin.natAdd 10 pcStack)))
    change w.head (CompactComplexScalarCountRootBank.countSlot (Fin.natAdd 10 pcStack))=storage.head _ ∧
      w.tape (CompactComplexScalarCountRootBank.countSlot (Fin.natAdd 10 pcStack))=storage.tape _ at hb
    rw [hb.1,hb.2]
    exact physical.saved
  refine ⟨{
    control := control, queue := queue, scalar := scalar, tail := tail,
    storage := storage, payload := returnedPayload h selected gap child, aux := aux,
    data := returnedData h selected gap child, canonical_bank := rfl,
    width := returned_width h selected gap child hw, count_blank := physical.count_blank,
    role_words := ?_, source_blank := ?_, clock_blank := physical.clock_blank, aux_free := physical.aux_free,
    exponentValue := e, exponentValue_eq := rfl, exponent := physical.exponent,
    control28_blank := physical.control28_blank, control29_blank := physical.control29_blank,
    live := physical.live, targetValue := h.targetValue, target := physical.target_word,
    target_growth := by have ht := h.target_growth; omega,
    upper_ledger := returned_ledger h gap volume hgap,
    grid := (returned_grid h selected gap volume child hmetadata hgap hc hcapacity hguard).1,
    saved_calls := hsave },rfl⟩
  · intro a
    have hb := CompactComplexSpectatorTargetBank.role_bank control queue scalar
      (CompactComplexNativeCodec.raw stage rows ell metadataP) tail storage
      (returnedPayload h selected gap child) (CompactComplexScalarRolePorts.roleIndex a)
    refine ⟨hb.1.trans ?_,hb.2.trans ?_⟩
    · simp only [returnedPayload,CompactComplexStoppedGridHandoff.payload,CyclicRowCopy.payload,
        Tapes.append,Fin.addCases_right]
    · simp only [returnedPayload,CompactComplexStoppedGridHandoff.payload,CyclicRowCopy.payload,
        Tapes.append,Fin.addCases_right,returnedData]
      exact CompactComplexStoppedGridHandoff.words_tape _
  · simp only [returnedPayload,CompactComplexStoppedGridHandoff.payload,CyclicRowCopy.payload,
      Tapes.append,Fin.addCases_left]
    exact ⟨trivial,trivial⟩

/-- Public return packaging derives the promotion guard and capacity from
the real parent dependency path. The remaining child certificate is its
numerical output invariant, with no supplied network equality or execution. -/
theorem returned_reached_from_path {left : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left e levels frames returned)
    (selected : Fin roles) (gap volume : ℕ) (child : Array sh (rows/roles) ell)
    (ha : 0<sh.active) (hp : p+2*sh.bits≤metadataP) (haxes : axes+gap≤sh.bits)
    (hC : CompactFramedScalarGrid.growthConstant≤C)
    (hroom : CompactSpectatorInheritedGrid.dependencyCoefficient C+Nat.clog 2 (C+1)+
      CompactComplexScalarIntegerRows.guardBits≤sh.chunk) (hgap : gap≤2*volume)
    (hw : ∀ i,(child i).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (child i).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1)
    (hc : Grid sh (rows/roles) ell (metadataP-2*sh.bits) (n+gap)
      (CompactFramedScalarGrid.bound pref
        (CompactRecursiveGridBudget.bound p C levels (frames+2*(returned+volume)+axes))) child)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+s) 2) (aux : Tapes 2 2)
    (physical : Restored e (n+gap) h.targetValue pcStack origin calls control storage aux) :
    ∃ hn : Reached stage rows ell metadataP e p C axes baseline levels frames (returned+volume) pref
      (n+gap) pcStack origin calls (canonical (returnedCaller h selected gap child control queue scalar tail storage) aux),
      hn.data=returnedData h selected gap child := by
  have hg := promotion_guard (pref:=pref) path gap ha hp haxes hC hroom
  exact returned_reached h selected gap volume child (by omega) hgap hw hc hg.1 hg.2
    control queue scalar tail storage aux physical

end Return
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedReturnInvariant
