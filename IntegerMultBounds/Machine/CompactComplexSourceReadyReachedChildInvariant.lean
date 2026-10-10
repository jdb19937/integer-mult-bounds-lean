import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventInvariant
import IntegerMultBounds.Machine.CompactComplexChildInputReadiness
import IntegerMultBounds.Machine.CompactComplexStoppedEventProgress
import IntegerMultBounds.Machine.CompactComplexChildTensorCoordinateFactor
import IntegerMultBounds.Machine.CompactComplexActualCallAlignment

/-! Original physical recursive child entry inherits its selected literal
array, numerical budget, true live denominator and genuine associated call
list. This is an entry invariant, not an assumption of child execution. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedChildInvariant
noncomputable section
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes permanent ready)
open CompactComplexSourceReadyReachedEventInvariant (Reached caller canonical)
open CompactComplexScalarIntegerRows (wireIndex)
open CompactComplexSourceReadyChildEntryPath (selected publicOutput)
open CompactSpectatorInheritedGrid (Width Grid decoded half)
open CompactComplexDenominatorCapacity (ledger scalarRows)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexChildHeadersData (parent child)
open CompactSpectatorVisitGeometry (Array)
open Networks
variable {s : ℕ} {sh : CompactGadgetReservationShape.Shape}
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites
  CompactComplexRolePhaseSite.roleCount CompactComplexCompletedLiveLower.schedule
  ComplexFramedExecution.rows

/-- The actual selected permanent role, with no supplied input-array equality. -/
def selectedArray {stage : ActivePrefixStageParameters.Stage sh}
    {rows ell metadataP e p C axes baseline levels frames returned pref n : ℕ}
    {pcStack : Fin s} {origin : ℤ} {calls : List ComplexRecursiveCallSchema.Call}
    {v : Tapes (nodeTapes s roles) 2}
    (h : Reached stage rows ell metadataP e p C axes baseline levels frames returned pref n pcStack origin calls v)
    (call : ComplexRecursiveCallSchema.Call) : Array sh (rows/roles) ell :=
  h.data (CompactComplexScalarRolePorts.roleIndex.symm (selected call))

private theorem stored_half (metadataP : ℕ) (hp : 2*sh.bits≤metadataP) :
    ButterflyGuard.halfWidth metadataP sh.bits=half sh (metadataP-2*sh.bits) := by
  unfold half ButterflyGuard.halfWidth
  omega

theorem selected_width {stage : ActivePrefixStageParameters.Stage sh}
    {rows ell metadataP e p C axes baseline levels frames returned pref n : ℕ}
    {pcStack : Fin s} {origin : ℤ} {calls : List ComplexRecursiveCallSchema.Call}
    {v : Tapes (nodeTapes s roles) 2}
    (h : Reached stage rows ell metadataP e p C axes baseline levels frames returned pref n pcStack origin calls v)
    (call : ComplexRecursiveCallSchema.Call) (hp : 2*sh.bits≤metadataP) :
    Width sh (rows/roles) ell (metadataP-2*sh.bits) (selectedArray h call) := by
  intro i
  have hi := h.width (CompactComplexScalarRolePorts.roleIndex.symm (selected call)) i
  simpa only [selectedArray,ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq,
    stored_half metadataP hp] using hi

theorem selected_grid {stage : ActivePrefixStageParameters.Stage sh}
    {rows ell metadataP e p C axes baseline levels frames returned pref n : ℕ}
    {pcStack : Fin s} {origin : ℤ} {calls : List ComplexRecursiveCallSchema.Call}
    {v : Tapes (nodeTapes s roles) 2}
    (h : Reached stage rows ell metadataP e p C axes baseline levels frames returned pref n pcStack origin calls v)
    (call : ComplexRecursiveCallSchema.Call) (hp : 2*sh.bits≤metadataP) :
    Grid sh (rows/roles) ell (metadataP-2*sh.bits) n
      (CompactFramedScalarGrid.bound pref
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)))
      (selectedArray h call) := by
  intro i
  have hi := h.grid (wireIndex.symm (CompactComplexScalarRolePorts.roleIndex.symm (selected call))) i
  simpa only [CompactComplexScalarSequenceSemantics.values,Equiv.apply_symm_apply,
    decoded,ButterflyStreamSemantics.decode,selectedArray,stored_half metadataP hp] using hi

/-- A new genuine dependency level pays the parent's one complete scalar
prefix allowance, before any child arithmetic is executed. -/
theorem descent_bound (g p C levels frames returned k : ℕ)
    (call : ComplexRecursiveCallSchema.Call) (hC : CompactFramedScalarGrid.growthConstant≤C) :
    CompactFramedScalarGrid.bound g (CompactRecursiveGridBudget.bound p C levels (frames+2*returned))≤
      CompactRecursiveGridBudget.bound p C (levels+1)
        (frames+arity^(k+2)+2*(returned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(k+1))) := by
  have hg := CompactFramedScalarGrid.bound_le g
    (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) C hC
  rw [CompactRecursiveGridBudget.scalar_step] at hg
  refine hg.trans ?_
  unfold CompactRecursiveGridBudget.bound
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 0<4) (by omega))

/-- The literal child source bank and its true dependency/call invariants. -/
structure Entered (stage : ActivePrefixStageParameters.Stage sh)
    (rows ell metadataP e left p C n baseline levels frames returned : ℕ)
    (pcStack : Fin s) (origin : ℤ) (calls : List ComplexRecursiveCallSchema.Call)
    (f : Array sh rows ell)
    (out : Tapes (CompactComplexSourceReadyWorkspace.publicTapes s roles) 2) : Prop where
  path : CompactRecursiveDependencyBudget.Path sh.active left e levels frames returned
  width : Width sh rows ell (metadataP-2*sh.bits) f
  grid : Grid sh rows ell (metadataP-2*sh.bits) n
    (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) f
  upper_ledger : n≤ledger scalarRows baseline levels frames returned 0
  headers : Placement.active CompactComplexNonleafRoleEntry.headerPlacement
    (CompactComplexNonleafRoleSourceReturn.base out)=ActiveRepairRankHeadersCommands.bank
      (CompactComplexNativeCodec.raw stage rows ell metadataP)
  source : out.head (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=10+s)))=0 ∧
    out.tape (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=10+s)))=CompactSpectatorLeafAxis.word f
  source_support : RoleArrayStack.Supported
    (out.tape (Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=10+s))))
    (CompactComplexSpectatorVolumeHeaders.streamVolume sh roles rows ell metadataP false)
  stop_ready : CompactComplexSourceReadyGuard.Ready out
  dimension : out.head CompactComplexSourceReadyGuard.dimension=1 ∧
    out.tape CompactComplexSourceReadyGuard.dimension=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits sh.axes)
  live : CompactComplexRecursiveLiveProgress.Live out CompactComplexNonleafRoleChildBank.current n
  target_blank : out.head CompactComplexNonleafRoleChildBank.target=0 ∧
    out.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank)
  exponent : out.head (CompactComplexNonleafRoleChildBank.control 1)=1 ∧
    out.tape (CompactComplexNonleafRoleChildBank.control 1)=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits e)
  roles_blank : ∀ j,(CompactComplexNonleafRoleSourceReturn.base out).head
    (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
    (CompactComplexNonleafRoleSourceReturn.base out).tape (CompactComplexNonleafRoleEntry.roleTape j)=(fun _ => blank)
  saved_calls : CompactComplexSourceReadySavedCallHistory.Reached pcStack origin calls
    (ready (CompactComplexSourceReadyWorkspace.ready out))

section Child
variable {left k levels frames returned rows ell metadataP p C baseline pref n : ℕ}
    (rho : Fin sh.chunk)
    (path : CompactRecursiveDependencyBudget.Path sh.active left (k+2) levels frames returned)
    (hactive : sh.active≤sh.axes) (pair : BinaryRowProgram.Op (Fin arity))
    {pcStack : Fin s} {origin : ℤ} {calls : List ComplexRecursiveCallSchema.Call}
    {v : Tapes (nodeTapes s roles) 2}
    (h : Reached (parent rho path.visit hactive pair) rows ell metadataP (k+2) p C 0
      baseline levels frames returned pref n pcStack origin calls v)
    (call : ComplexRecursiveCallSchema.Call)

def childPublic (headerStack liveStack : Fin s) :=
  publicOutput call rho path.visit hactive pair rows ell metadataP (selectedArray h call) (caller h)
    h.targetValue n headerStack pcStack liveStack

private theorem caller_storage (i : Fin (10+s)) :
    (caller h).head (CompactComplexNonleafRoleReturnFrame.oldSlot i)=h.storage.head i ∧
    (caller h).tape (CompactComplexNonleafRoleReturnFrame.oldSlot i)=h.storage.tape i := by
  have he := CompactComplexSourceReadyScalarChildReadiness.entry_prefix
    (CompactComplexNativeCodecFrame.bank h.control h.queue h.scalar
      (CompactComplexNativeCodec.raw (parent rho path.visit hactive pair) rows ell metadataP)
      h.tail h.storage h.payload) h.aux (CompactComplexSpectatorTargetBank.oldSlot i)
  have hb := CompactComplexSpectatorTargetBank.old_bank h.control h.queue h.scalar
    (CompactComplexNativeCodec.raw (parent rho path.visit hactive pair) rows ell metadataP)
    h.tail h.storage h.payload i
  exact ⟨he.1.trans hb.1,he.2.trans hb.2⟩

/-- Actual child entry installs the selected original role and pushes its
real call code. Every input readiness and numerical property is derived. -/
theorem child_entered (headerStack liveStack : Fin s)
    (hh : pcStack≠headerStack) (hl : pcStack≠liveStack)
    (hp : 2*sh.bits≤metadataP) (hC : CompactFramedScalarGrid.growthConstant≤C) :
    Entered (child rho path.visit hactive pair call.slot) (rows/roles) ell metadataP (k+1)
      (left+call.slot.val*arity^(k+1)) p C n baseline (levels+1) (frames+arity^(k+2))
      (returned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(k+1))
      pcStack origin (call::calls) (selectedArray h call) (childPublic rho path hactive pair h call headerStack liveStack) := by
  have hw := selected_width h call hp
  have hg := selected_grid h call hp
  have hgrid : Grid sh (rows/roles) ell (metadataP-2*sh.bits) n
      (CompactRecursiveGridBudget.bound p C (levels+1)
        (frames+arity^(k+2)+2*(returned+CompactRecursiveDependencyBudget.precedingCalls call*arity^(k+1))))
      (selectedArray h call) := by
    intro i
    exact GaussianPrecision.bound_mono (descent_bound pref p C levels frames returned k call hC)
      (by simpa only [Nat.add_zero] using hg i)
  have hl0 := caller_storage rho path hactive pair h ⟨7,by omega⟩
  have hcurrent := CompactComplexChildInputReadiness.entered_current call rho path.visit hactive pair
    rows ell metadataP (selectedArray h call) (caller h) h.targetValue n headerStack pcStack liveStack
  have hsave0 := CompactComplexSourceReadyScalarSavedCallHistory.saved_permanent pcStack v
  have hv := (congrArg permanent h.canonical_bank).trans
    (CompactComplexSourceReadyReachedEventInvariant.canonical_permanent _ _)
  rw [hv] at hsave0
  have hb := CompactComplexSpectatorTargetBank.old_bank h.control h.queue h.scalar
    (CompactComplexNativeCodec.raw (parent rho path.visit hactive pair) rows ell metadataP)
    h.tail h.storage h.payload (Fin.natAdd 10 pcStack)
  change (CompactComplexNativeCodecFrame.bank h.control h.queue h.scalar
      (CompactComplexNativeCodec.raw (parent rho path.visit hactive pair) rows ell metadataP)
      h.tail h.storage h.payload).head
      (CompactComplexScalarCountRootBank.countSlot (Fin.natAdd 10 pcStack))=h.storage.head _ ∧
    (CompactComplexNativeCodecFrame.bank h.control h.queue h.scalar
      (CompactComplexNativeCodec.raw (parent rho path.visit hactive pair) rows ell metadataP)
      h.tail h.storage h.payload).tape
      (CompactComplexScalarCountRootBank.countSlot (Fin.natAdd 10 pcStack))=h.storage.tape _ at hb
  rw [hb.1,hb.2] at hsave0
  change (ready v).head _=h.storage.head (Fin.natAdd 10 pcStack) ∧
    (ready v).tape _=h.storage.tape (Fin.natAdd 10 pcStack) at hsave0
  -- The public caller exposes exactly the same genuinely associated stack.
  have hassoc : CompactComplexSourceReadySavedCallHistory.Associated origin calls
      ((caller h).tape (CompactComplexNonleafRoleReturnFrame.oldSlot (Fin.natAdd 10 pcStack)))
      ((caller h).head (CompactComplexNonleafRoleReturnFrame.oldSlot (Fin.natAdd 10 pcStack))) := by
    have hc := caller_storage rho path hactive pair h (Fin.natAdd 10 pcStack)
    rw [hc.1,hc.2]
    have hs := h.saved_calls
    unfold CompactComplexSourceReadySavedCallHistory.Reached at hs
    rw [hsave0.1,hsave0.2] at hs
    exact hs
  have hpush := CompactComplexSourceReadySavedCallHistory.child_entry_push call rho path.visit hactive pair
    rows ell metadataP (selectedArray h call) (caller h) h.targetValue n headerStack pcStack liveStack hh hl origin calls hassoc
  refine {
    path := CompactRecursiveDependencyBudget.Path.child path call, width := hw, grid := hgrid,
    upper_ledger := ?_, headers := CompactComplexChildInputReadiness.entered_headers call rho path.visit hactive pair
      rows ell metadataP (selectedArray h call) (caller h) h.targetValue n headerStack pcStack liveStack,
    source := CompactComplexChildInputReadiness.entered_source call rho path.visit hactive pair
      rows ell metadataP (selectedArray h call) (caller h) h.targetValue n headerStack pcStack liveStack,
    source_support := ?_, stop_ready := CompactComplexChildInputReadiness.entered_stop_ready call rho path.visit hactive pair
      rows ell metadataP (selectedArray h call) (caller h) h.targetValue n headerStack pcStack liveStack,
    dimension := CompactComplexChildInputReadiness.entered_dimension call rho path.visit hactive pair
      rows ell metadataP (selectedArray h call) (caller h) h.targetValue n headerStack pcStack liveStack,
    live := ?_, target_blank := CompactComplexChildInputReadiness.entered_target call rho path.visit hactive pair
      rows ell metadataP (selectedArray h call) (caller h) h.targetValue n headerStack pcStack liveStack,
    exponent := CompactComplexChildInputReadiness.entered_exponent call rho path.visit hactive pair
      rows ell metadataP (selectedArray h call) (caller h) h.targetValue n headerStack pcStack liveStack,
    roles_blank := CompactComplexChildInputReadiness.entered_roles call rho path.visit hactive pair
      rows ell metadataP (selectedArray h call) (caller h) h.targetValue n headerStack pcStack liveStack,
    saved_calls := CompactComplexSourceReadySavedCallHistory.ready_associated pcStack origin (call::calls) _ _ hpush }
  · apply CompactComplexDenominatorCapacity.child_entry scalarRows baseline levels frames returned
      (CompactFramedScalarGrid.rows pref).length n (k+1) call (CompactComplexDenominatorCapacity.actual_prefix pref)
    exact h.upper_ledger.trans (by unfold ledger; omega)
  · apply CompactComplexChildInputReadiness.entered_source_supported call rho path.visit hactive pair
      rows ell metadataP (selectedArray h call) (caller h) h.targetValue n headerStack pcStack liveStack
    exact h.width _
  · exact ⟨hcurrent.1.trans (hl0.1.trans h.live.1),hcurrent.2.trans (hl0.2.trans h.live.2)⟩

include rho path in
/-- Every signed child guard is paid by the actual parent prefix and retained
reserve; no working-width or child-execution certificate is supplied. -/
theorem selected_guard (ha : 0<sh.active) (hp : p+2*sh.bits≤metadataP)
    (hC : CompactFramedScalarGrid.growthConstant≤C)
    (hroom : CompactSpectatorInheritedGrid.dependencyCoefficient C+Nat.clog 2 (C+1)+
      CompactComplexScalarIntegerRows.guardBits≤sh.chunk) :
    4*(CompactFramedScalarGrid.bound pref
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned))*4^(arity^(k+1)))<
      2^(half sh (metadataP-2*sh.bits)) := by
  have hbits := CompactSpectatorLeafSemantics.count_le_bits sh rho path.visit
  have hpow : arity^(k+1)≤arity^(k+2) :=
    Nat.pow_le_pow_right (by decide : 0<arity) (by omega)
  simpa only [Nat.add_zero,Nat.zero_add] using
    CompactComplexStoppedEventProgress.prefix_guard_from_path path pref p C 0 (arity^(k+1)) metadataP
      ha hp (by omega) hC hroom

/-- The parent invariant supplies the real target/live/exponent and payload
premises of the paid physical child-entry program. -/
theorem child_entry_runs (headerStack liveStack : Fin s)
    (hp : p+2*sh.bits≤metadataP) (hbase : baseline≤p)
    (hroom : CompactComplexDenominatorCapacity.room scalarRows≤sh.chunk)
    (hrows : 0<rows/roles) (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) :
    HoareTime (CompactComplexSourceReadyChildEntryPath.program headerStack pcStack liveStack call)
      (fun z => z=v)
      (fun z => z=CompactComplexSourceReadyWorkspace.ready
        (childPublic rho path hactive pair h call headerStack liveStack))
      (CompactComplexSourceReadyChildEntryPath.bound (sh:=sh) rows ell metadataP) := by
  have hx := CompactComplexSourceReadyReachedEventInvariant.child_exponent h
  rw [h.exponentValue_eq] at hx
  have htarget := caller_storage rho path hactive pair h ⟨8,by omega⟩
  have hlive := caller_storage rho path hactive pair h ⟨7,by omega⟩
  have hr : 0<rows := by
    have hmul : 0<rows/roles*roles := Nat.mul_pos hrows (by norm_num [roles,CompactComplexRolePhaseSite.roleCount])
    exact lt_of_lt_of_le hmul (Nat.div_mul_le_self rows roles)
  let budget : CompactComplexNonleafRoleChildBankBudget.Ledger sh metadataP n h.targetValue left (k+2) := {
    R := scalarRows, baseline := baseline, levels := levels, frames := frames, returned := returned,
    used := (CompactFramedScalarGrid.rows pref).length, path := path,
    metadata := by omega, base := by omega, room := hroom,
    used_le := CompactComplexDenominatorCapacity.actual_prefix pref,
    live := h.upper_ledger, target_growth := h.target_growth }
  have hs := CompactComplexSourceReadyReachedEventInvariant.child_source h
  have htape : (caller h).tape (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨8,by omega⟩)=
      BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits h.targetValue) := by
    exact (htarget.2.trans h.target.2).trans (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm
  have hntape : (caller h).tape (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨7,by omega⟩)=
      BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits n) := by
    exact (hlive.2.trans h.live.2).trans (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm
  have hroles : ∀ j,(caller h).head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      RoleArrayStack.Supported ((caller h).tape (CompactComplexNonleafRoleEntry.roleTape j))
        (CompactComplexSpectatorVolumeHeaders.streamVolume sh roles rows ell metadataP true) := by
    intro j
    have he := CompactComplexSourceReadyScalarChildReadiness.entry_prefix
      (CompactComplexNativeCodecFrame.bank h.control h.queue h.scalar
        (CompactComplexNativeCodec.raw (parent rho path.visit hactive pair) rows ell metadataP)
        h.tail h.storage h.payload) h.aux (CompactComplexNativeRoleBridge.roleSlot j)
    have hw := h.role_words (CompactComplexScalarRolePorts.roleIndex.symm j)
    simp only [Equiv.apply_symm_apply] at hw
    refine ⟨he.1.trans hw.1,?_⟩
    simpa only [Equiv.apply_symm_apply] using
      CompactComplexSourceReadyReachedEventInvariant.child_role_supported h (CompactComplexScalarRolePorts.roleIndex.symm j)
  have hf : (caller h).tape (CompactComplexNonleafRoleEntry.roleTape (selected call))=
      NativeZeroPadding.word (NativeZeroPaddingArray.word (selectedArray h call)) := by
    have he := CompactComplexSourceReadyScalarChildReadiness.entry_prefix
      (CompactComplexNativeCodecFrame.bank h.control h.queue h.scalar
        (CompactComplexNativeCodec.raw (parent rho path.visit hactive pair) rows ell metadataP)
        h.tail h.storage h.payload) h.aux (CompactComplexNativeRoleBridge.roleSlot (selected call))
    have hw := h.role_words (CompactComplexScalarRolePorts.roleIndex.symm (selected call))
    simp only [Equiv.apply_symm_apply] at hw
    exact he.2.trans hw.2
  have hrun := CompactComplexSourceReadyChildEntryPath.runs_linear call rho path.visit hactive pair
    rows ell metadataP (selectedArray h call) (caller h) h.targetValue n headerStack pcStack liveStack budget hx
    htape (htarget.1.trans h.target.1) hntape (hlive.1.trans h.live.1) hr hrows hG hA hK
    (CompactComplexSourceReadyReachedEventInvariant.child_headers h)
    (CompactComplexSourceReadyReachedEventInvariant.child_clock h)
    ⟨hs.1,by rw [hs.2]; intro z hz; rfl⟩ hroles hf
    (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2) (SharedBank.empty 10 2)
  have hv : v=CompactComplexSourceReadyWorkspace.ready ((caller h).append (SharedBank.empty 7 2)) :=
    h.canonical_bank
  exact hrun.consequence (fun _ hz => hz.trans hv) (fun _ hz => hz) le_rfl

end Child
end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedChildInvariant
