module

public import IntegerMultBounds.Machine.CompactComplexAlignedChildReturnPath
public import IntegerMultBounds.Machine.CompactComplexAlignedCompletedReturnReadiness

/-! The inverse basis pass uses the original fixed program and original call.
Output width comes from the actual completed child, and promotion capacity and
guard from the actual parent dependency path. Only recursive output grid and
physical restored-port facts remain explicit boundary obligations. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexAlignedCompletedInverse
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes ready)
open CompactComplexSourceReadyReachedEventInvariant (Reached canonical)
open CompactComplexSourceReadyReachedReturnInvariant (Restored returnedCaller returnedData promotion_guard)
open CompactComplexSourceReadyReachedBasisInvariant (basisArray replacementCaller replacementData)
open Networks.ComplexRecursiveCallSchema (Call)
variable {q : ℕ}
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  CompactComplexRolePhaseSite.roleCount CompactComplexCompletedLiveLower.schedule

/-- The literal completed-child result supplies its own stored widths to the
same fixed inverse program, selected by the original call's role and PC. -/
theorem runs_from_path (D : ℕ) (P : Program ActivePrefixStageNative.tapes q prime) (K : ℝ)
    (hP : CompactComplexAlignedChildEntryPath.BasisRuns D q P K) :
    ∀ (s : ℕ) (sh : CompactGadgetReservationShape.Shape) (stage : ActivePrefixStageParameters.Stage sh)
      (rows ell metadataP e p C axes baseline levels frames returned pref n : ℕ)
      (pcStack : Fin s) (origin : ℤ) (calls : List Call) (v : Tapes (nodeTapes s roles) 2)
      (h : Reached stage rows ell metadataP e p C axes baseline levels frames returned pref n pcStack origin calls v)
      (call : Call) (childStage : ActivePrefixStageParameters.Stage sh)
      (ce cp cC caxes cbaseline clevels cframes creturned cpref cn : ℕ)
      (cv : Tapes (nodeTapes s roles) 2)
      (hc : Reached childStage (rows/roles) ell metadataP ce cp cC caxes cbaseline
        clevels cframes creturned cpref cn pcStack origin (call::calls) cv)
      (hchildSlots : childStage.slots=NativeEndpointCharacterRoles.arity)
      (hchildRows : roles∣rows/roles) (gap volume left : ℕ)
      (_path : CompactRecursiveDependencyBudget.Path sh.active left e levels frames returned)
      (_ha : 0<sh.active) (_hp : p+2*sh.bits≤metadataP) (_haxes : axes+gap≤sh.bits)
      (_hC : CompactFramedScalarGrid.growthConstant≤C)
      (_hroom : CompactSpectatorInheritedGrid.dependencyCoefficient C+Nat.clog 2 (C+1)+
        CompactComplexScalarIntegerRows.guardBits≤sh.chunk) (_hgap : gap≤2*volume)
      (_hgrid : CompactSpectatorInheritedGrid.Grid sh (rows/roles) ell (metadataP-2*sh.bits) (n+gap)
        (CompactFramedScalarGrid.bound pref
          (CompactRecursiveGridBudget.bound p C levels (frames+2*(returned+volume)+axes))) (CompactComplexSourceReadyCompletedChildBoundary.result hc hchildSlots hchildRows call))
      (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
      (tail : Tapes 22 2) (storage : Tapes (10+s) 2) (aux : Tapes 2 2)
      (_physical : Restored e (n+gap) h.targetValue pcStack origin calls control storage aux)
      (hG : 1≤sh.guard) (hGK : sh.guard+1≤sh.chunk) (_hr : 0<rows) (hm : 0<rows/roles)
      (_hd : roles∣rows) (_hpay : sh.payload=1) (hslots : stage.slots=25^3)
      (hpack : ∀ op,1<stage.f → ActivePrefixStageRuntimeData.Packed
        (ActivePrefixStagePairData.changePair
          (CompactComplexSourceReadyReachedBasisInvariant.input stage (rows/roles) ell metadataP hG hGK hm) op) D),
      let d := CompactComplexSourceReadyReachedBasisInvariant.input stage (rows/roles) ell metadataP hG hGK hm
      let start := canonical (returnedCaller h (CompactComplexRolePhaseSite.role call.site) gap (CompactComplexSourceReadyCompletedChildBoundary.result hc hchildSlots hchildRows call) control queue scalar tail storage) aux
      ∃ hn : Reached stage rows ell metadataP e p C axes baseline levels frames (returned+volume) pref
        (n+gap) pcStack origin calls start,
        hn.data=returnedData h (CompactComplexRolePhaseSite.role call.site) gap (CompactComplexSourceReadyCompletedChildBoundary.result hc hchildSlots hchildRows call) ∧
        let after := basisArray stage (rows/roles) ell metadataP hG hGK hm hslots (CompactComplexRolePhaseSite.pc call.site) true
          (hn.data (CompactComplexScalarRolePorts.roleIndex.symm (CompactComplexRolePhaseSite.role call.site)))
        let passTime := CompactNativeConjugatedSharedCaller.cost (CompactNativeRoleSourcePorts.callerTapes 44 roles) d ell
          (CompactComplexActualCallAlignment.nativeCost D d hslots (CompactComplexRolePhaseSite.pc call.site) true
            (ActivePrefixStageNativePolynomial.symbols (2^ell) (NativePolynomialStageShape.width sh metadataP)) hpack)
        ∃ ha : Reached stage rows ell metadataP e p C axes baseline levels frames (returned+volume) pref
          (n+gap) pcStack origin calls (canonical (replacementCaller hn (CompactComplexRolePhaseSite.role call.site) after) hn.aux),
          ha.data=replacementData hn (CompactComplexRolePhaseSite.role call.site) after ∧
          HoareTime (CompactComplexActualCallFullAlignment.roleProgram P s roles (CompactComplexRolePhaseSite.role call.site) (CompactComplexRolePhaseSite.pc call.site) true)
            (fun z => z=CleanSubbank.bank (Alphabet.mapTapes CompactNativeRoleConjugatedPorts.encoding (ready start)))
            (fun z => z=CleanSubbank.bank (Alphabet.mapTapes CompactNativeRoleConjugatedPorts.encoding
              (ready (canonical (replacementCaller hn (CompactComplexRolePhaseSite.role call.site) after) hn.aux))))
            (CompactComplexActualCallRoleAlignment.cost roles stage rows ell metadataP passTime) ∧
          (CompactComplexActualCallRoleAlignment.cost roles stage rows ell metadataP passTime : ℝ)≤
            K*ActivePrefixStageInverseBudget.scale d := by
  intro s sh stage rows ell metadataP e p C axes baseline levels frames returned pref n pcStack origin calls v h
    call childStage ce cp cC caxes cbaseline clevels cframes creturned cpref cn cv hc hchildSlots hchildRows
    gap volume left path ha hp haxes hC hroom hgap hgrid control queue scalar tail storage aux physical
    hG hGK hr hm hd hpay hslots hpack
  have hmetadata : 2*sh.bits≤metadataP := by omega
  have hw := CompactComplexSourceReadyCompletedChildWidth.result_lengths hc hchildSlots hchildRows hmetadata call
  have hg := promotion_guard (pref:=pref) path gap ha hp haxes hC hroom
  exact CompactComplexAlignedChildReturnPath.restored_inverse_runs D P K hP
    s sh stage rows ell metadataP e p C axes baseline levels frames returned pref n pcStack origin calls v h
    (CompactComplexRolePhaseSite.role call.site) (CompactComplexRolePhaseSite.pc call.site) gap volume
    (CompactComplexSourceReadyCompletedChildBoundary.result hc hchildSlots hchildRows call)
    hmetadata hgap hw hgrid hg.1 hg.2 control queue scalar tail storage aux physical
    hG hGK hr hm hd hpay hslots hpack

end
end IntegerMultBounds.Machine.CompactComplexAlignedCompletedInverse
