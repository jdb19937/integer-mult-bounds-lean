module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyAlignedActualTable
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedChildInvariant
public import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafFinalGeometry
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedBasisInvariant

/-! Actual aligned child-call prefixes in the fixed prime-alphabet table.
The physical forward basis pass runs before literal original child entry;
canonical raw parent metadata is restored between the two programs. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexAlignedChildEntryPath
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactNativeRoleConjugatedPorts (encoding)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes ready)
open CompactComplexActualCallFullAlignment (localTapes tapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached canonical)
open Networks.ComplexRecursiveCallSchema (Call)
open CompactComplexCompletedLiveLower (Event schedule)
variable {s q : ℕ}
attribute [local irreducible] Networks.ComplexRank25.program
  Networks.ComplexRecursiveCallSchema.sites schedule CompactComplexRolePhaseSite.roleCount

/-- Exact original full-bank geometry, retaining the real auxiliary clock
and payload stack, the seven Entry frames and all fixed private workspaces. -/
theorem canonical_full (w : Tapes (CompactComplexSourceReadyScalarWorkspace.permanentTapes s roles) 2)
    (aux : Tapes 2 2) :
    CompactComplexActualCallFullAlignment.bank w (aux.append (SharedBank.empty 7 2))
      (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2)
      (SharedBank.empty 10 2) (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)=
      ready (canonical w aux) := by
  unfold CompactComplexActualCallFullAlignment.bank
  rw [CompactComplexSourceReadyNonleafFinalGeometry.entry_append]
  rfl


private theorem reindex_setTape {a L K : ℕ} (e : Fin L ≃ Fin K)
    (v : Tapes L a) (i : Fin L) (f : ℤ → Fin (a+4)) :
    SharedPlacementAlphabet.setTape (v.reindex e) (e i) f 0=
      (SharedPlacementAlphabet.setTape v i f 0).reindex e := by
  apply congrArg₂ Tapes.mk <;> funext j
  all_goals
    by_cases hj : j=e i
    · subst j
      simp [SharedPlacementAlphabet.setTape,Tapes.reindex]
    · have hj' : e.symm j≠i := fun h => hj (by rw [←h]; simp)
      simp [SharedPlacementAlphabet.setTape,Tapes.reindex,hj,hj']

/-- A selected permanent tape update lifts literally across all retained
public/Entry/leaf/work/scalar frames, without moving their tape indices. -/
theorem full_setTape (w : Tapes (CompactComplexSourceReadyScalarWorkspace.permanentTapes s roles) 2)
    (frame : Tapes 9 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (work : Tapes 10 2) (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (i : Fin (CompactComplexSourceReadyScalarWorkspace.permanentTapes s roles)) (f : ℤ → Fin 6) :
    SharedPlacementAlphabet.setTape (CompactComplexActualCallFullAlignment.bank w frame leaf work scratch)
      (CompactComplexActualCallFullAlignment.prefixSlot i) f 0=
      CompactComplexActualCallFullAlignment.bank (SharedPlacementAlphabet.setTape w i f 0) frame leaf work scratch := by
  unfold CompactComplexActualCallFullAlignment.bank CompactComplexActualCallFullAlignment.prefixSlot
    CompactComplexSourceReadyWorkspace.bank
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left,
    SharedPlacementAlphabet.setTape_append_left]
  unfold CompactComplexNonleafSpectatorTargetRestore.entry
  rw [reindex_setTape,SharedPlacementAlphabet.setTape_append_left]

/-- The exact physical selected-role output is the canonical reached layout
with only that permanent word replaced. -/
theorem canonical_setTape (w : Tapes (CompactComplexSourceReadyScalarWorkspace.permanentTapes s roles) 2)
    (aux : Tapes 2 2) (i : Fin (CompactComplexSourceReadyScalarWorkspace.permanentTapes s roles))
    (f : ℤ → Fin 6) :
    SharedPlacementAlphabet.setTape (ready (canonical w aux))
      (CompactComplexActualCallFullAlignment.prefixSlot i) f 0=
      ready (canonical (SharedPlacementAlphabet.setTape w i f 0) aux) := by
  rw [←canonical_full,full_setTape,canonical_full]

open CompactComplexSourceReadyReachedBasisInvariant
open CompactAllAxisPhaseDispatch (count)

/-- The genuine native witness performs the selected basis permutation on
any reached bank and returns the exact canonical replacement, with private
workspace blank and the original raw total row count restored. -/
theorem exists_basis_runs (D : ℕ) (hc : 0<roles) :
    ∃ q, ∃ P : Program ActivePrefixStageNative.tapes q prime,
    ∃ K : ℝ,0<K ∧
    ∀ (s : ℕ) (sh : CompactGadgetReservationShape.Shape)
      (stage : ActivePrefixStageParameters.Stage sh)
      (m ell metadataP e p C axes baseline levels frames returned pref n : ℕ)
      (pcStack : Fin s) (origin : ℤ) (calls : List Call)
      (v : Tapes (nodeTapes s roles) 2)
      (h : Reached stage m ell metadataP e p C axes baseline levels frames returned pref n pcStack origin calls v)
      (j : Fin roles) (hG : 1≤sh.guard) (hGK : sh.guard+1≤sh.chunk)
      (_hr : 0<m) (hm : 0<m/roles) (_hd : roles∣m)
      (_hpay : sh.payload=1) (hslots : stage.slots=25^3) (pc : Fin count) (reverse : Bool)
      (hp : ∀ op,1<stage.f → ActivePrefixStageRuntimeData.Packed
        (ActivePrefixStagePairData.changePair (CompactComplexSourceReadyReachedBasisInvariant.input stage (m/roles) ell metadataP hG hGK hm) op) D),
      let d := CompactComplexSourceReadyReachedBasisInvariant.input stage (m/roles) ell metadataP hG hGK hm
      let f := h.data (CompactComplexScalarRolePorts.roleIndex.symm j)
      let after := basisArray stage (m/roles) ell metadataP hG hGK hm hslots pc reverse f
      let passTime := CompactNativeConjugatedSharedCaller.cost (CompactNativeRoleSourcePorts.callerTapes 44 roles) d ell
        (CompactComplexActualCallAlignment.nativeCost D d hslots pc reverse
          (ActivePrefixStageNativePolynomial.symbols (2^ell) (NativePolynomialStageShape.width sh metadataP)) hp)
      HoareTime (CompactComplexActualCallFullAlignment.roleProgram P s roles j pc reverse)
        (fun z => z=CleanSubbank.bank (Alphabet.mapTapes encoding (ready v)))
        (fun z => z=CleanSubbank.bank (Alphabet.mapTapes encoding
          (ready (canonical (replacementCaller h j after) h.aux))))
        (CompactComplexActualCallRoleAlignment.cost roles stage m ell metadataP passTime) ∧
      (CompactComplexActualCallRoleAlignment.cost roles stage m ell metadataP passTime : ℝ)≤
        K*ActivePrefixStageInverseBudget.scale d := by
  obtain ⟨q,P,C,hC,hP⟩ := CompactComplexActualCallFullAlignment.exists_role_program D roles hc
  refine ⟨q,P,C,hC,?_⟩
  intro s sh stage m ell metadataP e p C axes baseline levels frames returned pref n pcStack origin calls v h j
    hG hGK hr hm hd hpay hslots pc reverse hp
  dsimp only
  have hw := polynomial_width stage (m/roles) ell metadataP hG hGK hm
    (h.data (CompactComplexScalarRolePorts.roleIndex.symm j))
    (NativePolynomialStageShape.width sh metadataP) (h.width _)
  have hn := selected_native_word h j hG hGK hm
  have hj : (⟨j.val+1,by omega⟩ : Fin (1+roles))=Fin.natAdd 1 j :=
    Fin.ext (by simp only [Fin.val_natAdd];omega)
  obtain ⟨hb,hbound⟩ := hP s h.control h.queue h.scalar h.tail h.storage h.payload j
    (h.aux.append (SharedBank.empty 7 2))
    (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2)
    (SharedBank.empty 10 2) (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)
    sh stage m ell metadataP hG hGK hr hm hd hpay hslots pc reverse hp
    (polynomial stage (m/roles) ell metadataP hG hGK hm
      (h.data (CompactComplexScalarRolePorts.roleIndex.symm j))) hw
      (by simpa only [hj] using hn.2) (by simpa only [hj] using hn.1)
  rw [canonical_full] at hb
  rw [←basisArray_word stage (m/roles) ell metadataP hG hGK hm hslots pc reverse
    (h.data (CompactComplexScalarRolePorts.roleIndex.symm j))
    (NativePolynomialStageShape.width sh metadataP) (h.width _),canonical_setTape] at hb
  change HoareTime _
    (fun z => z=CleanSubbank.bank (Alphabet.mapTapes encoding (ready (canonical
      (CompactComplexNativeCodecFrame.bank h.control h.queue h.scalar
        (CompactComplexNativeCodec.raw stage m ell metadataP) h.tail h.storage h.payload) h.aux))))
    (fun z => z=CleanSubbank.bank (Alphabet.mapTapes encoding (ready (canonical
      (SharedPlacementAlphabet.setTape
        (CompactComplexNativeCodecFrame.bank h.control h.queue h.scalar
          (CompactComplexNativeCodec.raw stage m ell metadataP) h.tail h.storage h.payload)
        (CompactComplexNativeRoleBridge.roleSlot j)
        (CompactSpectatorLeafAxis.word (basisArray stage (m/roles) ell metadataP hG hGK hm hslots pc reverse
          (h.data (CompactComplexScalarRolePorts.roleIndex.symm j)))) 0) h.aux)))) _ at hb
  rw [←replacementCaller_eq_setTape h j] at hb
  rw [←h.canonical_bank] at hb
  exact ⟨hb,hbound⟩

/-- The exact path relation of the original PC table with actual aligned
prime blocks and the original saved-PC port, extended by fixed basis work. -/
def path (P : Program ActivePrefixStageNative.tapes q prime)
    (headerStack pcStack liveStack : Fin s) :=
  CompactComplexFixedNodePaths.nodePath
    (Nat.zero_lt_of_lt (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack).isLt)
    (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack)
    (CompactComplexActualCallFullAlignment.childReturn P headerStack liveStack)
    (CompactComplexSourceReadyAlignedActualTable.controls pcStack)
    (CompactComplexSourceReadyAlignedActualTable.event P headerStack pcStack liveStack)
    (CompactComplexSourceReadyAlignedActualTable.classify pcStack)

private theorem child_path (P : Program ActivePrefixStageNative.tapes q prime)
    (headerStack pcStack liveStack : Fin s) (call : Call) (i : Fin schedule.length)
    (hi : schedule.get i=Event.child call) (before after : Tapes (tapes s roles) prime) (B : ℕ)
    (h : HoareTime (CompactComplexActualCallFullAlignment.child P headerStack pcStack liveStack call).2
      (fun z => z=before) (fun z => z=after) B) :
    ∃ time≤B+1,path P headerStack pcStack liveStack
      (CompactComplexScheduledPCLayout.eventPC i) before time
      (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount schedule.length 0) after := by
  apply CompactComplexFixedNodePaths.child_prefix_path
    (Nat.zero_lt_of_lt (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack).isLt)
    (CompactComplexSourceReadyAlignedActualTable.savedStackSlot pcStack)
    (CompactComplexActualCallFullAlignment.childReturn P headerStack liveStack)
    (CompactComplexSourceReadyAlignedActualTable.controls pcStack)
    (CompactComplexSourceReadyAlignedActualTable.event P headerStack pcStack liveStack)
    (CompactComplexSourceReadyAlignedActualTable.classify pcStack) i call hi before after B
  exact h

/-- A single genuine native witness gives the actual original-table child
prefix. The intermediate basis bank and all child readiness are derived
from the reached invariant; both sequence and table transitions are paid. -/
theorem exists_child_paths (D : ℕ) (hc : 0<roles) :
    ∃ q, ∃ P : Program ActivePrefixStageNative.tapes q prime,
    ∃ K : ℝ,0<K ∧
    ∀ (s : ℕ) (sh : CompactGadgetReservationShape.Shape)
      (left k levels frames returned m ell metadataP p C baseline pref n : ℕ)
      (rho : Fin sh.chunk)
      (visit : CompactRecursiveDependencyBudget.Path sh.active left (k+2) levels frames returned)
      (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin CompactComplexRecursiveGeometry.arity))
      (headerStack pcStack liveStack : Fin s) (origin : ℤ) (calls : List Call)
      (v : Tapes (nodeTapes s roles) 2)
      (h : Reached (CompactComplexChildHeadersData.parent rho visit.visit hactive pair)
        m ell metadataP (k+2) p C 0 baseline levels frames returned pref n pcStack origin calls v)
      (call : Call) (i : Fin schedule.length) (_hi : schedule.get i=Event.child call)
      (hG : 1≤sh.guard) (hGK : sh.guard+1≤sh.chunk) (_hr : 0<m) (hm : 0<m/roles) (_hd : roles∣m)
      (_hpay : sh.payload=1)
      (hslots : (CompactComplexChildHeadersData.parent rho visit.visit hactive pair).slots=25^3)
      (hpack : ∀ op,1<(CompactComplexChildHeadersData.parent rho visit.visit hactive pair).f →
        ActivePrefixStageRuntimeData.Packed (ActivePrefixStagePairData.changePair
          (CompactComplexSourceReadyReachedBasisInvariant.input
            (CompactComplexChildHeadersData.parent rho visit.visit hactive pair) (m/roles) ell metadataP hG hGK hm) op) D)
      (_hmeta : p+2*sh.bits≤metadataP) (_hbase : baseline≤p)
      (_hroom : CompactComplexDenominatorCapacity.room CompactComplexDenominatorCapacity.scalarRows≤sh.chunk)
      (_hA : 0<sh.axes) (_hK : 0<sh.chunk),
      let stage := CompactComplexChildHeadersData.parent rho visit.visit hactive pair
      let j := CompactComplexRolePhaseSite.role call.site
      let pc := CompactComplexRolePhaseSite.pc call.site
      let d := CompactComplexSourceReadyReachedBasisInvariant.input stage (m/roles) ell metadataP hG hGK hm
      let after := basisArray stage (m/roles) ell metadataP hG hGK hm hslots pc false
        (h.data (CompactComplexScalarRolePorts.roleIndex.symm j))
      let passTime := CompactNativeConjugatedSharedCaller.cost (CompactNativeRoleSourcePorts.callerTapes 44 roles) d ell
        (CompactComplexActualCallAlignment.nativeCost D d hslots pc false
          (ActivePrefixStageNativePolynomial.symbols (2^ell) (NativePolynomialStageShape.width sh metadataP)) hpack)
      ∃ hn : Reached stage m ell metadataP (k+2) p C 0 baseline levels frames returned pref n pcStack origin calls
        (canonical (replacementCaller h j after) h.aux),
        hn.data=replacementData h j after ∧
        (CompactComplexActualCallRoleAlignment.cost roles stage m ell metadataP passTime : ℝ)≤
          K*ActivePrefixStageInverseBudget.scale d ∧
        ∃ time≤CompactComplexActualCallRoleAlignment.cost roles stage m ell metadataP passTime+
          1+CompactComplexSourceReadyChildEntryPath.bound (sh:=sh) m ell metadataP+1,
          path P headerStack pcStack liveStack (CompactComplexScheduledPCLayout.eventPC i)
            (CleanSubbank.bank (Alphabet.mapTapes encoding (ready v))) time
            (CompactComplexFixedNodeTable.controlPCFor CompactComplexScheduledPCLayout.originalCount schedule.length 0)
            (CleanSubbank.bank (Alphabet.mapTapes encoding
              (ready (CompactComplexSourceReadyWorkspace.ready
                (CompactComplexSourceReadyReachedChildInvariant.childPublic rho visit hactive pair hn call headerStack liveStack))))) := by
  obtain ⟨q,P,K,hKpos,hP⟩ := exists_basis_runs D hc
  refine ⟨q,P,K,hKpos,?_⟩
  intro s sh left k levels frames returned m ell metadataP p C baseline pref n rho visit hactive pair
    headerStack pcStack liveStack origin calls v h call i hi hG hGK hr hm hd hpay hslots hpack hmeta hbase hroom hA hK
  dsimp only
  obtain ⟨hn,hdata⟩ := basis_reached h (CompactComplexRolePhaseSite.role call.site) hG hGK hm hslots
    (CompactComplexRolePhaseSite.pc call.site) false
  obtain ⟨hb,hbound⟩ := hP s sh _ m ell metadataP (k+2) p C 0 baseline levels frames returned pref n pcStack origin calls v h
    (CompactComplexRolePhaseSite.role call.site) hG hGK hr hm hd hpay hslots
    (CompactComplexRolePhaseSite.pc call.site) false hpack
  refine ⟨hn,hdata,hbound,?_⟩
  have he := CompactComplexSourceReadyReachedChildInvariant.child_entry_runs rho visit hactive pair hn call
    headerStack liveStack hmeta hbase hroom hm hG hA hK
  have hex := hoare_extend_eq he (SharedBank.empty CompactComplexSourceReadyScalarWorkspace.scratch 2)
  have hl := CompactComplexSourceReadyAlignedActualTable.lift_runs
    (CompactComplexSourceReadyActualTable.child headerStack pcStack liveStack call).2
    _ _ (SharedBank.empty (localTapes roles) prime) hex
  have hj := hb.seq hl
  exact child_path P headerStack pcStack liveStack call i hi _ _ _ hj

end
end IntegerMultBounds.Machine.CompactComplexAlignedChildEntryPath
