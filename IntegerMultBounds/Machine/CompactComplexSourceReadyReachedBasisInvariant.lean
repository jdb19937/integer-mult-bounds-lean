import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedChildInvariant

/-! The real chronological basis word permutes original selected polynomial
coefficients without changing widths, denominator or any prefix grid. The
expanded codec shape is private; retained parent raw rows stay unchanged. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedBasisInvariant
noncomputable section
open ActivePrefixStageParameters (Stage)
open ActivePrefixStageNativePolynomial (flattenArray rows)
open CompactComplexActualCallAlignment (coefficients coefficients_width)
open CompactComplexScalarNativeEndpoint (unflatten)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Grid Width decoded)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes permanent ready output)
open CompactComplexSourceReadyReachedEventInvariant (Reached canonical)
open CompactAllAxisPhaseDispatch (count)
open ButterflyStreamData (Coefficient)
variable {s : ℕ} {sh : CompactGadgetReservationShape.Shape}
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount Networks.ComplexRank25.program
  Networks.ComplexFramedExecution.rows CompactComplexCompletedLiveLower.schedule

section Arrays
variable (stage : Stage sh) (m ell metadataP : ℕ)
    (hG : 1≤sh.guard) (hGK : sh.guard+1≤sh.chunk) (hm : 0<m)

abbrev input := NativePolynomialStageShape.inputs stage m ell metadataP hG hGK hm

theorem cardinality : ActivePrefixStageTripleWords.count (input stage m ell metadataP hG hGK hm)*2^ell=
    ButterflySpectatorGeometry.Size m sh.bits (2^ell) := by
  rw [NativePolynomialStageShape.count]
  unfold ButterflySpectatorGeometry.Size
  exact Nat.mul_assoc _ _ _

/-- The original coefficient array reinterpreted as the real native row and
immutable polynomial coordinate, without changing its word order. -/
def polynomial (f : Array sh m ell) :
    Fin (ActivePrefixStageTripleWords.count (input stage m ell metadataP hG hGK hm)) → Fin (2^ell) → Coefficient :=
  unflatten (fun i => f (Fin.cast (cardinality stage m ell metadataP hG hGK hm) i))

/-- Actual original basis output, pulled back through the reversed native
chronological row word. This is a computed array, not a supplied endpoint. -/
def basisArray (hslots : stage.slots=25^3) (pc : Fin count) (reverse : Bool) (f : Array sh m ell) : Array sh m ell :=
  fun i => flattenArray (coefficients (input stage m ell metadataP hG hGK hm) hslots pc reverse
    (polynomial stage m ell metadataP hG hGK hm f))
    (Fin.cast (cardinality stage m ell metadataP hG hGK hm).symm i)

theorem polynomial_width (f : Array sh m ell) (w : ℕ)
    (hw : ∀ i,(f i).1.length=w ∧ (f i).2.length=w) :
    ∀ i j,(polynomial stage m ell metadataP hG hGK hm f i j).1.length=w ∧
      (polynomial stage m ell metadataP hG hGK hm f i j).2.length=w := fun _ _ => hw _

theorem basisArray_width (hslots : stage.slots=25^3) (pc : Fin count) (reverse : Bool)
    (f : Array sh m ell) (w : ℕ) (hw : ∀ i,(f i).1.length=w ∧ (f i).2.length=w) :
    ∀ i,(basisArray stage m ell metadataP hG hGK hm hslots pc reverse f i).1.length=w ∧
      (basisArray stage m ell metadataP hG hGK hm hslots pc reverse f i).2.length=w := by
  intro i
  exact coefficients_width _ hslots pc reverse _
    (polynomial_width stage m ell metadataP hG hGK hm f w hw) _ _

/-- Genuine basis execution only reindexes coefficients. Every true
numerator/denominator grid is therefore retained with the identical budget. -/
theorem basisArray_grid (hslots : stage.slots=25^3) (pc : Fin count) (reverse : Bool)
    (f : Array sh m ell) (q n M : ℕ) (hg : Grid sh m ell q n M f) :
    Grid sh m ell q n M (basisArray stage m ell metadataP hG hGK hm hslots pc reverse f) := by
  intro i
  exact hg _

private theorem coefficient_word_cast {N M : ℕ} (he : N=M) (f : Fin M → Coefficient) :
    ButterflyStreamData.full (fun _ => blank) 0 (fun i => f (Fin.cast he i))=
      ButterflyStreamData.full (fun _ => blank) 0 f := by
  subst M
  rfl

/-- Exact original role word consumed by the physical native converter. -/
theorem polynomial_word (f : Array sh m ell) (w : ℕ)
    (hw : ∀ i,(f i).1.length=w ∧ (f i).2.length=w) :
    CompactSpectatorLeafAxis.word f=SymbolTripleClean.word
      (List.ofFn (ActivePrefixStageNativeRows.flat
        (rows (input stage m ell metadataP hG hGK hm)
          (polynomial stage m ell metadataP hG hGK hm f)
          (polynomial_width stage m ell metadataP hG hGK hm f w hw)))) := by
  rw [ActivePrefixStageNativePolynomial.serialized_rows]
  have he := CompactComplexScalarNativeEndpoint.flatten_unflatten
    (fun i => f (Fin.cast (cardinality stage m ell metadataP hG hGK hm) i))
  change CompactSpectatorLeafAxis.word f=SymbolTripleClean.word
    (UnitPhaseFullStreamNormalized.serialized (flattenArray (polynomial stage m ell metadataP hG hGK hm f)))
  unfold polynomial
  rw [he]
  exact (coefficient_word_cast (cardinality stage m ell metadataP hG hGK hm) f).symm

/-- Exact returned serialized role word, on the original array cardinality. -/
theorem basisArray_word (hslots : stage.slots=25^3) (pc : Fin count) (reverse : Bool)
    (f : Array sh m ell) (w : ℕ) (hw : ∀ i,(f i).1.length=w ∧ (f i).2.length=w) :
    CompactSpectatorLeafAxis.word (basisArray stage m ell metadataP hG hGK hm hslots pc reverse f)=
      SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
        (rows (input stage m ell metadataP hG hGK hm)
          (coefficients (input stage m ell metadataP hG hGK hm) hslots pc reverse
            (polynomial stage m ell metadataP hG hGK hm f))
          (coefficients_width _ hslots pc reverse _
            (polynomial_width stage m ell metadataP hG hGK hm f w hw))))) := by
  rw [ActivePrefixStageNativePolynomial.serialized_rows]
  exact coefficient_word_cast (cardinality stage m ell metadataP hG hGK hm).symm _

end Arrays
private theorem single_role_replace {c : ℕ} (payload : Tapes (1+c) 2) (j : Fin c)
    (word : ℤ → Fin 6) (head : ℤ) :
    CompactComplexNativeRoleBridge.single (SharedPlacementAlphabet.setTape payload (Fin.natAdd 1 j) word head)=
      CompactComplexNativeRoleBridge.single payload := by
  have hn : (0 : Fin (1+c))≠Fin.natAdd 1 j := by
    intro he; have hv := congrArg Fin.val he; simp only [Fin.val_zero,Fin.val_natAdd] at hv; omega
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [SharedPlacementAlphabet.setTape,Function.update_of_ne hn]

private theorem role_function_update {c : ℕ} {X : Type*} (f : Fin (1+c) → X) (j : Fin c) (value : X) :
    (fun i : Fin c => Function.update f (Fin.natAdd 1 j) value ⟨i.val+1,by have := i.isLt;omega⟩)=
      Function.update (fun i : Fin c => f ⟨i.val+1,by have := i.isLt;omega⟩) j value := by
  funext i
  by_cases hi : i=j
  · subst i
    have he : (⟨j.val+1,by have := j.isLt;omega⟩ : Fin (1+c))=Fin.natAdd 1 j :=
      Fin.ext (by simp only [Fin.val_natAdd];omega)
    simp only [he,Function.update_self]
  · have hn : (⟨i.val+1,by have := i.isLt;omega⟩ : Fin (1+c))≠Fin.natAdd 1 j := by
      intro he
      exact hi (Fin.ext (by have hv := congrArg Fin.val he; simp only [Fin.val_natAdd] at hv;omega))
    simp only [Function.update_of_ne hn,Function.update_of_ne hi]

private theorem roles_role_replace {c : ℕ} (payload : Tapes (1+c) 2) (j : Fin c)
    (word : ℤ → Fin 6) (head : ℤ) :
    CompactNativeRoleSourcePorts.roles (SharedPlacementAlphabet.setTape payload (Fin.natAdd 1 j) word head)=
      SharedPlacementAlphabet.setTape (CompactNativeRoleSourcePorts.roles payload) j word head :=
  congrArg₂ Tapes.mk (role_function_update payload.head j head) (role_function_update payload.tape j word)

/-- The selected payload update is literally the real permanent role port
update used by the full physical basis pass. -/
theorem bank_role_replace {a c : ℕ}
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar rawStage : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes a 2) (payload : Tapes (1+c) 2)
    (j : Fin c) (word : ℤ → Fin 6) (head : ℤ) :
    CompactComplexNativeCodecFrame.bank control queue scalar rawStage tail storage
      (SharedPlacementAlphabet.setTape payload (Fin.natAdd 1 j) word head)=
    SharedPlacementAlphabet.setTape
      (CompactComplexNativeCodecFrame.bank control queue scalar rawStage tail storage payload)
      (CompactComplexNativeRoleBridge.roleSlot (s:=a+43) j) word head := by
  simp only [CompactComplexNativeCodecFrame.bank,CompactComplexNativeRoleBridge.bank,
    CompactComplexNativeRoleBridge.native,single_role_replace,roles_role_replace,
    CompactComplexNativeRoleBridge.roleSlot,SharedPlacementAlphabet.setTape_append_right]

section Replacement
variable {stage : Stage sh} {m ell metadataP e p C axes baseline levels frames returned pref n : ℕ}
    {pcStack : Fin s} {origin : ℤ} {calls : List Networks.ComplexRecursiveCallSchema.Call}
    {v : Tapes (nodeTapes s roles) 2}
    (h : Reached stage m ell metadataP e p C axes baseline levels frames returned pref n pcStack origin calls v)
    (j : Fin roles) (f : Array sh (m/roles) ell)

/-- Only the genuine selected payload tape is replaced. -/
def replacementPayload := SharedPlacementAlphabet.setTape h.payload (Fin.natAdd 1 j)
  (CompactSpectatorLeafAxis.word f) 0

def replacementCaller := CompactComplexNativeCodecFrame.bank h.control h.queue h.scalar
  (CompactComplexNativeCodec.raw stage m ell metadataP) h.tail h.storage (replacementPayload h j f)

def replacementData := Function.update h.data (CompactComplexScalarRolePorts.roleIndex.symm j) f

theorem replacementCaller_eq_setTape : replacementCaller h j f=
    SharedPlacementAlphabet.setTape
      (CompactComplexNativeCodecFrame.bank h.control h.queue h.scalar
        (CompactComplexNativeCodec.raw stage m ell metadataP) h.tail h.storage h.payload)
      (CompactComplexNativeRoleBridge.roleSlot (s:=10+s+43) j) (CompactSpectatorLeafAxis.word f) 0 :=
  bank_role_replace _ _ _ _ _ _ _ _ _ _

/-- Local numerical preservation packages an actual single-role replacement
as another canonical reached bank; no execution or codec equality is supplied. -/
theorem replacement_reached
    (hw : ∀ i,(f i).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (f i).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1)
    (hg : ∀ i,Networks.GaussianPrecision.BoundedGrid n
      (CompactFramedScalarGrid.bound pref
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)))
      (ButterflyStreamSemantics.decode (ButterflyGuard.halfWidth metadataP sh.bits) n (f i))) :
    ∃ hn : Reached stage m ell metadataP e p C axes baseline levels frames returned pref n pcStack origin calls
      (canonical (replacementCaller h j f) h.aux),
      hn.data=replacementData h j f := by
  have hv := (congrArg permanent h.canonical_bank).trans
    (CompactComplexSourceReadyReachedEventInvariant.canonical_permanent _ _)
  have hs0 := CompactComplexSourceReadyScalarSavedCallHistory.saved_permanent pcStack v
  rw [hv] at hs0
  have hb0 := CompactComplexSpectatorTargetBank.old_bank h.control h.queue h.scalar
    (CompactComplexNativeCodec.raw stage m ell metadataP) h.tail h.storage h.payload (Fin.natAdd 10 pcStack)
  change (CompactComplexNativeCodecFrame.bank h.control h.queue h.scalar
      (CompactComplexNativeCodec.raw stage m ell metadataP) h.tail h.storage h.payload).head
      (CompactComplexScalarCountRootBank.countSlot (Fin.natAdd 10 pcStack))=h.storage.head _ ∧
    (CompactComplexNativeCodecFrame.bank h.control h.queue h.scalar
      (CompactComplexNativeCodec.raw stage m ell metadataP) h.tail h.storage h.payload).tape
      (CompactComplexScalarCountRootBank.countSlot (Fin.natAdd 10 pcStack))=h.storage.tape _ at hb0
  rw [hb0.1,hb0.2] at hs0
  have hs1 := CompactComplexSourceReadyScalarSavedCallHistory.saved_permanent pcStack
    (canonical (replacementCaller h j f) h.aux)
  rw [CompactComplexSourceReadyReachedEventInvariant.canonical_permanent] at hs1
  have hb1 := CompactComplexSpectatorTargetBank.old_bank h.control h.queue h.scalar
    (CompactComplexNativeCodec.raw stage m ell metadataP) h.tail h.storage (replacementPayload h j f) (Fin.natAdd 10 pcStack)
  change (replacementCaller h j f).head (CompactComplexScalarCountRootBank.countSlot (Fin.natAdd 10 pcStack))=h.storage.head _ ∧
    (replacementCaller h j f).tape (CompactComplexScalarCountRootBank.countSlot (Fin.natAdd 10 pcStack))=h.storage.tape _ at hb1
  rw [hb1.1,hb1.2] at hs1
  have hsave : CompactComplexSourceReadySavedCallHistory.Reached pcStack origin calls
      (ready (canonical (replacementCaller h j f) h.aux)) := by
    have hs := h.saved_calls
    unfold CompactComplexSourceReadySavedCallHistory.Reached at hs ⊢
    rw [hs0.1,hs0.2] at hs
    rw [hs1.1,hs1.2]
    exact hs
  refine ⟨{
    control := h.control, queue := h.queue, scalar := h.scalar, tail := h.tail,
    storage := h.storage, payload := replacementPayload h j f, aux := h.aux,
    data := replacementData h j f, canonical_bank := rfl,
    width := ?_, count_blank := h.count_blank, role_words := ?_, source_blank := ?_,
    clock_blank := h.clock_blank, aux_free := h.aux_free,
    exponentValue := h.exponentValue, exponentValue_eq := h.exponentValue_eq, exponent := h.exponent,
    control28_blank := h.control28_blank, control29_blank := h.control29_blank,
    live := h.live, targetValue := h.targetValue, target := h.target, target_growth := h.target_growth,
    upper_ledger := h.upper_ledger, grid := ?_, saved_calls := hsave },rfl⟩
  · intro a i
    by_cases ha : a=(CompactComplexScalarRolePorts.roleIndex.symm j)
    · subst a
      simpa only [replacementData,Function.update_self] using hw i
    · simpa only [replacementData,Function.update_of_ne ha] using h.width a i
  · intro a
    have hb := CompactComplexSpectatorTargetBank.role_bank h.control h.queue h.scalar
      (CompactComplexNativeCodec.raw stage m ell metadataP) h.tail h.storage (replacementPayload h j f)
      (CompactComplexScalarRolePorts.roleIndex a)
    have hb0 := CompactComplexSpectatorTargetBank.role_bank h.control h.queue h.scalar
      (CompactComplexNativeCodec.raw stage m ell metadataP) h.tail h.storage h.payload
      (CompactComplexScalarRolePorts.roleIndex a)
    have h0 := h.role_words a
    refine ⟨hb.1.trans ?_,hb.2.trans ?_⟩
    all_goals by_cases ha : a=(CompactComplexScalarRolePorts.roleIndex.symm j)
    all_goals
      first
      | subst a
        simp only [Equiv.apply_symm_apply,replacementPayload,SharedPlacementAlphabet.setTape,
          Function.update_self,replacementData]
      | skip
    all_goals
      have hne : Fin.natAdd 1 (CompactComplexScalarRolePorts.roleIndex a)≠(Fin.natAdd 1 j : Fin (1+roles)) := by
        intro he
        have he' : CompactComplexScalarRolePorts.roleIndex a=j := Fin.ext (by
          have hv := congrArg Fin.val he
          simp only [Fin.val_natAdd] at hv
          omega)
        exact ha (by simpa only [Equiv.symm_apply_apply] using congrArg CompactComplexScalarRolePorts.roleIndex.symm he')
      first
      | simpa only [replacementPayload,SharedPlacementAlphabet.setTape,Function.update_of_ne hne]
          using hb0.1.symm.trans h0.1
      | simpa only [replacementPayload,SharedPlacementAlphabet.setTape,Function.update_of_ne hne,
          replacementData,Function.update_of_ne ha] using hb0.2.symm.trans h0.2
  · have hne : Fin.castAdd roles (0 : Fin 1)≠(Fin.natAdd 1 j : Fin (1+roles)) := by
      intro he; have hv := congrArg Fin.val he; simp only [Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero] at hv; omega
    simpa only [replacementPayload,SharedPlacementAlphabet.setTape,Function.update_of_ne hne] using h.source_blank
  · intro wire i
    by_cases hi : CompactComplexScalarIntegerRows.wireIndex wire=(CompactComplexScalarRolePorts.roleIndex.symm j)
    · simpa only [CompactComplexScalarSequenceSemantics.values,replacementData,hi,Function.update_self,
        ButterflyStreamSemantics.decode] using hg i
    · simpa only [CompactComplexScalarSequenceSemantics.values,replacementData,Function.update_of_ne hi]
        using h.grid wire i

/-- Physical payload input is exactly the native polynomial codec expected
by the real quotient-count basis wrapper, including its original head. -/
theorem selected_native_word (hG : 1≤sh.guard) (hGK : sh.guard+1≤sh.chunk) (hm : 0<m/roles) :
    h.payload.head (Fin.natAdd 1 j)=0 ∧
    h.payload.tape (Fin.natAdd 1 j)=SymbolTripleClean.word
      (List.ofFn (ActivePrefixStageNativeRows.flat
        (rows (input stage (m/roles) ell metadataP hG hGK hm)
          (polynomial stage (m/roles) ell metadataP hG hGK hm
            (h.data (CompactComplexScalarRolePorts.roleIndex.symm j)))
          (polynomial_width stage (m/roles) ell metadataP hG hGK hm _
            (NativePolynomialStageShape.width sh metadataP) (h.width _))))) := by
  have hb := CompactComplexSpectatorTargetBank.role_bank h.control h.queue h.scalar
    (CompactComplexNativeCodec.raw stage m ell metadataP) h.tail h.storage h.payload j
  have hw := h.role_words (CompactComplexScalarRolePorts.roleIndex.symm j)
  simp only [Equiv.apply_symm_apply] at hw
  exact ⟨hb.1.symm.trans hw.1,(hb.2.symm.trans hw.2).trans
    (polynomial_word stage (m/roles) ell metadataP hG hGK hm _
      (NativePolynomialStageShape.width sh metadataP) (h.width _))⟩

/-- Forward or reverse actual basis permutation gives a central reached
bank with the same retained raw rows, headers, grid, live and saved calls. -/
theorem basis_reached (hG : 1≤sh.guard) (hGK : sh.guard+1≤sh.chunk) (hm : 0<m/roles)
    (hslots : stage.slots=25^3) (pc : Fin count) (reverse : Bool) :
    let after := basisArray stage (m/roles) ell metadataP hG hGK hm hslots pc reverse
      (h.data (CompactComplexScalarRolePorts.roleIndex.symm j))
    ∃ hn : Reached stage m ell metadataP e p C axes baseline levels frames returned pref n pcStack origin calls
      (canonical (replacementCaller h j after) h.aux),
      hn.data=replacementData h j after := by
  dsimp only
  let before := h.data (CompactComplexScalarRolePorts.roleIndex.symm j)
  let after := basisArray stage (m/roles) ell metadataP hG hGK hm hslots pc reverse before
  have hw := basisArray_width stage (m/roles) ell metadataP hG hGK hm hslots pc reverse before
    (ButterflyGuard.halfWidth metadataP sh.bits+1) (h.width _)
  have hg0 : ∀ i,Networks.GaussianPrecision.BoundedGrid n
      (CompactFramedScalarGrid.bound pref
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)))
      (ButterflyStreamSemantics.decode (ButterflyGuard.halfWidth metadataP sh.bits) n (before i)) := by
    intro i
    simpa only [before,CompactComplexScalarSequenceSemantics.values,Equiv.apply_symm_apply,
      ButterflyStreamSemantics.decode] using
      h.grid (CompactComplexScalarIntegerRows.wireIndex.symm (CompactComplexScalarRolePorts.roleIndex.symm j)) i
  have hg : ∀ i,Networks.GaussianPrecision.BoundedGrid n
      (CompactFramedScalarGrid.bound pref
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)))
      (ButterflyStreamSemantics.decode (ButterflyGuard.halfWidth metadataP sh.bits) n (after i)) := by
    intro i
    exact hg0 _
  exact replacement_reached h j after hw hg

end Replacement

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedBasisInvariant
