module

public import IntegerMultBounds.Machine.CompactComplexSourceReadySettledEventInvariant
public import IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEventTrace

/-! The corrected-entry physical target descriptor determines the actual
Reached target value uniquely, independently of how that witness was built. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEntryTarget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexSourceReadyScalarWorkspace (roles nodeTapes)
open CompactComplexSourceReadyReachedEventInvariant (Reached canonical)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  CompactComplexRolePhaseSite.roleCount

private theorem putBits_blank_tail_injective (leftBits rightBits : List Bool)
    (base : ℤ → Fin 4) (start : ℤ)
    (blankTail : ∀ cell,start≤cell → base cell=blank)
    (sameCells : ∀ cell,start≤cell → putBits base start leftBits cell=putBits base start rightBits cell) :
    leftBits=rightBits := by
  induction leftBits generalizing rightBits start with
  | nil =>
    cases rightBits with
    | nil => rfl
    | cons rightBit rightTail =>
      have headEqual := sameCells start le_rfl
      rw [putBits_head,show putBits base start [] start=base start from rfl,blankTail start le_rfl] at headEqual
      have distinct : bitSymbol (a:=0) rightBit≠blank (a:=0) := by cases rightBit <;> decide
      exact False.elim (distinct headEqual.symm)
  | cons leftBit leftTail inductionHypothesis =>
    cases rightBits with
    | nil =>
      have headEqual := sameCells start le_rfl
      rw [putBits_head,show putBits base start [] start=base start from rfl,blankTail start le_rfl] at headEqual
      have distinct : bitSymbol (a:=0) leftBit≠blank (a:=0) := by cases leftBit <;> decide
      exact False.elim (distinct headEqual)
    | cons rightBit rightTail =>
      have headEqual := sameCells start le_rfl
      rw [putBits_head,putBits_head] at headEqual
      have bitEqual : leftBit=rightBit := by
        cases leftBit <;> cases rightBit <;> simp_all [bitSymbol]
      subst rightBit
      apply congrArg (List.cons leftBit)
      apply inductionHypothesis rightTail (start+1)
      · intro cell beyondStart
        exact blankTail cell (by omega)
      · intro cell beyondStart
        have distinct : cell≠start := by omega
        have cellEqual := sameCells cell (by omega)
        simpa only [putBits,Function.update_of_ne distinct] using cellEqual

/-- Equality of literal encoded binary natural descriptors implies equality
of the numbers, including zero and descriptors of different lengths. -/
theorem encoded_bits_injective {alphabetSize leftValue rightValue : ℕ}
    (encodedEqual : RadixZeroFill.encodedBinary (q:=alphabetSize) (RecursiveChildQuotientsConstant.bits leftValue)=
      RadixZeroFill.encodedBinary (q:=alphabetSize) (RecursiveChildQuotientsConstant.bits rightValue)) :
    leftValue=rightValue := by
  have binaryEqual : CountedCopyReuse.binary (RecursiveChildQuotientsConstant.bits leftValue)=
      CountedCopyReuse.binary (RecursiveChildQuotientsConstant.bits rightValue) := by
    funext cell
    apply (RadixToBinary.binaryEncoding (q:=alphabetSize)).injective
    exact congrFun encodedEqual cell
  have bitsEqual := putBits_blank_tail_injective
    (RecursiveChildQuotientsConstant.bits leftValue) (RecursiveChildQuotientsConstant.bits rightValue)
    CountedCopyReuse.empty 1
    (by intro cell beyondStart; simp [CountedCopyReuse.empty,show cell≠0 by omega])
    (fun cell _ => congrFun binaryEqual cell)
  have valuesEqual := congrArg Counter.value bitsEqual
  simpa only [RecursiveChildQuotientsConstant.bits_value] using valuesEqual

/-- Recover the target from the same literal original corrected-entry bank;
no abstract target assertion or choice of initial Reached witness is needed. -/
theorem target_of_corrected_entry
    {stackCount : ℕ} {shape : Shape} {stage : ActivePrefixStageParameters.Stage shape}
    {rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant completedAxes
      baselineLive dependencyLevels frameVolume returnedCount prefixCount live : ℕ}
    {pcStack : Fin stackCount} {origin : ℤ} {savedCalls : List Networks.ComplexRecursiveCallSchema.Call}
    {actualBank : Tapes (nodeTapes stackCount roles) 2}
    (reached : Reached stage rowCount polynomialExponent metadataPrecision nodeExponent baselinePrecision growthConstant
      completedAxes baselineLive dependencyLevels frameVolume returnedCount prefixCount live pcStack origin savedCalls actualBank)
    (stageSlots : stage.slots=arity) (initialLive childExponent : ℕ) (rolesDivide : roles∣rowCount)
    (original : CompactSpectatorVisitGeometry.Array shape rowCount polynomialExponent)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (oldStorage : Tapes (10+stackCount) 2) (auxiliary : Tapes 2 2)
    (entryBank : actualBank=canonical
      (CompactComplexCorrectedEntryGeometryReadiness.permanent stage stageSlots rowCount polynomialExponent
        metadataPrecision initialLive childExponent rolesDivide original control queue scalar tail oldStorage) auxiliary) :
    reached.targetValue=initialLive+2*arity^(childExponent+1) := by
  obtain ⟨storageEqual,_⟩ := CompactComplexSourceReadySettledEventInvariant.canonical_fields reached _ auxiliary entryBank
  simp only [CompactComplexCorrectedEntryGeometryReadiness.permanent,
    CompactComplexSourceReadyReachedDormantFrameInvariant.storageOf_bank] at storageEqual
  have targetStored := reached.target.2
  rw [storageEqual] at targetStored
  have literalTarget := CompactComplexCorrectedEntryGeometryReadiness.storage_target oldStorage
    (initialLive+2*arity^(childExponent+1))
  exact encoded_bits_injective (targetStored.symm.trans literalTarget.2)

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyReachedEntryTarget
