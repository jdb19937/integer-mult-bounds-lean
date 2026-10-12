module

public import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedFinal
public import IntegerMultBounds.Machine.CompactComplexCorrectedEntryGridReadiness
public import IntegerMultBounds.Machine.CompactComplexSinkCorrectionGrid

/-! The literal named sink signs, column phase, X negation and exchange are
exactly the corrected network's output map at their actual codec addresses.
Only genuine input decoding, retained widths and signed reserves are used. -/

@[expose] public section
namespace IntegerMultBounds.Machine.CompactComplexSinkCorrectOutput
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Width Grid decoded half)
open CompactComplexEndpointRoleExchange (Wire Address)
open CompactComplexSourceReadySinkCorrections (signed data)
open CompactComplexCorrectedEntryGridReadiness (coordinates)
variable {shape : Shape} {rows polynomialExponent precision : ℕ}
attribute [local irreducible] ComplexRank25.program CompactComplexRolePhaseSite.roleCount

private theorem signed_guards (live numeratorBound : ℕ) (inputArray : Array shape rows polynomialExponent)
    (inputGrid : Grid shape rows polynomialExponent precision live numeratorBound inputArray)
    (signedReserve : numeratorBound<2^(half shape precision)) :
    ∀ coefficient,|ButterflySigned.signedValue (half shape precision) (inputArray coefficient).1|<(2^(half shape precision) : ℕ) ∧
      |ButterflySigned.signedValue (half shape precision) (inputArray coefficient).2|<(2^(half shape precision) : ℕ) := by
  have integerReserve : (numeratorBound : ℤ)<(2^(half shape precision) : ℕ) := by exact_mod_cast signedReserve
  intro coefficient
  have componentBounds := ButterflyGuard.represented_bound _ _ live numeratorBound (inputGrid coefficient)
  exact ⟨componentBounds.1.trans_lt integerReserve,componentBounds.2.trans_lt integerReserve⟩

private theorem character_decoded_guarded
    (stage : Stage shape) (parentSlots : stage.slots=NativeEndpointCharacterRoles.arity) (metadataPrecision live numeratorBound : ℕ)
    (before : Wire → Array shape rows polynomialExponent) (character : Address)
    (inputWidth : Width shape rows polynomialExponent precision (before (Sum.inr (Sum.inl character))))
    (inputGrid : Grid shape rows polynomialExponent precision live numeratorBound (before (Sum.inr (Sum.inl character))))
    (signedReserve : numeratorBound<2^(half shape precision)) :
    decoded shape rows polynomialExponent precision live
      (NativeEndpointCharacterNamedBank.result true stage parentSlots polynomialExponent metadataPrecision before character)=
      fun coefficient => BinaryPhase.phase
        ((NativeEndpointCharacterPath.phase true stage parentSlots polynomialExponent metadataPrecision character coefficient.val).val : ZMod 4)*
        decoded shape rows polynomialExponent precision live (before (Sum.inr (Sum.inl character))) coefficient := by
  funext coefficient
  apply NativeEndpointCharacterPath.signed_decoded
  · intro index
    simpa only [NativeEndpointCharacterNamedRoles.role,ite_true,half,ButterflyGuard.width,
      ButterflyIndependentGuardSemantics.half_eq] using inputWidth index
  · exact signed_guards live numeratorBound _ inputGrid signedReserve

private theorem rotation_decoded_guarded (columns live numeratorBound : ℕ)
    (inputArray : Array shape rows polynomialExponent)
    (inputWidth : Width shape rows polynomialExponent precision inputArray)
    (inputGrid : Grid shape rows polynomialExponent precision live numeratorBound inputArray)
    (signedReserve : numeratorBound<2^(half shape precision)) :
    decoded shape rows polynomialExponent precision live (NativeUniformPolynomialRotationSemantics.array columns inputArray)=
      fun coefficient => Complex.I^(27*columns)*decoded shape rows polynomialExponent precision live inputArray coefficient := by
  funext coefficient
  apply NativeUniformPolynomialRotationSemantics.decoded
  · intro index
    simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using inputWidth index
  · exact signed_guards live numeratorBound _ inputGrid signedReserve

private theorem negative_decoded_guarded (live numeratorBound : ℕ)
    (inputArray : Array shape rows polynomialExponent)
    (inputWidth : Width shape rows polynomialExponent precision inputArray)
    (inputGrid : Grid shape rows polynomialExponent precision live numeratorBound inputArray)
    (signedReserve : numeratorBound<2^(half shape precision)) :
    decoded shape rows polynomialExponent precision live (UnitPhasePolynomialArray.result 2 inputArray)=
      fun coefficient => -decoded shape rows polynomialExponent precision live inputArray coefficient := by
  funext coefficient
  apply NativeUniformPolynomialRotationSemantics.negative_decoded
  · intro index
    simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using inputWidth index
  · exact signed_guards live numeratorBound _ inputGrid signedReserve

/-- The actual before-array lookup initializes the theoretical stored bank.
Every emitted role, including unchanged scratch, has the real corrected output
value at its own codec address; no output equality is supplied. -/
theorem decoded_correctOutput_at_guarded
    (stage : Stage shape) (parentSlots : stage.slots=NativeEndpointCharacterRoles.arity)
    (metadataPrecision live numeratorBound : ℕ) (before : Wire → Array shape rows polynomialExponent)
    (inputWidth : ∀ wire,Width shape rows polynomialExponent precision (before wire))
    (inputGrid : ∀ wire,Grid shape rows polynomialExponent precision live numeratorBound (before wire))
    (signedReserve : numeratorBound<2^(half shape precision))
    (coefficient : Fin (ButterflySpectatorGeometry.Size rows shape.bits (2^polynomialExponent)))
    (stored : Wire → BinaryColumns.Arrays (25^3) stage.f)
    (inputDecoded : ∀ wire,decoded shape rows polynomialExponent precision live (before wire) coefficient=
      stored wire (coordinates stage parentSlots rows polynomialExponent metadataPrecision coefficient)) :
    ∀ wire,decoded shape rows polynomialExponent precision live
      (data stage parentSlots polynomialExponent metadataPrecision before wire) coefficient=
      ComplexEndpoints.correctOutput stage.f stored wire
        (coordinates stage parentSlots rows polynomialExponent metadataPrecision coefficient) := by
  have signedWidth := CompactComplexSinkCorrectionGrid.signed_width stage parentSlots metadataPrecision before inputWidth
  have signedGrid : ∀ wire,Grid shape rows polynomialExponent precision live numeratorBound
      (signed stage parentSlots polynomialExponent metadataPrecision before wire) := by
    intro wire coefficient
    rcases wire with character|character|scratch
    · exact inputGrid _ coefficient
    · change GaussianPrecision.BoundedGrid live numeratorBound
        (decoded shape rows polynomialExponent precision live
          (NativeEndpointCharacterNamedBank.result true stage parentSlots polynomialExponent metadataPrecision before character) coefficient)
      rw [character_decoded_guarded stage parentSlots metadataPrecision live numeratorBound before character
        (inputWidth _) (inputGrid _) signedReserve]
      exact GaussianPrecision.bounded_I_pow_mul _ (inputGrid _ coefficient)
    · exact inputGrid _ coefficient
  intro wire
  rcases wire with character|character|scratch
  · change decoded shape rows polynomialExponent precision live
      (NativeUniformPolynomialRotationSemantics.array stage.f
        (NativeEndpointCharacterNamedBank.result true stage parentSlots polynomialExponent metadataPrecision before character)) coefficient=
      Complex.I^(27*stage.f)*ComplexEndpoints.signColumns stage.f (ComplexEndpoints.terminalVector character)
        (stored (Sum.inr (Sum.inl character))) (coordinates stage parentSlots rows polynomialExponent metadataPrecision coefficient)
    have characterWidth : Width shape rows polynomialExponent precision
        (NativeEndpointCharacterNamedBank.result true stage parentSlots polynomialExponent metadataPrecision before character) :=
      signedWidth (Sum.inr (Sum.inl character))
    have characterGrid : Grid shape rows polynomialExponent precision live numeratorBound
        (NativeEndpointCharacterNamedBank.result true stage parentSlots polynomialExponent metadataPrecision before character) :=
      signedGrid (Sum.inr (Sum.inl character))
    have rotated := congrFun (rotation_decoded_guarded stage.f live numeratorBound _ characterWidth characterGrid signedReserve) coefficient
    have characterized := congrFun (character_decoded_guarded stage parentSlots metadataPrecision live numeratorBound before character
      (inputWidth _) (inputGrid _) signedReserve) coefficient
    have characterPhase := CompactComplexCorrectedEntryGridReadiness.phase_character stage parentSlots rows
      polynomialExponent metadataPrecision character coefficient
    change BinaryPhase.phase
      ((NativeEndpointCharacterPath.phase true stage parentSlots polynomialExponent metadataPrecision character coefficient.val).val : ZMod 4)=_ at characterPhase
    have decodedBefore := inputDecoded (Sum.inr (Sum.inl character))
    have rawSignEquality := congrArg₂ (fun phaseValue coefficientValue : ℂ => phaseValue*coefficientValue)
      characterPhase decodedBefore
    have signAt := ComplexEndpoints.signColumns_apply stage.f (ComplexEndpoints.terminalVector character)
      (stored (Sum.inr (Sum.inl character))) (coordinates stage parentSlots rows polynomialExponent metadataPrecision coefficient)
    have correctedCharacter := characterized.trans (rawSignEquality.trans signAt.symm)
    exact rotated.trans (congrArg (fun value : ℂ => Complex.I^(27*stage.f)*value) correctedCharacter)
  · change decoded shape rows polynomialExponent precision live (UnitPhasePolynomialArray.result 2 (before (Sum.inl character))) coefficient=
      -stored (Sum.inl character) (coordinates stage parentSlots rows polynomialExponent metadataPrecision coefficient)
    have negated := congrFun (negative_decoded_guarded live numeratorBound (before (Sum.inl character))
      (inputWidth (Sum.inl character)) (inputGrid (Sum.inl character)) signedReserve) coefficient
    exact negated.trans (congrArg (fun value : ℂ => -value) (inputDecoded (Sum.inl character)))
  · exact inputDecoded _

/-! The universal decoder wrapper follows from the local coefficient theorem. -/
theorem decoded_correctOutput_guarded
    (stage : Stage shape) (parentSlots : stage.slots=NativeEndpointCharacterRoles.arity)
    (metadataPrecision live numeratorBound : ℕ) (before : Wire → Array shape rows polynomialExponent)
    (inputWidth : ∀ wire,Width shape rows polynomialExponent precision (before wire))
    (inputGrid : ∀ wire,Grid shape rows polynomialExponent precision live numeratorBound (before wire))
    (signedReserve : numeratorBound<2^(half shape precision))
    (stored : Wire → BinaryColumns.Arrays (25^3) stage.f)
    (inputDecoded : ∀ wire coefficient,decoded shape rows polynomialExponent precision live (before wire) coefficient=
      stored wire (coordinates stage parentSlots rows polynomialExponent metadataPrecision coefficient)) :
    ∀ wire coefficient,decoded shape rows polynomialExponent precision live
      (data stage parentSlots polynomialExponent metadataPrecision before wire) coefficient=
      ComplexEndpoints.correctOutput stage.f stored wire
        (coordinates stage parentSlots rows polynomialExponent metadataPrecision coefficient) := by
  intro wire coefficient
  exact decoded_correctOutput_at_guarded stage parentSlots metadataPrecision live numeratorBound before
    inputWidth inputGrid signedReserve coefficient stored (fun inputWire => inputDecoded inputWire coefficient) wire

/-- A genuine Path supplies this local signed reserve when its actual grid
matches the before arrays. The guarded core also supports advanced terminal
cursors whose reserve is derived separately from the real sibling budget. -/
theorem decoded_correctOutput_from_path
    (stage : Stage shape) (parentSlots : stage.slots=NativeEndpointCharacterRoles.arity) (metadataPrecision live : ℕ)
    {nodeLeft nodeExponent dependencyLevels frameVolume returnedVolume : ℕ}
    (path : CompactRecursiveDependencyBudget.Path shape.active nodeLeft nodeExponent dependencyLevels frameVolume returnedVolume)
    (baselinePrecision growthConstant : ℕ) (baselineFits : baselinePrecision≤precision)
    (chunkRoom : CompactSpectatorInheritedGrid.dependencyCoefficient growthConstant≤shape.chunk)
    (before : Wire → Array shape rows polynomialExponent)
    (inputWidth : ∀ wire,Width shape rows polynomialExponent precision (before wire))
    (inputGrid : ∀ wire,Grid shape rows polynomialExponent precision live
      (CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels (frameVolume+2*returnedVolume)) (before wire))
    (stored : Wire → BinaryColumns.Arrays (25^3) stage.f)
    (inputDecoded : ∀ wire coefficient,decoded shape rows polynomialExponent precision live (before wire) coefficient=
      stored wire (coordinates stage parentSlots rows polynomialExponent metadataPrecision coefficient)) :
    ∀ wire coefficient,decoded shape rows polynomialExponent precision live
      (data stage parentSlots polynomialExponent metadataPrecision before wire) coefficient=
      ComplexEndpoints.correctOutput stage.f stored wire
        (coordinates stage parentSlots rows polynomialExponent metadataPrecision coefficient) := by
  have guard := CompactSpectatorInheritedGrid.guard_from_path shape precision path baselinePrecision growthConstant 0
    baselineFits chunkRoom (Nat.zero_le _)
  have signedReserve : CompactRecursiveGridBudget.bound baselinePrecision growthConstant dependencyLevels
      (frameVolume+2*returnedVolume)<2^(half shape precision) := by
    simp only [pow_zero,Nat.mul_one] at guard
    omega
  exact decoded_correctOutput_guarded stage parentSlots metadataPrecision live _ before inputWidth inputGrid signedReserve stored inputDecoded

/-- The named role-indexed family consumed by real contraction/rejoin has
those same corrected output values, without changing its emitted arrays. -/
theorem decoded_family_guarded
    (stage : Stage shape) (parentSlots : stage.slots=NativeEndpointCharacterRoles.arity)
    (metadataPrecision live numeratorBound : ℕ) (before : Wire → Array shape rows polynomialExponent)
    (inputWidth : ∀ wire,Width shape rows polynomialExponent precision (before wire))
    (inputGrid : ∀ wire,Grid shape rows polynomialExponent precision live numeratorBound (before wire))
    (signedReserve : numeratorBound<2^(half shape precision))
    (stored : Wire → BinaryColumns.Arrays (25^3) stage.f)
    (inputDecoded : ∀ wire coefficient,decoded shape rows polynomialExponent precision live (before wire) coefficient=
      stored wire (coordinates stage parentSlots rows polynomialExponent metadataPrecision coefficient)) :
    ∀ role coefficient,decoded shape rows polynomialExponent precision live
      (CompactComplexSourceReadyCorrectedFinal.family stage parentSlots polynomialExponent metadataPrecision before role) coefficient=
      ComplexEndpoints.correctOutput stage.f stored (CompactComplexRolePhaseSite.roleEncoding.symm role)
        (coordinates stage parentSlots rows polynomialExponent metadataPrecision coefficient) :=
  fun role => decoded_correctOutput_guarded stage parentSlots metadataPrecision live numeratorBound before
    inputWidth inputGrid signedReserve stored inputDecoded (CompactComplexRolePhaseSite.roleEncoding.symm role)

end
end IntegerMultBounds.Machine.CompactComplexSinkCorrectOutput
