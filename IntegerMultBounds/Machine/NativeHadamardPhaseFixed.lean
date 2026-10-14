module

public import IntegerMultBounds.Machine.NativeHadamardPhaseOriginal

/-! Choose the checked physical phase compiler before all geometry and data.
The run contract keeps its large finite state count abstract during placement. -/

@[expose] public section
namespace IntegerMultBounds.Machine.NativeHadamardPhaseFixed
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactComplexRecursiveGeometry (arity)
open CompactSpectatorVisitGeometry (Array)
variable {tapeCount : ℕ}
attribute [local irreducible] arity NativeHadamardPhaseOriginal.fixedWeights
  NativeHadamardPhaseOriginal.program

def Runs (focus : Fin 15 → Fin tapeCount) (source : Fin tapeCount) {stateCount : ℕ}
    (phaseProgram : Program (tapeCount+67) stateCount 2) : Prop :=
  ∀ {shape : Shape} {rows ell : ℕ} (caller : Tapes tapeCount 2) (stage : Stage shape) (metadataPrecision : ℕ),
    stage.slots=arity → 0<rows → 0<shape.guard → 0<shape.axes → shape.guard+1≤shape.chunk → shape.payload=1 →
    ∀ input : Array shape rows ell,
    (∀ index, (input index).1.length=NativePolynomialStageShape.width shape metadataPrecision ∧
      (input index).2.length=NativePolynomialStageShape.width shape metadataPrecision) →
    (∀ header, caller.tape (focus header)=RadixZeroFill.encodedBinary
      (NativeEndpointCharacterCopy.words stage rows ell metadataPrecision header)) →
    (∀ header, caller.head (focus header)=1) →
    caller.tape source=putWord (fun _ => blank) 0 (NativeZeroPaddingArray.word input) → caller.head source=0 →
    HoareTime phaseProgram (fun bank => bank=caller.append (FixedHeaderBankCopy.empty 67))
      (fun bank => bank=(NativeHadamardPhaseOriginal.resultCaller caller source stage metadataPrecision input).append
        (FixedHeaderBankCopy.empty 67))
      (NativeHadamardPhaseOriginal.constant*CompactNativeRoleTransferBudget.volume rows shape ell metadataPrecision)

theorem exists_program (focus : Fin 15 → Fin tapeCount) (source : Fin tapeCount) :
    ∃ stateCount,∃ phaseProgram : Program (tapeCount+67) stateCount 2, Runs focus source phaseProgram := by
  refine ⟨_,NativeHadamardPhaseOriginal.program focus source,?_⟩
  intro shape rows ell caller stage metadataPrecision stageSlots rowsPositive guardPositive axesPositive guardFits
    unitPayload input inputWidth headersReady headersPositioned sourceReady sourcePositioned
  exact NativeHadamardPhaseOriginal.runs focus source caller stage metadataPrecision stageSlots rowsPositive
    guardPositive axesPositive guardFits unitPayload input inputWidth headersReady headersPositioned sourceReady sourcePositioned

def stateCount (focus : Fin 15 → Fin tapeCount) (source : Fin tapeCount) :=
  Classical.choose (exists_program focus source)

def program (focus : Fin 15 → Fin tapeCount) (source : Fin tapeCount) :
    Program (tapeCount+67) (stateCount focus source) 2 :=
  Classical.choose (Classical.choose_spec (exists_program focus source))

/-- Execution derives from the checked concrete compiler, rather than a supplied
phase program, execution certificate, output equation or total-time premise. -/
theorem runs (focus : Fin 15 → Fin tapeCount) (source : Fin tapeCount) : Runs focus source (program focus source) :=
  Classical.choose_spec (Classical.choose_spec (exists_program focus source))

end
end IntegerMultBounds.Machine.NativeHadamardPhaseFixed
