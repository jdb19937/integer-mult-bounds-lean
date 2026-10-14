module

public import IntegerMultBounds.Machine.LayerNativeWidening
public import IntegerMultBounds.Machine.NativeSignExtendSetup

@[expose] public section
namespace IntegerMultBounds.Machine.LayerGuardedInput
noncomputable section
open Spec.SignedRingProduct (Rec array layerHeader)
open SharedPlacementAlphabet (setTape)
variable {coefficientCount : ℕ}

def fields (width : ℕ) (polynomials : List (Rec coefficientCount)) :=
  (LayerNativeInput.publicPairs width polynomials).flatMap fun pair =>
    [ChirpPublicCodec.nativeWord pair.1, ChirpPublicCodec.nativeWord pair.2]

theorem native_fields (width : ℕ) (polynomials : List (Rec coefficientCount)) :
    NativeSignExtendArray.native (fields width polynomials) =
      ChirpPublicArray.native (LayerNativeInput.publicPairs width polynomials) := by
  unfold NativeSignExtendArray.native fields ChirpPublicArray.native
  generalize LayerNativeInput.publicPairs width polynomials = pairs
  induction pairs with
  | nil => rfl
  | cons pair rest inductionHypothesis =>
    simp only [List.flatMap_cons, List.flatMap_append, List.flatMap_nil, List.append_nil, inductionHypothesis,
      DelimitedRadixRecord.complex]

theorem field_widths (width : ℕ) (polynomials : List (Rec coefficientCount)) :
    ∀ field ∈ fields width polynomials, field.length = width := by
  intro field member
  obtain ⟨pair, pairMember, fieldMember⟩ := List.mem_flatMap.mp member
  have widths := LayerNativeInput.pair_widths width polynomials pair pairMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at fieldMember
  rcases fieldMember with rfl | rfl <;> rw [ChirpPublicCodec.native_length]
  · exact widths.1
  · exact widths.2

def program (roleCount arity : ℕ) := seq (extend (LayerPreparedInput.program roleCount arity) 6) LayerNativeWidening.program

def prepared (roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (polynomials : List (Rec coefficientCount)) (secondArray thirdArray : List Bool) :=
  (LayerPreparedInput.output roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
    polynomials secondArray thirdArray).append (SharedBank.empty 6 2)

def output (roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (polynomials : List (Rec coefficientCount)) (secondArray thirdArray : List Bool) : Tapes 70 2 :=
  setTape (prepared roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
    polynomials secondArray thirdArray) (69 : Fin 70)
    (NativeSignExtendArray.word (NativeSignExtendArray.widened (fields wordWidth polynomials)
      (LayerReservationHeaders.nativeWidth activeCount chunkWidth wordWidth))) 0

def cost (roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (polynomials : List (Rec coefficientCount)) :=
  LayerPreparedInput.cost roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth polynomials+1+
    LayerNativeWidening.cost (fields wordWidth polynomials) (LayerReservationHeaders.nativeWidth activeCount chunkWidth wordWidth)

theorem runs_public (parameters : Spec.SignedRingProduct.LayerParams) (parametersValid : parameters.Valid)
    (roleCount arity : ℕ) (rolesPositive : 2 ≤ roleCount) (arityPositive : 2 ≤ arity)
    (precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (precisionPositive : 1 ≤ precision)
    (admissible : Spec.SignedRingProduct.LayerAdmissible parameters precision axes coefficientCount activeCount
      outerCount suffixCount chunkWidth selectedBit wordWidth)
    (polynomials : List (Rec coefficientCount)) (secondArray thirdArray : List Bool) :
    HoareTime (program roleCount arity)
      (· = Spec.SignedRingProduct.bank
        (layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
        (array wordWidth polynomials) secondArray thirdArray)
      (· = output roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
        polynomials secondArray thirdArray)
      (cost roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth polynomials) := by
  have preparedRun := hoare_extend_eq
    (LayerPreparedInput.runs_public parameters parametersValid roleCount arity rolesPositive arityPositive precision axes activeCount
      outerCount suffixCount chunkWidth selectedBit wordWidth precisionPositive admissible polynomials secondArray thirdArray)
    (SharedBank.empty 6 2)
  have publicInput : (Spec.SignedRingProduct.bank (t := 64) (a := 2)
      (layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
      (array wordWidth polynomials) secondArray thirdArray).append (SharedBank.empty 6 2) =
      Spec.SignedRingProduct.bank (t := 70)
        (layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
        (array wordWidth polynomials) secondArray thirdArray := by
    apply Placement.Tapes.ext'
    all_goals intro slot; fin_cases slot <;> rfl
  rw [publicInput] at preparedRun
  let caller := prepared roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
    polynomials secondArray thirdArray
  let targetWidth := LayerReservationHeaders.nativeWidth activeCount chunkWidth wordWidth
  have widthReady : caller.tape 30 = RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits targetWidth) := rfl
  have widthHead : caller.head 30 = 1 := rfl
  have sourceReady : caller.tape 63 = NativeSignExtendArray.word (NativeSignExtendArray.native (fields wordWidth polynomials)) := by
    rw [native_fields]
    exact (LayerPreparedInput.native_source roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit
      wordWidth polynomials secondArray thirdArray).2
  have sourceHead : caller.head 63 = 0 := rfl
  have workBlank : ∀ slot : Fin 70, 64 ≤ slot.val → caller.head slot = 0 ∧ caller.tape slot = (fun _ => blank) := by
    intro slot outside
    let privateSlot : Fin 6 := ⟨slot.val-64, by omega⟩
    have slotEqual : slot = Fin.natAdd 64 privateSlot := by apply Fin.ext; dsimp [privateSlot]; omega
    rw [slotEqual]
    simp only [caller, prepared, Tapes.append, Fin.addCases_right, SharedBank.empty, and_self]
  have wideningRun := LayerNativeWidening.runs caller (fields wordWidth polynomials) targetWidth
    (by intro field member; rw [field_widths wordWidth polynomials field member]; unfold targetWidth LayerReservationHeaders.nativeWidth; omega)
    widthReady widthHead sourceReady sourceHead workBlank
  unfold program output cost
  exact preparedRun.seq wideningRun

theorem signed_values (wordWidth activeCount chunkWidth : ℕ) (polynomials : List (Rec coefficientCount))
    (widthPositive : 0 < wordWidth) :
    ((fields wordWidth polynomials).map (fun field => NativeSignExtend.extended field
      (LayerReservationHeaders.nativeWidth activeCount chunkWidth wordWidth))).map
        (ButterflySigned.signedValue (LayerReservationHeaders.nativeWidth activeCount chunkWidth wordWidth-1)) =
      (fields wordWidth polynomials).map (ButterflySigned.signedValue (wordWidth-1)) := by
  have targetPositive : 0 < LayerReservationHeaders.nativeWidth activeCount chunkWidth wordWidth := by
    unfold LayerReservationHeaders.nativeWidth
    omega
  have values := NativeSignExtendArray.widened_values (fields wordWidth polynomials) (wordWidth-1)
    (LayerReservationHeaders.nativeWidth activeCount chunkWidth wordWidth-1)
    (by intro field member; rw [field_widths wordWidth polynomials field member]; omega)
    (by unfold LayerReservationHeaders.nativeWidth; omega)
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ LayerReservationHeaders.nativeWidth activeCount chunkWidth wordWidth)] using values

theorem workspace_blank (roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (polynomials : List (Rec coefficientCount)) (secondArray thirdArray : List Bool) (slot : Fin 6)
    (notDestination : slot ≠ 5) :
    (output roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
      polynomials secondArray thirdArray).head (Fin.natAdd 64 slot) = 0 ∧
    (output roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
      polynomials secondArray thirdArray).tape (Fin.natAdd 64 slot) = (fun _ => blank) := by
  have outsideDestination : Fin.natAdd 64 slot ≠ (69 : Fin 70) := by
    intro equal
    apply notDestination
    apply Fin.ext
    have values := congrArg Fin.val equal
    change 64+slot.val=69 at values
    change slot.val=5
    omega
  simp [output, prepared, setTape, outsideDestination, Tapes.append, SharedBank.empty]

theorem native_output (roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (polynomials : List (Rec coefficientCount)) (secondArray thirdArray : List Bool) :
    (output roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
      polynomials secondArray thirdArray).head 69 = 0 ∧
    (output roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
      polynomials secondArray thirdArray).tape 69 = NativeSignExtendArray.word
        (NativeSignExtendArray.widened (fields wordWidth polynomials)
          (LayerReservationHeaders.nativeWidth activeCount chunkWidth wordWidth)) := by
  simp only [output, setTape, Function.update_self, and_self]

theorem output_widths (wordWidth activeCount chunkWidth : ℕ) (polynomials : List (Rec coefficientCount)) :
    ∀ field ∈ (fields wordWidth polynomials).map (fun source => NativeSignExtend.extended source
      (LayerReservationHeaders.nativeWidth activeCount chunkWidth wordWidth)),
      field.length = LayerReservationHeaders.nativeWidth activeCount chunkWidth wordWidth := by
  intro field member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
  apply NativeSignExtend.extended_length
  rw [field_widths wordWidth polynomials source sourceMember]
  unfold LayerReservationHeaders.nativeWidth
  omega

theorem nonfallback_flag (roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (polynomials : List (Rec coefficientCount)) (secondArray thirdArray : List Bool) :
    (output roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
      polynomials secondArray thirdArray).tape 39 0 =
      bitSymbol (decide (LayerReservationHeaders.reservationAxes roleCount arity precision axes chunkWidth < activeCount)) := by
  exact LayerPreparedInput.nonfallback_flag roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit
    wordWidth polynomials secondArray thirdArray

end
end IntegerMultBounds.Machine.LayerGuardedInput
