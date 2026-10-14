module

public import IntegerMultBounds.Machine.LayerNativeInput
public import IntegerMultBounds.Machine.LayerReservationClassifier

@[expose] public section
namespace IntegerMultBounds.Machine.LayerPreparedInput
noncomputable section
open Spec.SignedRingProduct (Rec array layerHeader)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {coefficientCount : ℕ}

def program (roleCount arity : ℕ) := seq (LayerNativeInput.program roleCount arity)
  (extend (LayerReservationClassifier.classify (alphabet:=2)) 4)

def nativeFrame (width : ℕ) (polynomials : List (Rec coefficientCount)) : Tapes 4 2 :=
  ⟨fun _ => 0,![fun _ => blank,fun _ => blank,fun _ => blank,
    putWord (fun _ => blank) 0 (ChirpPublicArray.native (LayerNativeInput.publicPairs width polynomials))]⟩

def output (roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (polynomials : List (Rec coefficientCount)) (secondArray thirdArray : List Bool) : Tapes 64 2 :=
  setTape (LayerNativeInput.output roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
    polynomials secondArray thirdArray) (39 : Fin 64)
    (BinaryDescriptorCompare.result (bits (LayerReservationHeaders.reservationAxes roleCount arity precision axes chunkWidth))
      (bits activeCount)) 0

def cost (roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (polynomials : List (Rec coefficientCount)) :=
  LayerNativeInput.cost roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth polynomials+1+
    BinaryDescriptorCompare.cost (bits (LayerReservationHeaders.reservationAxes roleCount arity precision axes chunkWidth)) (bits activeCount)

theorem native_bank (roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (polynomials : List (Rec coefficientCount)) (secondArray thirdArray : List Bool) :
    (LayerPolynomialHeaders.output (alphabet:=2) roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth
      selectedBit wordWidth (array wordWidth polynomials) secondArray thirdArray).append (nativeFrame wordWidth polynomials)=
      LayerNativeInput.output roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
        polynomials secondArray thirdArray := by
  apply Placement.Tapes.ext'
  all_goals intro slot; fin_cases slot <;> rfl

theorem runs_public (parameters : Spec.SignedRingProduct.LayerParams) (parametersValid : parameters.Valid)
    (roleCount arity : ℕ) (rolesPositive : 2≤roleCount) (arityPositive : 2≤arity)
    (precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (precisionPositive : 1≤precision)
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
  have nativeRun := LayerNativeInput.runs_public parameters parametersValid roleCount arity rolesPositive arityPositive precision axes activeCount
    outerCount suffixCount chunkWidth selectedBit wordWidth precisionPositive admissible polynomials secondArray thirdArray
  let caller := LayerPolynomialHeaders.output (alphabet:=2) roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth
    selectedBit wordWidth (array wordWidth polynomials) secondArray thirdArray
  let reservedAxes := LayerReservationHeaders.reservationAxes roleCount arity precision axes chunkWidth
  have reservedHead : caller.head 37=1 := rfl
  have reservedTape : caller.tape 37=BinaryDescriptorStack.descriptor (bits reservedAxes) := by
    change RadixZeroFill.encodedBinary (bits reservedAxes)=_
    exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm
  have activeHead : caller.head 20=1 := rfl
  have activeTape : caller.tape 20=BinaryDescriptorStack.descriptor (bits activeCount) := by
    change RadixZeroFill.encodedBinary (bits activeCount)=_
    exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm
  have compared := hoare_extend_eq (LayerReservationClassifier.compares caller reservedAxes activeCount
    reservedHead reservedTape activeHead activeTape rfl rfl) (nativeFrame wordWidth polynomials)
  have appendedUpdate : (setTape caller (39 : Fin 60) (BinaryDescriptorCompare.result (bits reservedAxes) (bits activeCount)) 0).append
      (nativeFrame wordWidth polynomials)=
      setTape (caller.append (nativeFrame wordWidth polynomials)) (39 : Fin 64)
        (BinaryDescriptorCompare.result (bits reservedAxes) (bits activeCount)) 0 := by
    exact (SharedPlacementAlphabet.setTape_append_left caller (nativeFrame wordWidth polynomials) (39 : Fin 60) _ 0).symm
  rw [appendedUpdate,native_bank] at compared
  unfold program output cost
  exact nativeRun.seq compared

theorem nonfallback_flag (roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (polynomials : List (Rec coefficientCount)) (secondArray thirdArray : List Bool) :
    (output roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
      polynomials secondArray thirdArray).tape 39 0=
      bitSymbol (decide (LayerReservationHeaders.reservationAxes roleCount arity precision axes chunkWidth<activeCount)) := by
  simp only [output,setTape,Function.update_self,BinaryDescriptorCompare.result,RecursiveChildQuotientsConstant.bits_value]

theorem native_source (roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (polynomials : List (Rec coefficientCount)) (secondArray thirdArray : List Bool) :
    let bank := output roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
      polynomials secondArray thirdArray
    bank.head 63=0 ∧ bank.tape 63=putWord (fun _ => blank) 0 (ChirpPublicArray.native (LayerNativeInput.publicPairs wordWidth polynomials)) := by
  simp only [output,setTape,Function.update_of_ne (by decide : (63 : Fin 64)≠39),LayerNativeInput.output,Function.update_self,and_self]

end
end IntegerMultBounds.Machine.LayerPreparedInput
