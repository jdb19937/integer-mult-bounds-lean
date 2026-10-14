module

public import IntegerMultBounds.Machine.LayerReservationHeaders

@[expose] public section
namespace IntegerMultBounds.Machine.LayerReservationSetup
noncomputable section
variable {alphabet : ℕ}

def geometry (roleCount arity : ℕ) := Placement.placed
  (LayerReservationHeaders.program (alphabet:=alphabet) roleCount arity) LayerControlBank.nativePlacement
def program (roleCount arity : ℕ) := seq (LayerControlBank.program (alphabet:=alphabet)) (geometry roleCount arity)

def output (roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (firstArray secondArray thirdArray : List Bool) : Tapes 60 alphabet :=
  LayerControlBank.block
    (LayerSelectedBitSetup.output precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
      firstArray secondArray thirdArray)
    (LayerReservationHeaders.finished roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)

def cost (roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ) :=
  11*(Spec.SignedRingProduct.layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth).length+
    310+LayerControlBank.copyCost precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth+
    LayerReservationHeaders.cost roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth

theorem runs_public (parameters : Spec.SignedRingProduct.LayerParams) (parametersValid : parameters.Valid)
    (roleCount arity : ℕ) (rolesPositive : 2≤roleCount) (arityPositive : 2≤arity)
    (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (precisionPositive : 1≤precision)
    (admissible : Spec.SignedRingProduct.LayerAdmissible parameters precision axes coefficientCount activeCount
      outerCount suffixCount chunkWidth selectedBit wordWidth)
    (firstArray secondArray thirdArray : List Bool) :
    HoareTime (program (alphabet:=alphabet) roleCount arity)
      (· = Spec.SignedRingProduct.bank
        (Spec.SignedRingProduct.layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
        firstArray secondArray thirdArray)
      (· = output roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
        firstArray secondArray thirdArray)
      (cost roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth) := by
  have controls := LayerControlBank.runs_public (alphabet:=alphabet) parameters parametersValid precision axes coefficientCount activeCount
    outerCount suffixCount chunkWidth selectedBit wordWidth precisionPositive admissible firstArray secondArray thirdArray
  have validity := parametersValid
  rcases validity with ⟨_,_,_,_,_,_,_,_,_,_,lowerAxesPositive,_,_,_,_,_,_⟩
  have admissibility := admissible
  rcases admissibility with ⟨axesLower,_,_,_,_,_,_,_,_,selectedFits,_,_,_,_⟩
  have precisionRealPositive : (0 : ℝ)<precision := by exact_mod_cast precisionPositive
  have axesRealPositive : (0 : ℝ)<axes := lt_of_lt_of_le
    (mul_pos lowerAxesPositive (Real.rpow_pos_of_pos precisionRealPositive _)) axesLower
  have axesPositive : 0<axes := by exact_mod_cast axesRealPositive
  have nativeRun := LayerReservationHeaders.runs (alphabet:=alphabet) roleCount arity precision axes coefficientCount activeCount outerCount
    suffixCount chunkWidth selectedBit wordWidth rolesPositive arityPositive (by omega) axesPositive (by omega)
  have placed := hoare_place nativeRun LayerControlBank.nativePlacement
    (LayerSelectedBitSetup.output precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
      firstArray secondArray thirdArray)
  rw [LayerControlBank.native_bank,LayerControlBank.native_bank] at placed
  unfold LayerControlBank.output at controls
  unfold program geometry output cost
  exact (controls.seq placed).consequence (fun _ equality => equality) (fun _ equality => equality) (by omega)

def port (slot : Fin 28) : Fin 60 := Fin.castAdd 15 (Fin.natAdd 17 slot)

theorem descriptor (roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (firstArray secondArray thirdArray : List Bool) (slot : Fin 28) (value : ℕ)
    (valueReady : LayerReservationHeaders.finished roleCount arity precision axes coefficientCount activeCount outerCount suffixCount
      chunkWidth selectedBit wordWidth slot=some value) :
    let bank := output (alphabet:=alphabet) roleCount arity precision axes coefficientCount activeCount outerCount suffixCount
      chunkWidth selectedBit wordWidth firstArray secondArray thirdArray
    bank.head (port slot)=1 ∧ bank.tape (port slot)=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits value) := by
  simp [output,LayerControlBank.block,port,Tapes.append,
    ActiveRepairRankHeadersCommands.caller,valueReady]

theorem reservation_shape (roleCount arity precision axes chunkWidth : ℕ) :
    LayerReservationHeaders.reservationAxes roleCount arity precision axes chunkWidth=
      CompactGlobalReservation.reservedAxes roleCount arity axes (LayerReservationHeaders.guard precision) chunkWidth := rfl

theorem original_bits (roleCount arity precision axes activeCount chunkWidth : ℕ)
    (chunkPositive : 0<chunkWidth)
    (reservationFits : LayerReservationHeaders.reservationAxes roleCount arity precision axes chunkWidth≤activeCount) :
    CompactGlobalRowPadding.rowAxes roleCount arity axes*chunkWidth+
      (CompactGlobalReservation.shape roleCount arity axes activeCount (LayerReservationHeaders.guard precision) chunkWidth 1).bits=
      activeCount*chunkWidth :=
  CompactGlobalReservation.original_bits roleCount arity axes activeCount (LayerReservationHeaders.guard precision) chunkWidth 1
    chunkPositive reservationFits

theorem original_fields (roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (firstArray secondArray thirdArray : List Bool) (slot : Fin 17) :
    let bank := output (alphabet:=alphabet) roleCount arity precision axes coefficientCount activeCount outerCount suffixCount
      chunkWidth selectedBit wordWidth firstArray secondArray thirdArray
    bank.head (Fin.castAdd 15 (Fin.castAdd 28 slot))=
      (LayerSelectedBitSetup.output (alphabet:=alphabet) precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
        firstArray secondArray thirdArray).head slot ∧
      bank.tape (Fin.castAdd 15 (Fin.castAdd 28 slot))=
        (LayerSelectedBitSetup.output (alphabet:=alphabet) precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
          firstArray secondArray thirdArray).tape slot := by
  simp only [output,LayerControlBank.block,Tapes.append,Fin.addCases_left,and_self]

theorem private_blank (roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (firstArray secondArray thirdArray : List Bool) (slot : Fin 15) :
    let bank := output (alphabet:=alphabet) roleCount arity precision axes coefficientCount activeCount outerCount suffixCount
      chunkWidth selectedBit wordWidth firstArray secondArray thirdArray
    bank.head (Fin.natAdd 45 slot)=0 ∧ bank.tape (Fin.natAdd 45 slot)=(fun _ => blank) := by
  simp only [output,LayerControlBank.block,Tapes.append,Fin.addCases_right,SharedBank.empty,and_self]

end
end IntegerMultBounds.Machine.LayerReservationSetup
