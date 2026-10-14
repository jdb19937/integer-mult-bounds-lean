module

public import IntegerMultBounds.Machine.LayerReservationSetup
public import IntegerMultBounds.Machine.BinaryDescriptorCompare
public import IntegerMultBounds.Machine.PlacementBankEndpoint

@[expose] public section
namespace IntegerMultBounds.Machine.LayerReservationClassifier
noncomputable section
variable {alphabet : ℕ}
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)

def ports : Fin 3 → Fin 60 := ![37,20,39]
theorem ports_injective : Function.Injective ports := by decide
def placement := InjectivePlacement.placement ports ports_injective (by decide : 3+57=60)
def classify := Placement.placed (BinaryDescriptorCompare.program (q:=alphabet)) placement
def program (roleCount arity : ℕ) := seq (LayerReservationSetup.program (alphabet:=alphabet) roleCount arity) classify

def output (roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (firstArray secondArray thirdArray : List Bool) : Tapes 60 alphabet :=
  setTape (LayerReservationSetup.output roleCount arity precision axes coefficientCount activeCount outerCount suffixCount
    chunkWidth selectedBit wordWidth firstArray secondArray thirdArray) (39 : Fin 60)
    (BinaryDescriptorCompare.result (bits (LayerReservationHeaders.reservationAxes roleCount arity precision axes chunkWidth))
      (bits activeCount)) 0

def cost (roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ) :=
  LayerReservationSetup.cost roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth+1+
    BinaryDescriptorCompare.cost (bits (LayerReservationHeaders.reservationAxes roleCount arity precision axes chunkWidth)) (bits activeCount)

theorem compares (caller : Tapes 60 alphabet) (reservedAxes activeCount : ℕ)
    (reservedHead : caller.head 37=1)
    (reservedTape : caller.tape 37=BinaryDescriptorStack.descriptor (bits reservedAxes))
    (activeHead : caller.head 20=1)
    (activeTape : caller.tape 20=BinaryDescriptorStack.descriptor (bits activeCount))
    (flagHead : caller.head 39=0) (flagTape : caller.tape 39=(fun _ => blank)) :
    HoareTime (classify (alphabet:=alphabet)) (· = caller)
      (· = setTape caller (39 : Fin 60) (BinaryDescriptorCompare.result (bits reservedAxes) (bits activeCount)) 0)
      (BinaryDescriptorCompare.cost (bits reservedAxes) (bits activeCount)) := by
  have inputReady : Placement.active placement caller=BinaryDescriptorCompare.input (bits reservedAxes) (bits activeCount) := by
    rw [placement,InjectivePlacement.active_bank,BinaryDescriptorCompare.input,BinaryDescriptorCompare.bank,
      BinaryCompare.cfg,Config.tapes]
    apply congrArg₂ Tapes.mk
    · funext slot
      fin_cases slot
      · exact reservedHead
      · exact activeHead
      · exact flagHead
    · funext slot
      fin_cases slot
      · exact reservedTape
      · exact activeTape
      · exact flagTape
  have compared := Placement.hoare_at (BinaryDescriptorCompare.compare_hoare (bits reservedAxes) (bits activeCount))
    placement caller inputReady
  have endpoint : Placement.replace placement caller (BinaryDescriptorCompare.output (bits reservedAxes) (bits activeCount))=
      setTape caller (39 : Fin 60) (BinaryDescriptorCompare.result (bits reservedAxes) (bits activeCount)) 0 := by
    apply InjectivePlacement.replace_eq ports ports_injective (by decide : 3+57=60) caller _
    · rw [InjectivePlacement.active_bank,BinaryDescriptorCompare.output,BinaryDescriptorCompare.bank,BinaryCompare.cfg,Config.tapes]
      apply congrArg₂ Tapes.mk
      · funext slot
        fin_cases slot
        · simpa [ports,setTape] using reservedHead
        · simpa [ports,setTape] using activeHead
        · simp [ports,setTape]
      · funext slot
        fin_cases slot
        · simpa [ports,setTape] using reservedTape
        · simpa [ports,setTape] using activeTape
        · simp [ports,setTape]
    · intro slot outside
      have notFlag : slot≠39 := by intro equal; exact outside 2 (by simpa [ports] using equal.symm)
      simp only [setTape,Function.update_of_ne notFlag,and_self]
  apply compared.consequence (fun _ ready => ready) _ le_rfl
  rintro resultBank ⟨small,smallReady,resultReady⟩
  rw [smallReady] at resultReady
  exact resultReady.trans endpoint

theorem classifies (roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (firstArray secondArray thirdArray : List Bool) :
    HoareTime (classify (alphabet:=alphabet))
      (· = LayerReservationSetup.output roleCount arity precision axes coefficientCount activeCount outerCount suffixCount
        chunkWidth selectedBit wordWidth firstArray secondArray thirdArray)
      (· = output roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
        firstArray secondArray thirdArray)
      (BinaryDescriptorCompare.cost (bits (LayerReservationHeaders.reservationAxes roleCount arity precision axes chunkWidth)) (bits activeCount)) := by
  let caller := LayerReservationSetup.output (alphabet:=alphabet) roleCount arity precision axes coefficientCount activeCount outerCount suffixCount
    chunkWidth selectedBit wordWidth firstArray secondArray thirdArray
  have reservation := LayerReservationSetup.descriptor (alphabet:=alphabet) roleCount arity precision axes coefficientCount activeCount outerCount
    suffixCount chunkWidth selectedBit wordWidth firstArray secondArray thirdArray 20
    (LayerReservationHeaders.reservationAxes roleCount arity precision axes chunkWidth) rfl
  have selected := LayerReservationSetup.descriptor (alphabet:=alphabet) roleCount arity precision axes coefficientCount activeCount outerCount
    suffixCount chunkWidth selectedBit wordWidth firstArray secondArray thirdArray 3 activeCount rfl
  exact compares caller (LayerReservationHeaders.reservationAxes roleCount arity precision axes chunkWidth) activeCount
    reservation.1 (reservation.2.trans (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm)
    selected.1 (selected.2.trans (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm) rfl rfl

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
      (cost roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth) :=
  (LayerReservationSetup.runs_public parameters parametersValid roleCount arity rolesPositive arityPositive precision axes coefficientCount activeCount
    outerCount suffixCount chunkWidth selectedBit wordWidth precisionPositive admissible firstArray secondArray thirdArray).seq
    (classifies roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
      firstArray secondArray thirdArray)

theorem nonfallback_flag (roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (firstArray secondArray thirdArray : List Bool) :
    (output (alphabet:=alphabet) roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
      firstArray secondArray thirdArray).tape 39 0=
      bitSymbol (decide (LayerReservationHeaders.reservationAxes roleCount arity precision axes chunkWidth<activeCount)) := by
  simp only [output,setTape,Function.update_self,BinaryDescriptorCompare.result,RecursiveChildQuotientsConstant.bits_value]

end
end IntegerMultBounds.Machine.LayerReservationClassifier
