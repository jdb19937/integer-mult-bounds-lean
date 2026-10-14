module

public import IntegerMultBounds.Machine.LayerHeaderRead
public import IntegerMultBounds.Machine.BinaryDescriptorDifference

@[expose] public section
namespace IntegerMultBounds.Machine.LayerSelectedBitSetup
noncomputable section
variable {alphabet : ℕ}
open SharedPlacementAlphabet (setTape)
open Spec.SignedRingProduct (layerHeader)

def oneBits : List Bool := RecursiveChildQuotientsConstant.bits 1

def differenceSlots : Fin (3+14) ≃ Fin 17 where
  toFun := ![13,15,16,0,1,2,3,4,5,6,7,8,9,10,11,12,14]
  invFun := ![3,4,5,6,7,8,9,10,11,12,13,14,15,0,16,1,2]
  left_inv := by decide
  right_inv := by decide

def initializeOne := RecoverWorkspace.atProgram
  (RecursiveChildQuotientsConstant.program (a:=alphabet) 1) (15 : Fin 17)
def difference := Placement.placed (BinaryDescriptorDifference.program (a:=alphabet)) differenceSlots
def cleanup := BinaryDescriptorCleanupList.oneProgram (a:=alphabet) (15 : Fin 17)
def setup := seq (seq (initializeOne (alphabet:=alphabet)) difference) cleanup
def program := seq (extend (LayerHeaderRead.publicProgram (alphabet:=alphabet)) 2) setup

def controls (constantValue selectedValue : Option ℕ) : Tapes 2 alphabet :=
  ⟨![LayerHeaderRead.descriptorHead constantValue,LayerHeaderRead.descriptorHead selectedValue],
    ![LayerHeaderRead.descriptorTape constantValue,LayerHeaderRead.descriptorTape selectedValue]⟩

def frame (caller : Tapes 15 alphabet) : Tapes 14 alphabet :=
  ⟨fun port => caller.head ⟨if port.val=13 then 14 else port.val,by have := port.isLt; split_ifs <;> omega⟩,
    fun port => caller.tape ⟨if port.val=13 then 14 else port.val,by have := port.isLt; split_ifs <;> omega⟩⟩

private theorem difference_bank (caller : Tapes 15 alphabet) (selectedBits : List Bool)
    (sourceTape : caller.tape 13=CountedLoopReuseAlphabet.binary selectedBits)
    (sourceHead : caller.head 13=1) (resultTape : ℤ → Fin (alphabet+4)) (resultHead : ℤ) :
    ((BinaryDescriptorDifference.bank selectedBits oneBits resultTape resultHead).append (frame caller)).reindex differenceSlots=
      caller.append (⟨![1,resultHead],![CountedLoopReuseAlphabet.binary oneBits,resultTape]⟩ : Tapes 2 alphabet) := by
  apply congrArg₂ Tapes.mk
  all_goals
    funext port
    fin_cases port <;> first | rfl | exact sourceHead.symm | exact sourceTape.symm

theorem runs_setup (caller : Tapes 15 alphabet) (selectedBit : ℕ)
    (selectedTape : caller.tape 13=BinaryDescriptorStack.descriptor (GammaHeaderRead.bits (selectedBit+1)))
    (selectedHead : caller.head 13=1) :
    HoareTime (setup (alphabet:=alphabet))
      (· = caller.append (controls none none))
      (· = caller.append (controls none (some selectedBit)))
      (6*max (Nat.size (selectedBit+1)) 1+38) := by
  let initialBank := caller.append (controls (alphabet:=alphabet) none none)
  let constantBank := caller.append (controls (alphabet:=alphabet) (some 1) none)
  let resultBank := caller.append (controls (alphabet:=alphabet) (some 1) (some selectedBit))
  have initialized := RecoverWorkspace.runs_one_at
    (RecursiveChildQuotientsConstant.program (a:=alphabet) 1) (15 : Fin 17) initialBank
    (fun _ => blank) (BinaryDescriptorStack.descriptor oneBits) 0 1 rfl rfl
    (RecursiveChildQuotientsConstant.initialize_hoare 1)
  have initializedBank : setTape initialBank (15 : Fin 17) (BinaryDescriptorStack.descriptor oneBits) 1=constantBank := by
    apply congrArg₂ Tapes.mk
    all_goals funext port; fin_cases port <;> rfl
  rw [initializedBank] at initialized
  have originalSource : caller.tape 13=CountedLoopReuseAlphabet.binary (GammaHeaderRead.bits (selectedBit+1)) :=
    selectedTape.trans (GammaDescriptorRead.controller_descriptor _)
  have subtracted := hoare_place
    (BinaryDescriptorDifference.difference_hoare (a:=alphabet) (GammaHeaderRead.bits (selectedBit+1)) oneBits
      (by rw [GammaHeaderRead.decoded_value]; change Counter.value (RecursiveChildQuotientsConstant.bits 1)≤selectedBit+1;
          rw [RecursiveChildQuotientsConstant.bits_value]; omega))
    differenceSlots (frame caller)
  have resultValue : Counter.value (GammaHeaderRead.bits (selectedBit+1))-Counter.value oneBits=selectedBit := by
    rw [GammaHeaderRead.decoded_value]
    change selectedBit+1-Counter.value (RecursiveChildQuotientsConstant.bits 1)=selectedBit
    rw [RecursiveChildQuotientsConstant.bits_value]
    omega
  simp only [BinaryDescriptorDifference.input,BinaryDescriptorDifference.output,resultValue] at subtracted
  rw [difference_bank caller _ originalSource selectedHead,difference_bank caller _ originalSource selectedHead] at subtracted
  rw [←GammaDescriptorRead.controller_descriptor,←GammaHeaderRead.bits_eq_native selectedBit] at subtracted
  change HoareTime (difference (alphabet:=alphabet)) (· = constantBank) (· = resultBank)
    (6*max (GammaHeaderRead.bits (selectedBit+1)).length oneBits.length+21) at subtracted
  have cleared := BinaryDescriptorCleanupList.one_hoare (a:=alphabet) (15 : Fin 17) resultBank oneBits
    rfl rfl
  have clearedBank : setTape resultBank (15 : Fin 17) (fun _ => blank) 0=caller.append (controls none (some selectedBit)) := by
    apply congrArg₂ Tapes.mk
    all_goals funext port; fin_cases port <;> rfl
  rw [clearedBank] at cleared
  unfold setup initializeOne
  apply ((initialized.seq subtracted).seq cleared).consequence (fun _ equality => equality) (fun _ equality => equality)
  simp only [GammaHeaderRead.bits,List.length_reverse,Spec.SignedRingProduct.length_msbBits,
    RecursiveChildQuotientsConstant.cost]
  have oneLength : oneBits.length=1 := by decide
  have nativeOneLength : (RecursiveChildQuotientsConstant.bits 1).length=1 := by decide
  rw [oneLength,nativeOneLength]
  omega

def output (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (firstArray secondArray thirdArray : List Bool) : Tapes 17 alphabet :=
  (LayerHeaderRead.publicBank
    (layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
    firstArray secondArray thirdArray
    (fun field => some (LayerHeaderRead.fields precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth field))).append
      (controls none (some selectedBit))

theorem runs_public (parameters : Spec.SignedRingProduct.LayerParams) (parametersValid : parameters.Valid)
    (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (precisionPositive : 1≤precision)
    (admissible : Spec.SignedRingProduct.LayerAdmissible parameters precision axes coefficientCount activeCount
      outerCount suffixCount chunkWidth selectedBit wordWidth)
    (firstArray secondArray thirdArray : List Bool) :
    HoareTime (program (alphabet:=alphabet))
      (· = Spec.SignedRingProduct.bank
        (layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
        firstArray secondArray thirdArray)
      (· = output precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
        firstArray secondArray thirdArray)
      (11*(layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth).length+308) := by
  let decodedBank := LayerHeaderRead.publicBank (alphabet:=alphabet)
    (layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
    firstArray secondArray thirdArray
    (fun field => some (LayerHeaderRead.fields precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth field))
  have parsed := hoare_extend_eq
    (LayerHeaderRead.runs_admissible (alphabet:=alphabet) parameters parametersValid precision axes coefficientCount activeCount
      outerCount suffixCount chunkWidth selectedBit wordWidth precisionPositive admissible firstArray secondArray thirdArray)
    (controls (alphabet:=alphabet) none none)
  have ready := LayerHeaderRead.public_descriptors (alphabet:=alphabet) precision axes coefficientCount activeCount outerCount
    suffixCount chunkWidth selectedBit wordWidth firstArray secondArray thirdArray (7 : Fin 9)
  have setupRun := runs_setup decodedBank selectedBit ready.2.1 ready.1
  have initialBank : (Spec.SignedRingProduct.bank (t:=15) (a:=alphabet)
      (layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
      firstArray secondArray thirdArray).append (controls none none)=
      Spec.SignedRingProduct.bank (t:=17)
        (layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
        firstArray secondArray thirdArray := by
    apply congrArg₂ Tapes.mk
    all_goals funext port; fin_cases port <;> rfl
  rw [initialBank] at parsed
  unfold program output
  apply (parsed.seq setupRun).consequence (fun _ equality => equality) (fun _ equality => equality)
  have selectedLength := Spec.SignedRingProduct.length_gamma (by omega : 1≤selectedBit+1)
  have selectedPositive := Nat.size_pos.mpr (by omega : 1≤selectedBit+1)
  simp only [layerHeader,List.length_append]
  omega

theorem output_selected (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (firstArray secondArray thirdArray : List Bool) :
    let resultBank := output (alphabet:=alphabet) precision axes coefficientCount activeCount outerCount suffixCount
      chunkWidth selectedBit wordWidth firstArray secondArray thirdArray
    resultBank.head 16=1 ∧
      resultBank.tape 16=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits selectedBit) ∧
      Counter.value (RecursiveChildQuotientsConstant.bits selectedBit)=selectedBit ∧
      GrowingCounterData.Canonical (RecursiveChildQuotientsConstant.bits selectedBit) := by
  refine ⟨rfl,?_,RecursiveChildQuotientsConstant.bits_value _,RecursiveChildQuotientsConstant.bits_canonical _⟩
  change BinaryDescriptorStack.descriptor (GammaHeaderRead.bits selectedBit)=_
  rw [GammaHeaderRead.bits_eq_native,BinaryDescriptorStackRoundtrip.descriptor_encoded]

theorem output_native_fields (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (firstArray secondArray thirdArray : List Bool) (field : Fin 9) :
    let values := LayerHeaderRead.fields precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
    let resultBank := output (alphabet:=alphabet) precision axes coefficientCount activeCount outerCount suffixCount
      chunkWidth selectedBit wordWidth firstArray secondArray thirdArray
    resultBank.head (Fin.castAdd 2 (Fin.natAdd 6 field))=1 ∧
      resultBank.tape (Fin.castAdd 2 (Fin.natAdd 6 field))=
        RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits (values field)) := by
  have descriptors := LayerHeaderRead.public_descriptors (alphabet:=alphabet) precision axes coefficientCount activeCount
    outerCount suffixCount chunkWidth selectedBit wordWidth firstArray secondArray thirdArray field
  refine ⟨?_,?_⟩
  · simpa only [output,Tapes.append,Fin.addCases_left] using descriptors.1
  · simpa only [output,Tapes.append,Fin.addCases_left,GammaHeaderRead.bits_eq_native,
      BinaryDescriptorStackRoundtrip.descriptor_encoded] using descriptors.2.1

theorem output_public_frame (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (firstArray secondArray thirdArray : List Bool) (slot : Fin 6) :
    let resultBank := output (alphabet:=alphabet) precision axes coefficientCount activeCount outerCount suffixCount
      chunkWidth selectedBit wordWidth firstArray secondArray thirdArray
    resultBank.head (Fin.castAdd 11 slot)=0 ∧
      resultBank.tape (Fin.castAdd 11 slot)=
        (Spec.SignedRingProduct.bank (t:=17)
          (layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
          firstArray secondArray thirdArray).tape (Fin.castAdd 11 slot) := by
  fin_cases slot <;> exact ⟨rfl,rfl⟩

theorem output_constant_blank (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (firstArray secondArray thirdArray : List Bool) :
    let resultBank := output (alphabet:=alphabet) precision axes coefficientCount activeCount outerCount suffixCount
      chunkWidth selectedBit wordWidth firstArray secondArray thirdArray
    resultBank.head 15=0 ∧ resultBank.tape 15=(fun _ => blank) := ⟨rfl,rfl⟩

def constant (parameters : Spec.SignedRingProduct.LayerParams) : ℝ := 3*LayerHeaderRead.constant parameters

theorem runtime_le_layer_cost (parameters : Spec.SignedRingProduct.LayerParams) (parametersValid : parameters.Valid)
    (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (precisionPositive : 1≤precision)
    (admissible : Spec.SignedRingProduct.LayerAdmissible parameters precision axes coefficientCount activeCount
      outerCount suffixCount chunkWidth selectedBit wordWidth) :
    ((11*(layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth).length+308 : ℕ) : ℝ)≤
      constant parameters*Spec.SignedRingProduct.layerCost parameters axes coefficientCount
        (outerCount*suffixCount*2^(chunkWidth*activeCount)) wordWidth := by
  have headerBudget := LayerHeaderRead.runtime_le_layer_cost parameters parametersValid precision axes coefficientCount activeCount
    outerCount suffixCount chunkWidth selectedBit wordWidth precisionPositive admissible
  have scaledBudget := mul_le_mul_of_nonneg_left headerBudget (by norm_num : (0 : ℝ)≤3)
  have setupBound :
      ((11*(layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth).length+308 : ℕ) : ℝ)≤
        3*((5*(layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth).length+263 : ℕ) : ℝ) := by
    push_cast
    nlinarith [Nat.cast_nonneg (α:=ℝ)
      (layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth).length]
  simpa only [constant,mul_assoc] using setupBound.trans scaledBudget

end
end IntegerMultBounds.Machine.LayerSelectedBitSetup
