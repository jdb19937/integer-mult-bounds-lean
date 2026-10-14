module

public import IntegerMultBounds.Machine.GammaHeaderRead
public import IntegerMultBounds.Machine.ReturnOrigin
public import IntegerMultBounds.Spec.SimultaneousLayer

@[expose] public section
namespace IntegerMultBounds.Machine.LayerHeaderRead
noncomputable section
variable {alphabet : ℕ}
open RecoverCarryStep (word)
open Spec.SignedRingProduct (gamma header layerHeader)

def descriptorHead (value : Option ℕ) : ℤ := if value.isSome then 1 else 0
def descriptorTape (value : Option ℕ) : ℤ → Fin (alphabet+4) :=
  value.elim (fun _ => blank) (fun number => BinaryDescriptorStack.descriptor (GammaHeaderRead.bits number))

def bank (source : ℤ → Fin (alphabet+4)) (sourceHead : ℤ) (values : Fin 9 → Option ℕ) : Tapes 12 alphabet :=
  (⟨![0,sourceHead,0],![fun _ => blank,source,fun _ => blank]⟩ : Tapes 3 alphabet).append
    ⟨fun field => descriptorHead (values field),fun field => descriptorTape (values field)⟩

def slots : Fin 3 → Fin (6+6) ≃ Fin 12
  | 0 => Equiv.refl _
  | 1 => {
      toFun := ![0,1,2,6,7,8,3,4,5,9,10,11]
      invFun := ![0,1,2,6,7,8,3,4,5,9,10,11]
      left_inv := by decide
      right_inv := by decide }
  | 2 => {
      toFun := ![0,1,2,9,10,11,3,4,5,6,7,8]
      invFun := ![0,1,2,6,7,8,9,10,11,3,4,5]
      left_inv := by decide
      right_inv := by decide }

def read (group : Fin 3) : Program 12 75 alphabet := Placement.placed GammaHeaderRead.program (slots group)
def decoder : Program 12 225 alphabet := seq (seq (read 0) (read 1)) (read 2)

def rewindSlots : Fin (1+11) ≃ Fin 12 where
  toFun := ![1,0,2,3,4,5,6,7,8,9,10,11]
  invFun := ![1,0,2,3,4,5,6,7,8,9,10,11]
  left_inv := by decide
  right_inv := by decide

def rewind : Program 12 3 alphabet := Placement.placed ReturnOrigin.program rewindSlots
def program : Program 12 228 alphabet := seq decoder rewind

def frame (group : Fin 3) (values : Fin 9 → Option ℕ) : Tapes 6 alphabet :=
  let remaining : Fin 6 → Option ℕ := match group with
    | 0 => ![values 3,values 4,values 5,values 6,values 7,values 8]
    | 1 => ![values 0,values 1,values 2,values 6,values 7,values 8]
    | 2 => ![values 0,values 1,values 2,values 3,values 4,values 5]
  ⟨fun field => descriptorHead (remaining field),fun field => descriptorTape (remaining field)⟩

private theorem assembled (group : Fin 3) (source : ℤ → Fin (alphabet+4))
    (sourceHead : ℤ) (values : Fin 9 → Option ℕ) :
    ((GammaHeaderRead.bank source sourceHead
      (values ⟨3*group.val,by have := group.isLt; omega⟩)
      (values ⟨3*group.val+1,by have := group.isLt; omega⟩)
      (values ⟨3*group.val+2,by have := group.isLt; omega⟩)).append
      (frame group values)).reindex (slots group)=bank source sourceHead values := by
  apply congrArg₂ Tapes.mk
  all_goals
    funext port
    fin_cases group <;> fin_cases port <;> rfl

def fields (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ) : Fin 9 → ℕ :=
  ![precision,axes,coefficientCount,activeCount,outerCount,suffixCount,chunkWidth,selectedBit+1,wordWidth]

def filled (values : Fin 9 → ℕ) (count : ℕ) : Fin 9 → Option ℕ :=
  fun field => if field.val<count then some (values field) else none

def input (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ) : Tapes 12 alphabet :=
  bank (word (layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth))
    0 (fun _ => none)

def decoded (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ) : Tapes 12 alphabet :=
  bank (word (layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth))
    (layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth).length
    (fun field => some (fields precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth field))

def output (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ) : Tapes 12 alphabet :=
  bank (word (layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth))
    0 (fun field => some (fields precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth field))

theorem runs_decode (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (precisionPositive : 1≤precision) (axesPositive : 1≤axes) (coefficientPositive : 1≤coefficientCount)
    (activePositive : 1≤activeCount) (outerPositive : 1≤outerCount) (suffixPositive : 1≤suffixCount)
    (chunkPositive : 1≤chunkWidth) (wordPositive : 1≤wordWidth) :
    HoareTime (decoder (alphabet:=alphabet))
      (· = input precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
      (· = decoded precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
      (4*(layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth).length+260) := by
  let values := fields precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
  let firstHeader := header precision axes coefficientCount
  let secondHeader := header activeCount outerCount suffixCount
  let thirdHeader := header chunkWidth (selectedBit+1) wordWidth
  have firstRead := hoare_place
    (GammaHeaderRead.runs_at (alphabet:=alphabet) [] (secondHeader++thirdHeader) precision axes coefficientCount
      precisionPositive axesPositive coefficientPositive)
    (slots 0) (frame 0 (filled values 0))
  have firstInput := assembled (alphabet:=alphabet) 0 (word (firstHeader++secondHeader++thirdHeader)) 0 (filled values 0)
  have firstOutput := assembled (alphabet:=alphabet) 0 (word (firstHeader++secondHeader++thirdHeader)) firstHeader.length (filled values 3)
  change ((GammaHeaderRead.bank _ 0 none none none).append (frame 0 (filled values 0))).reindex (slots 0)=_ at firstInput
  change ((GammaHeaderRead.bank _ firstHeader.length (some precision) (some axes) (some coefficientCount)).append
    (frame 0 (filled values 3))).reindex (slots 0)=_ at firstOutput
  have firstFrame : frame (alphabet:=alphabet) 0 (filled values 3)=frame 0 (filled values 0) := by rfl
  rw [firstFrame] at firstOutput
  simp only [List.nil_append,List.length_nil,Nat.cast_zero,zero_add,←List.append_assoc] at firstRead
  rw [firstInput,firstOutput] at firstRead
  have secondRead := hoare_place
    (GammaHeaderRead.runs_at (alphabet:=alphabet) firstHeader thirdHeader activeCount outerCount suffixCount
      activePositive outerPositive suffixPositive)
    (slots 1) (frame 1 (filled values 3))
  have secondInput := assembled (alphabet:=alphabet) 1 (word (firstHeader++secondHeader++thirdHeader)) firstHeader.length (filled values 3)
  have secondOutput := assembled (alphabet:=alphabet) 1 (word (firstHeader++secondHeader++thirdHeader))
    (firstHeader.length+secondHeader.length) (filled values 6)
  change ((GammaHeaderRead.bank _ firstHeader.length none none none).append (frame 1 (filled values 3))).reindex (slots 1)=_ at secondInput
  change ((GammaHeaderRead.bank _ (firstHeader.length+secondHeader.length) (some activeCount) (some outerCount) (some suffixCount)).append
    (frame 1 (filled values 6))).reindex (slots 1)=_ at secondOutput
  have secondFrame : frame (alphabet:=alphabet) 1 (filled values 6)=frame 1 (filled values 3) := by
    rfl
  rw [secondFrame] at secondOutput
  rw [secondInput,secondOutput] at secondRead
  have thirdRead := hoare_place
    (GammaHeaderRead.runs_at (alphabet:=alphabet) (firstHeader++secondHeader) [] chunkWidth (selectedBit+1) wordWidth
      chunkPositive (by omega) wordPositive)
    (slots 2) (frame 2 (filled values 6))
  have thirdInput := assembled (alphabet:=alphabet) 2 (word (firstHeader++secondHeader++thirdHeader))
    (firstHeader.length+secondHeader.length) (filled values 6)
  have thirdOutput := assembled (alphabet:=alphabet) 2 (word (firstHeader++secondHeader++thirdHeader))
    (firstHeader.length+secondHeader.length+thirdHeader.length) (filled values 9)
  change ((GammaHeaderRead.bank _ (firstHeader.length+secondHeader.length) none none none).append (frame 2 (filled values 6))).reindex (slots 2)=_ at thirdInput
  change ((GammaHeaderRead.bank _ (firstHeader.length+secondHeader.length+thirdHeader.length) (some chunkWidth) (some (selectedBit+1)) (some wordWidth)).append
    (frame 2 (filled values 9))).reindex (slots 2)=_ at thirdOutput
  have thirdFrame : frame (alphabet:=alphabet) 2 (filled values 9)=frame 2 (filled values 6) := by rfl
  rw [thirdFrame] at thirdOutput
  simp only [List.append_nil,List.length_append,Nat.cast_add] at thirdRead
  rw [thirdInput,thirdOutput] at thirdRead
  have execution := (firstRead.seq secondRead).seq thirdRead
  have allEmpty : filled values 0=(fun _ => none) := by funext field; simp [filled]
  have allFilled : filled values 9=(fun field => some (values field)) := by
    funext field
    simp only [filled,ite_eq_left field.isLt]
  have headerEquation : layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth=
      firstHeader++secondHeader++thirdHeader := by simp [layerHeader,firstHeader,secondHeader,thirdHeader,header,List.append_assoc]
  rw [allEmpty,allFilled] at execution
  unfold decoder read input decoded
  rw [headerEquation]
  simp only [List.length_append,Nat.cast_add]
  apply execution.consequence (fun _ equality => equality) (fun _ equality => equality)
  dsimp only [firstHeader,secondHeader,thirdHeader]
  omega

theorem descriptor_value (value : ℕ) : Counter.value (GammaHeaderRead.bits value)=value :=
  GammaHeaderRead.decoded_value value

private theorem rewind_bank (source : ℤ → Fin (alphabet+4)) (sourceHead : ℤ) (values : Fin 9 → Option ℕ) :
    ((⟨fun _ => sourceHead,fun _ => source⟩ : Tapes 1 alphabet).append
      ((⟨![0,0],![fun _ => blank,fun _ => blank]⟩ : Tapes 2 alphabet).append
        ⟨fun field => descriptorHead (values field),fun field => descriptorTape (values field)⟩)).reindex rewindSlots=
      bank source sourceHead values := by
  apply congrArg₂ Tapes.mk
  all_goals funext port; fin_cases port <;> rfl

theorem runs_header (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (precisionPositive : 1≤precision) (axesPositive : 1≤axes) (coefficientPositive : 1≤coefficientCount)
    (activePositive : 1≤activeCount) (outerPositive : 1≤outerCount) (suffixPositive : 1≤suffixCount)
    (chunkPositive : 1≤chunkWidth) (wordPositive : 1≤wordWidth) :
    HoareTime (program (alphabet:=alphabet))
      (· = input precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
      (· = output precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
      (5*(layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth).length+263) := by
  let sourceHeader := layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
  let values := fun field => some (fields precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth field)
  have decodeRun := runs_decode (alphabet:=alphabet) precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
    precisionPositive axesPositive coefficientPositive activePositive outerPositive suffixPositive chunkPositive wordPositive
  have returnRun := hoare_place
    (ReturnOrigin.return_hoare (a:=alphabet) (sourceHeader.map bitSymbol) (by
      intro symbol membership
      obtain ⟨bit,_,rfl⟩ := List.mem_map.mp membership
      cases bit <;> simp [bitSymbol,blank,Fin.ext_iff]))
    rewindSlots ((⟨![0,0],![fun _ => blank,fun _ => blank]⟩ : Tapes 2 alphabet).append
      ⟨fun field => descriptorHead (values field),fun field => descriptorTape (values field)⟩)
  simp only [ReturnOrigin.cfg,Config.tapes,List.length_map] at returnRun
  rw [rewind_bank,rewind_bank] at returnRun
  exact (decodeRun.seq returnRun).consequence (fun _ equality => equality) (fun _ equality => equality)
    (by dsimp only [sourceHeader]; omega)

def publicSlots : Fin (12+3) ≃ Fin 15 where
  toFun := ![4,0,5,6,7,8,9,10,11,12,13,14,1,2,3]
  invFun := ![1,12,13,14,0,2,3,4,5,6,7,8,9,10,11]
  left_inv := by decide
  right_inv := by decide

def publicProgram : Program 15 228 alphabet := Placement.placed program publicSlots

def publicBank (sourceHeader firstArray secondArray thirdArray : List Bool) (values : Fin 9 → Option ℕ) : Tapes 15 alphabet :=
  (Spec.SignedRingProduct.bank (t:=6) sourceHeader firstArray secondArray thirdArray).append
    ⟨fun field => descriptorHead (values field),fun field => descriptorTape (values field)⟩

private theorem public_bank (sourceHeader firstArray secondArray thirdArray : List Bool) (values : Fin 9 → Option ℕ) :
    ((bank (word sourceHeader) 0 values).append
      (⟨![0,0,0],![Spec.SignedRingProduct.wordAt firstArray,Spec.SignedRingProduct.wordAt secondArray,
        Spec.SignedRingProduct.wordAt thirdArray]⟩ : Tapes 3 alphabet)).reindex publicSlots=
      publicBank sourceHeader firstArray secondArray thirdArray values := by
  apply congrArg₂ Tapes.mk
  all_goals
    funext port
    fin_cases port <;> first | rfl | change word sourceHeader=Spec.SignedRingProduct.wordAt sourceHeader
  funext cell
  simpa only [RecoverCarryStep.word,Spec.SignedRingProduct.wordAt,sub_zero] using
    putWord_blank 0 cell (sourceHeader.map (bitSymbol (a:=alphabet)))

theorem runs_public (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (precisionPositive : 1≤precision) (axesPositive : 1≤axes) (coefficientPositive : 1≤coefficientCount)
    (activePositive : 1≤activeCount) (outerPositive : 1≤outerCount) (suffixPositive : 1≤suffixCount)
    (chunkPositive : 1≤chunkWidth) (wordPositive : 1≤wordWidth)
    (firstArray secondArray thirdArray : List Bool) :
    HoareTime (publicProgram (alphabet:=alphabet))
      (· = Spec.SignedRingProduct.bank
        (layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
        firstArray secondArray thirdArray)
      (· = publicBank
        (layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
        firstArray secondArray thirdArray
        (fun field => some (fields precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth field)))
      (5*(layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth).length+263) := by
  have execution := hoare_place
    (runs_header (alphabet:=alphabet) precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
      precisionPositive axesPositive coefficientPositive activePositive outerPositive suffixPositive chunkPositive wordPositive)
    publicSlots (⟨![0,0,0],![Spec.SignedRingProduct.wordAt firstArray,Spec.SignedRingProduct.wordAt secondArray,
      Spec.SignedRingProduct.wordAt thirdArray]⟩ : Tapes 3 alphabet)
  unfold input output at execution
  rw [public_bank,public_bank] at execution
  have initialBank : publicBank (alphabet:=alphabet)
      (layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
      firstArray secondArray thirdArray (fun _ => none)=
      Spec.SignedRingProduct.bank (t:=15)
        (layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
        firstArray secondArray thirdArray := by
    apply congrArg₂ Tapes.mk
    all_goals funext port; fin_cases port <;> rfl
  rwa [initialBank] at execution

theorem runs_admissible (parameters : Spec.SignedRingProduct.LayerParams)
    (parametersValid : parameters.Valid)
    (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (precisionPositive : 1≤precision)
    (admissible : Spec.SignedRingProduct.LayerAdmissible parameters precision axes coefficientCount activeCount
      outerCount suffixCount chunkWidth selectedBit wordWidth)
    (firstArray secondArray thirdArray : List Bool) :
    HoareTime (publicProgram (alphabet:=alphabet))
      (· = Spec.SignedRingProduct.bank
        (layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
        firstArray secondArray thirdArray)
      (· = publicBank
        (layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
        firstArray secondArray thirdArray
        (fun field => some (fields precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth field)))
      (5*(layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth).length+263) := by
  rcases parametersValid with ⟨_,_,_,_,_,_,_,_,_,_,lowerAxesPositive,_,_,_,_,_,_⟩
  rcases admissible with ⟨axesLower,_,coefficientLower,_,_,activePositive,_,outerPositive,suffixPositive,selectedFits,_,_,wordLower,_⟩
  have precisionRealPositive : (0 : ℝ)<precision := by exact_mod_cast precisionPositive
  have axesRealPositive : (0 : ℝ)<axes := lt_of_lt_of_le
    (mul_pos lowerAxesPositive (Real.rpow_pos_of_pos precisionRealPositive _)) axesLower
  have coefficientRealPositive : (0 : ℝ)<coefficientCount := lt_of_lt_of_le
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ)<2) _) coefficientLower
  have axesPositive : 1≤axes := by exact_mod_cast axesRealPositive
  have coefficientPositive : 1≤coefficientCount := by exact_mod_cast coefficientRealPositive
  exact runs_public precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
    precisionPositive axesPositive coefficientPositive activePositive outerPositive suffixPositive (by omega) (by omega)
    firstArray secondArray thirdArray

theorem public_descriptors (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (firstArray secondArray thirdArray : List Bool) (field : Fin 9) :
    let values := fields precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
    let resultBank := publicBank (alphabet:=alphabet)
      (layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
      firstArray secondArray thirdArray (fun index => some (values index))
    resultBank.head (Fin.natAdd 6 field)=1 ∧
      resultBank.tape (Fin.natAdd 6 field)=BinaryDescriptorStack.descriptor (GammaHeaderRead.bits (values field)) ∧
      Counter.value (GammaHeaderRead.bits (values field))=values field := by
  refine ⟨?_,?_,descriptor_value _⟩ <;>
    simp [publicBank,Tapes.append,descriptorHead,descriptorTape]

def constant (parameters : Spec.SignedRingProduct.LayerParams) : ℝ := 5*parameters.Cdesc+263

theorem runtime_le_layer_cost (parameters : Spec.SignedRingProduct.LayerParams)
    (parametersValid : parameters.Valid)
    (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (precisionPositive : 1≤precision)
    (admissible : Spec.SignedRingProduct.LayerAdmissible parameters precision axes coefficientCount activeCount
      outerCount suffixCount chunkWidth selectedBit wordWidth) :
    ((5*(layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth).length+263 : ℕ) : ℝ)≤
      constant parameters*Spec.SignedRingProduct.layerCost parameters axes coefficientCount
        (outerCount*suffixCount*2^(chunkWidth*activeCount)) wordWidth := by
  rcases parametersValid with ⟨_,_,_,exponentPositive,_,_,_,_,_,_,lowerAxesPositive,_,_,_,_,descriptorPositive,_⟩
  rcases admissible with ⟨axesLower,_,coefficientLower,_,_,_,_,outerPositive,suffixPositive,_,_,headerUpper,wordLower,_⟩
  have precisionRealPositive : (0 : ℝ)<precision := by exact_mod_cast precisionPositive
  have axesRealPositive : (0 : ℝ)<axes := lt_of_lt_of_le
    (mul_pos lowerAxesPositive (Real.rpow_pos_of_pos precisionRealPositive _)) axesLower
  have axesPositive : 1≤axes := by exact_mod_cast axesRealPositive
  have coefficientRealPositive : (0 : ℝ)<coefficientCount := lt_of_lt_of_le
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ)<2) _) coefficientLower
  have coefficientPositive : 0<coefficientCount := by exact_mod_cast coefficientRealPositive
  have multiplicityPositive : 0<outerCount*suffixCount*2^(chunkWidth*activeCount) :=
    Nat.mul_pos (Nat.mul_pos outerPositive suffixPositive) (pow_pos (by decide) _)
  have volumeNatural := Nat.le_mul_of_pos_left wordWidth
    (Nat.mul_pos (Nat.mul_pos (by decide : 0<2) multiplicityPositive) coefficientPositive)
  let volume := 2*(outerCount*suffixCount*2^(chunkWidth*activeCount))*coefficientCount*wordWidth
  have volumeBound : (wordWidth : ℝ)≤volume := by exact_mod_cast volumeNatural
  have precisionWidth : (precision : ℝ)≤wordWidth := by exact_mod_cast (by omega : precision≤wordWidth)
  have wordPositive : (1 : ℝ)≤wordWidth := by exact_mod_cast (by omega : 1≤wordWidth)
  have powerBound := Real.one_le_rpow (by exact_mod_cast axesPositive : (1 : ℝ)≤axes)
    (by exact_mod_cast le_of_lt exponentPositive : (0 : ℝ)≤(parameters.lam' : ℝ))
  have descriptorBound := mul_le_mul_of_nonneg_left precisionWidth (le_of_lt descriptorPositive)
  have coefficientNonnegative : 0≤constant parameters := by unfold constant; positivity
  have setupBound :
      ((5*(layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth).length+263 : ℕ) : ℝ)≤
        constant parameters*(wordWidth : ℝ) := by
    unfold constant
    push_cast
    nlinarith only [headerUpper,descriptorBound,wordPositive]
  have linearBound := setupBound.trans (mul_le_mul_of_nonneg_left volumeBound coefficientNonnegative)
  have poweredBound := mul_le_mul_of_nonneg_left powerBound
    (mul_nonneg coefficientNonnegative (Nat.cast_nonneg volume))
  simp only [mul_one] at poweredBound
  have finalBound := linearBound.trans poweredBound
  simpa only [constant,Spec.SignedRingProduct.layerCost,volume,mul_assoc] using finalBound

end
end IntegerMultBounds.Machine.LayerHeaderRead
