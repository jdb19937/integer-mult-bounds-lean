module

public import IntegerMultBounds.Machine.LayerPolynomialPaddingData

@[expose] public section
namespace IntegerMultBounds.Machine.LayerPaddedInput
noncomputable section
open Spec.SignedRingProduct (Rec array layerHeader)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {coefficientCount : ℕ}

def headerMap (index : Fin 43) : Fin 75 := if index=22 then 74 else ⟨17+index.val, by omega⟩
theorem headerMap_injective : Function.Injective headerMap := by
  intro left right equal
  apply Fin.ext
  have leftBound := left.isLt
  have rightBound := right.isLt
  have values := congrArg Fin.val equal
  by_cases leftFlag : left=22 <;> by_cases rightFlag : right=22
  all_goals simp [headerMap, leftFlag, rightFlag] at values
  all_goals simp_all only [Fin.ext_iff]
  all_goals omega
def headerSlots := InjectivePlacement.placement headerMap headerMap_injective (by decide : 43+32=75)
def construct := Placement.placed (LayerPolynomialPaddingHeaders.core (alphabet := 2)) headerSlots
def paddingMap : Fin 9 → Fin 75 := ![69,74,42,30,43,70,71,72,73]
theorem paddingMap_injective : Function.Injective paddingMap := by decide
def paddingSlots := InjectivePlacement.placement paddingMap paddingMap_injective (by decide : 9+66=75)
def pad := Placement.placed NativePolynomialPadding.program paddingSlots
def program (roleCount arity : ℕ) := seq (seq (extend (LayerGuardedInput.program roleCount arity) 5) construct) pad

def originalState (roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ) :=
  LayerPolynomialHeaders.state (LayerReservationHeaders.finished roleCount arity precision axes coefficientCount activeCount
    outerCount suffixCount chunkWidth selectedBit wordWidth) coefficientCount
def nativeWidth (activeCount chunkWidth wordWidth : ℕ) := LayerReservationHeaders.nativeWidth activeCount chunkWidth wordWidth
def prepared (roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (polynomials : List (Rec coefficientCount)) (secondArray thirdArray : List Bool) :=
  (LayerGuardedInput.output roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
    polynomials secondArray thirdArray).append (SharedBank.empty 5 2)
def headers (roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (polynomials : List (Rec coefficientCount)) (secondArray thirdArray : List Bool) :=
  Placement.replace headerSlots (prepared roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit
    wordWidth polynomials secondArray thirdArray)
    (ActiveRepairRankHeadersCommands.bank (a := 2) (LayerPolynomialPaddingHeaders.output
      (originalState (coefficientCount := coefficientCount) roleCount arity precision axes activeCount outerCount suffixCount
        chunkWidth selectedBit wordWidth) coefficientCount (nativeWidth activeCount chunkWidth wordWidth)))
def paddedWord (wordWidth activeCount chunkWidth : ℕ) (polynomials : List (Rec coefficientCount)) :=
  (NativePolynomialPadding.padded (LayerPolynomialPaddingData.groups wordWidth (nativeWidth activeCount chunkWidth wordWidth) polynomials)
    (nativeWidth activeCount chunkWidth wordWidth) (LayerPolynomialPaddingHeaders.deficit coefficientCount)).flatten
def output (roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (polynomials : List (Rec coefficientCount)) (secondArray thirdArray : List Bool) :=
  setTape (headers roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
    polynomials secondArray thirdArray) (74 : Fin 75) (NativePolynomialPadding.word (paddedWord wordWidth activeCount chunkWidth polynomials)) 0

def paddingCost (wordWidth activeCount chunkWidth : ℕ) (polynomials : List (Rec coefficientCount)) :=
  let width := nativeWidth activeCount chunkWidth wordWidth
  let span := LayerPolynomialPaddingHeaders.span coefficientCount width
  let deficit := LayerPolynomialPaddingHeaders.deficit coefficientCount
  let groups := LayerPolynomialPaddingData.groups wordWidth width polynomials
  (NativePolynomialPadding.blockCost span width deficit+2)*groups.length+groups.flatten.length+
    (NativePolynomialPadding.padded groups width deficit).flatten.length+6
def cost (roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (polynomials : List (Rec coefficientCount)) :=
  LayerGuardedInput.cost roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth polynomials+1+
    CompactGlobalRowHeaderOps.scheduleCost LayerPolynomialPaddingHeaders.schedule
      (originalState (coefficientCount := coefficientCount) roleCount arity precision axes activeCount outerCount suffixCount
        chunkWidth selectedBit wordWidth)+1+paddingCost wordWidth activeCount chunkWidth polynomials

theorem headerMap_other (slot : Fin 75) (outside : 60 ≤ slot.val) (notPrivateFlag : slot ≠ 74) :
    ∀ index, headerMap index ≠ slot := by
  intro index equal
  by_cases flagSlot : index=22
  · simp only [headerMap, flagSlot, ite_true] at equal
    exact notPrivateFlag equal.symm
  · have values := congrArg Fin.val equal
    simp only [headerMap, flagSlot, ite_false] at values
    have indexBound := index.isLt
    omega

theorem prepared_active (roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (polynomials : List (Rec coefficientCount)) (secondArray thirdArray : List Bool) :
    Placement.active headerSlots (prepared roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
      polynomials secondArray thirdArray) = ActiveRepairRankHeadersCommands.bank (a := 2)
        (originalState (coefficientCount := coefficientCount) roleCount arity precision axes activeCount outerCount suffixCount chunkWidth
          selectedBit wordWidth) := by
  rw [headerSlots, InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk
  all_goals funext index; fin_cases index <;> rfl

theorem ready_for_padding (caller : Tapes 75 2) (original : ActiveRepairRankHeadersCommands.State)
    (count width : ℕ) (groups : List (List (Fin 6)))
    (sourceHead : caller.head 69 = 0) (sourceTape : caller.tape 69 = NativePolynomialPadding.word groups.flatten)
    (widthReady : original 13 = some width) (flagBlank : original 22 = none)
    (workBlank : ∀ slot : Fin 5, caller.head (Fin.natAdd 70 slot) = 0 ∧ caller.tape (Fin.natAdd 70 slot) = (fun _ => blank)) :
    Placement.active paddingSlots (Placement.replace headerSlots caller
      (ActiveRepairRankHeadersCommands.bank (a := 2) (LayerPolynomialPaddingHeaders.output original count width))) =
        NativePolynomialPadding.bank (NativePolynomialPadding.word groups.flatten) (fun _ => blank) 0 0
          (LayerPolynomialPaddingHeaders.span count width) width (LayerPolynomialPaddingHeaders.deficit count) := by
  let generated := ActiveRepairRankHeadersCommands.bank (a := 2) (LayerPolynomialPaddingHeaders.output original count width)
  let headerBank := Placement.replace headerSlots caller generated
  have headerHeads : ∀ index : Fin 43, headerBank.head (headerMap index) = generated.head index := by
    intro index
    exact InjectivePlacement.replace_head_slot headerMap headerMap_injective (by decide : 43+32=75) caller generated index
  have headerTapes : ∀ index : Fin 43, headerBank.tape (headerMap index) = generated.tape index := by
    intro index
    exact InjectivePlacement.replace_tape_slot headerMap headerMap_injective (by decide : 43+32=75) caller generated index
  have sourceHeadReady : headerBank.head 69 = 0 := by
    dsimp only [headerBank]
    rw [headerSlots, InjectivePlacement.replace_head_other _ _ _ _ _ _ (headerMap_other 69 (by decide) (by decide))]
    exact sourceHead
  have sourceTapeReady : headerBank.tape 69 = NativePolynomialPadding.word groups.flatten := by
    dsimp only [headerBank]
    rw [headerSlots, InjectivePlacement.replace_tape_other _ _ _ _ _ _ (headerMap_other 69 (by decide) (by decide))]
    exact sourceTape
  have workHeads : ∀ index : Fin 4, headerBank.head (⟨70+index.val, by omega⟩ : Fin 75) = 0 := by
    intro index
    dsimp only [headerBank]
    rw [headerSlots, InjectivePlacement.replace_head_other _ _ _ _ _ _
      (headerMap_other _ (by change 60 ≤ 70+index.val; omega)
        (by intro equal; have values := congrArg Fin.val equal; change 70+index.val=74 at values; omega))]
    exact (workBlank (Fin.castSucc index)).1
  have workTapes : ∀ index : Fin 4, headerBank.tape (⟨70+index.val, by omega⟩ : Fin 75) = (fun _ => blank) := by
    intro index
    dsimp only [headerBank]
    rw [headerSlots, InjectivePlacement.replace_tape_other _ _ _ _ _ _
      (headerMap_other _ (by change 60 ≤ 70+index.val; omega)
        (by intro equal; have values := congrArg Fin.val equal; change 70+index.val=74 at values; omega))]
    exact (workBlank (Fin.castSucc index)).2
  have generatedFlag : generated.head 22 = 0 ∧ generated.tape 22 = (fun _ => blank) := by
    change (ActiveRepairRankHeadersCommands.caller (a := 2) (LayerPolynomialPaddingHeaders.output original count width)).head 22 = 0 ∧
      (ActiveRepairRankHeadersCommands.caller (a := 2) (LayerPolynomialPaddingHeaders.output original count width)).tape 22 = _
    simp [LayerPolynomialPaddingHeaders.output, ActiveRepairRankHeadersCommands.caller,
      ActiveRepairRankHeadersCommands.put, flagBlank]
  have generatedSpan : generated.head 25 = 1 ∧ generated.tape 25 =
      RadixZeroFill.encodedBinary (bits (LayerPolynomialPaddingHeaders.span count width)) := by
    change (ActiveRepairRankHeadersCommands.caller (a := 2) (LayerPolynomialPaddingHeaders.output original count width)).head 25 = 1 ∧
      (ActiveRepairRankHeadersCommands.caller (a := 2) (LayerPolynomialPaddingHeaders.output original count width)).tape 25 = _
    simp [LayerPolynomialPaddingHeaders.output, ActiveRepairRankHeadersCommands.caller, ActiveRepairRankHeadersCommands.put]
  have generatedWidth : generated.head 13 = 1 ∧ generated.tape 13 = RadixZeroFill.encodedBinary (bits width) := by
    change (ActiveRepairRankHeadersCommands.caller (a := 2) (LayerPolynomialPaddingHeaders.output original count width)).head 13 = 1 ∧
      (ActiveRepairRankHeadersCommands.caller (a := 2) (LayerPolynomialPaddingHeaders.output original count width)).tape 13 = _
    simp [LayerPolynomialPaddingHeaders.output, ActiveRepairRankHeadersCommands.caller,
      ActiveRepairRankHeadersCommands.put, widthReady]
  have generatedDeficit : generated.head 26 = 1 ∧ generated.tape 26 =
      RadixZeroFill.encodedBinary (bits (LayerPolynomialPaddingHeaders.deficit count)) := by
    change (ActiveRepairRankHeadersCommands.caller (a := 2) (LayerPolynomialPaddingHeaders.output original count width)).head 26 = 1 ∧
      (ActiveRepairRankHeadersCommands.caller (a := 2) (LayerPolynomialPaddingHeaders.output original count width)).tape 26 = _
    simp [LayerPolynomialPaddingHeaders.output, ActiveRepairRankHeadersCommands.caller, ActiveRepairRankHeadersCommands.put]
  change Placement.active paddingSlots headerBank = _
  rw [paddingSlots, InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk
  all_goals
    funext index
    fin_cases index
    all_goals first
      | exact sourceHeadReady | exact sourceTapeReady
      | exact workHeads 0 | exact workHeads 1 | exact workHeads 2 | exact workHeads 3
      | exact workTapes 0 | exact workTapes 1 | exact workTapes 2 | exact workTapes 3
      | exact (headerHeads 22).trans generatedFlag.1 | exact (headerTapes 22).trans generatedFlag.2
      | exact (headerHeads 25).trans generatedSpan.1 | exact (headerTapes 25).trans generatedSpan.2
      | exact (headerHeads 13).trans generatedWidth.1 | exact (headerTapes 13).trans generatedWidth.2
      | exact (headerHeads 26).trans generatedDeficit.1 | exact (headerTapes 26).trans generatedDeficit.2

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
  have publicRun := hoare_extend_eq
    (LayerGuardedInput.runs_public parameters parametersValid roleCount arity rolesPositive arityPositive precision axes activeCount
      outerCount suffixCount chunkWidth selectedBit wordWidth precisionPositive admissible polynomials secondArray thirdArray)
    (SharedBank.empty 5 2)
  have publicInput : (Spec.SignedRingProduct.bank (t := 70) (a := 2)
      (layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
      (array wordWidth polynomials) secondArray thirdArray).append (SharedBank.empty 5 2) =
      Spec.SignedRingProduct.bank (t := 75)
        (layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
        (array wordWidth polynomials) secondArray thirdArray := by
    apply Placement.Tapes.ext'
    all_goals intro slot; fin_cases slot <;> rfl
  rw [publicInput] at publicRun
  let original := originalState (coefficientCount := coefficientCount) roleCount arity precision axes activeCount outerCount suffixCount
    chunkWidth selectedBit wordWidth
  let width := nativeWidth activeCount chunkWidth wordWidth
  let caller := prepared roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
    polynomials secondArray thirdArray
  let generated := ActiveRepairRankHeadersCommands.bank (a := 2) (LayerPolynomialPaddingHeaders.output original coefficientCount width)
  let headerBank := headers roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
    polynomials secondArray thirdArray
  have coefficientRealPositive : (0 : ℝ) < coefficientCount :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _) admissible.2.2.1
  have countPositive : 0 < coefficientCount := by exact_mod_cast coefficientRealPositive
  have activeReady : Placement.active headerSlots caller = ActiveRepairRankHeadersCommands.bank (a := 2) original := by
    exact prepared_active roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
      polynomials secondArray thirdArray
  have coreRun := LayerPolynomialPaddingHeaders.runs (alphabet := 2) original coefficientCount width countPositive
    rfl rfl rfl rfl rfl rfl
  have constructRun := Placement.hoare_at coreRun headerSlots caller activeReady
  have constructExact : HoareTime construct (· = caller) (· = headerBank)
      (CompactGlobalRowHeaderOps.scheduleCost LayerPolynomialPaddingHeaders.schedule original) := by
    apply constructRun.consequence (fun _ ready => ready) _ le_rfl
    rintro current ⟨localBank, rfl, ready⟩
    exact ready
  have sourceHead : caller.head 69 = 0 := rfl
  have sourceTape : caller.tape 69 = NativePolynomialPadding.word
      (LayerPolynomialPaddingData.groups wordWidth width polynomials).flatten := by
    rw [LayerPolynomialPaddingData.groups_widened]
    exact (LayerGuardedInput.native_output roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
      polynomials secondArray thirdArray).2
  have paddingReady : Placement.active paddingSlots headerBank = NativePolynomialPadding.bank
      (NativePolynomialPadding.word (LayerPolynomialPaddingData.groups wordWidth width polynomials).flatten)
      (fun _ => blank) 0 0 (LayerPolynomialPaddingHeaders.span coefficientCount width) width
      (LayerPolynomialPaddingHeaders.deficit coefficientCount) := by
    apply ready_for_padding caller original coefficientCount width _ sourceHead sourceTape rfl rfl
    intro slot
    simp only [caller, prepared, Tapes.append, Fin.addCases_right, SharedBank.empty, and_self]
  have widthFits : wordWidth ≤ width := by unfold width nativeWidth LayerReservationHeaders.nativeWidth; omega
  have groupLengths : ∀ group ∈ LayerPolynomialPaddingData.groups wordWidth width polynomials,
      group.length = LayerPolynomialPaddingHeaders.span coefficientCount width := by
    intro group member
    obtain ⟨polynomial, _, rfl⟩ := List.mem_map.mp member
    exact LayerPolynomialPaddingData.group_length wordWidth width polynomial widthFits
  have spanPositive : 0 < LayerPolynomialPaddingHeaders.span coefficientCount width := by
    unfold LayerPolynomialPaddingHeaders.span
    positivity
  have paddingRun := Placement.hoare_at (NativePolynomialPadding.runs
    (LayerPolynomialPaddingData.groups wordWidth width polynomials) _ width _ spanPositive groupLengths
    (LayerPolynomialPaddingData.groups_nonblank wordWidth width polynomials)) paddingSlots headerBank paddingReady
  have paddingEndpoint : Placement.replace paddingSlots headerBank (NativePolynomialPadding.bank
      (NativePolynomialPadding.word (LayerPolynomialPaddingData.groups wordWidth width polynomials).flatten)
      (NativePolynomialPadding.word (paddedWord wordWidth activeCount chunkWidth polynomials)) 0 0
      (LayerPolynomialPaddingHeaders.span coefficientCount width) width (LayerPolynomialPaddingHeaders.deficit coefficientCount)) =
      output roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
        polynomials secondArray thirdArray := by
    have localUpdated : NativePolynomialPadding.bank
        (NativePolynomialPadding.word (LayerPolynomialPaddingData.groups wordWidth width polynomials).flatten)
        (NativePolynomialPadding.word (paddedWord wordWidth activeCount chunkWidth polynomials)) 0 0
        (LayerPolynomialPaddingHeaders.span coefficientCount width) width (LayerPolynomialPaddingHeaders.deficit coefficientCount) =
        setTape (Placement.active paddingSlots headerBank) (1 : Fin 9)
          (NativePolynomialPadding.word (paddedWord wordWidth activeCount chunkWidth polynomials)) 0 := by
      rw [paddingReady]
      unfold setTape NativePolynomialPadding.bank
      apply congrArg₂ Tapes.mk
      all_goals funext index; fin_cases index <;> rfl
    rw [localUpdated]
    exact InjectivePlacement.replace_set paddingMap paddingMap_injective (by decide : 9+66=75) headerBank (1 : Fin 9) _ 0
  have paddingExact : HoareTime pad (· = headerBank)
      (· = output roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
        polynomials secondArray thirdArray) (paddingCost wordWidth activeCount chunkWidth polynomials) := by
    apply paddingRun.consequence (fun _ ready => ready) _ le_rfl
    rintro current ⟨localBank, rfl, ready⟩
    exact ready.trans paddingEndpoint
  unfold program cost
  exact (publicRun.seq constructExact).seq paddingExact

theorem native_output (roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (polynomials : List (Rec coefficientCount)) (secondArray thirdArray : List Bool) :
    (output roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
      polynomials secondArray thirdArray).head 74 = 0 ∧
    (output roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
      polynomials secondArray thirdArray).tape 74 = NativePolynomialPadding.word (paddedWord wordWidth activeCount chunkWidth polynomials) := by
  simp only [output, setTape, Function.update_self, and_self]

theorem workspace_blank (roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (polynomials : List (Rec coefficientCount)) (secondArray thirdArray : List Bool) (slot : Fin 4) :
    (output roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
      polynomials secondArray thirdArray).head (Fin.natAdd 70 (Fin.castSucc slot)) = 0 ∧
    (output roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
      polynomials secondArray thirdArray).tape (Fin.natAdd 70 (Fin.castSucc slot)) = (fun _ => blank) := by
  have notDestination : Fin.natAdd 70 (Fin.castSucc slot) ≠ (74 : Fin 75) := by
    intro equal
    have values := congrArg Fin.val equal
    change 70+slot.val=74 at values
    omega
  have outside := headerMap_other (Fin.natAdd 70 (Fin.castSucc slot)) (by change 60 ≤ 70+slot.val; omega) notDestination
  constructor
  · simp only [output, setTape, Function.update_of_ne notDestination]
    unfold headers
    rw [headerSlots, InjectivePlacement.replace_head_other _ _ _ _ _ _ outside]
    simp only [prepared, Tapes.append, Fin.addCases_right, SharedBank.empty]
  · simp only [output, setTape, Function.update_of_ne notDestination]
    unfold headers
    rw [headerSlots, InjectivePlacement.replace_tape_other _ _ _ _ _ _ outside]
    simp only [prepared, Tapes.append, Fin.addCases_right, SharedBank.empty]

theorem headerMap_not_flag : ∀ index, headerMap index ≠ (39 : Fin 75) := by
  intro index equal
  by_cases flagSlot : index=22
  · simp [headerMap, flagSlot] at equal
  · have values := congrArg Fin.val equal
    simp only [headerMap, flagSlot, ite_false] at values
    change 17+index.val=39 at values
    apply flagSlot
    apply Fin.ext
    change index.val=22
    omega

theorem nonfallback_flag (roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (polynomials : List (Rec coefficientCount)) (secondArray thirdArray : List Bool) :
    (output roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
      polynomials secondArray thirdArray).tape 39 0 =
      bitSymbol (decide (LayerReservationHeaders.reservationAxes roleCount arity precision axes chunkWidth < activeCount)) := by
  simp only [output, setTape, Function.update_of_ne (by decide : (39 : Fin 75) ≠ 74)]
  unfold headers
  rw [headerSlots, InjectivePlacement.replace_tape_other _ _ _ _ _ _ headerMap_not_flag]
  exact LayerGuardedInput.nonfallback_flag roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit
    wordWidth polynomials secondArray thirdArray

theorem padding_cost_linear (wordWidth activeCount chunkWidth : ℕ) (polynomials : List (Rec coefficientCount))
    (countPositive : 0 < coefficientCount) :
    paddingCost wordWidth activeCount chunkWidth polynomials ≤
      131*(LayerPolynomialPaddingData.groups wordWidth (nativeWidth activeCount chunkWidth wordWidth) polynomials).flatten.length+6 := by
  let width := nativeWidth activeCount chunkWidth wordWidth
  have widthFits : wordWidth ≤ width := by unfold width nativeWidth LayerReservationHeaders.nativeWidth; omega
  have blockBound := LayerPolynomialPaddingData.padding_cost_linear coefficientCount width countPositive
  have countBound := Nat.mul_le_mul_right polynomials.length blockBound
  have sourceLength := LayerPolynomialPaddingData.groups_length wordWidth width polynomials widthFits
  have paddedLength := LayerPolynomialPaddingData.padded_groups_volume wordWidth width polynomials widthFits countPositive
  unfold paddingCost
  simp only [LayerPolynomialPaddingData.groups, List.length_map] at countBound sourceLength paddedLength ⊢
  nlinarith

end
end IntegerMultBounds.Machine.LayerPaddedInput
