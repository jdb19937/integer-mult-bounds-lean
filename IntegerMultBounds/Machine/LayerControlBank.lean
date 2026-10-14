module

public import IntegerMultBounds.Machine.LayerSelectedBitSetup
public import IntegerMultBounds.Machine.FixedHeaderBankCopy
public import IntegerMultBounds.Machine.ActiveRepairRankHeadersCommands

@[expose] public section
namespace IntegerMultBounds.Machine.LayerControlBank
noncomputable section
variable {alphabet : ℕ}
open ActiveRepairRankHeadersCommands (State)
open RecursiveChildQuotientsConstant (bits)

def focus (slot : Fin 28) : Fin 17 :=
  if bounded : slot.val<9 then ⟨6+slot.val,by omega⟩ else 16

def values (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ) : Fin 28 → ℕ :=
  fun slot => if bounded : slot.val<9 then
    LayerHeaderRead.fields precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth ⟨slot.val,bounded⟩
    else selectedBit

def initial (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ) : State :=
  fun slot => if slot.val<10 then some (values precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth slot) else none

def operations : List (Fin 28) := [0,1,2,3,4,5,6,7,8,9]

def block (caller : Tapes 17 alphabet) (state : State) : Tapes 60 alphabet :=
  (caller.append (ActiveRepairRankHeadersCommands.caller state)).append (SharedBank.empty 15 alphabet)

def copyProgram := extend (FixedHeaderBankCopy.listProgram (a:=alphabet) (by decide : 0<17+28) focus operations) 15
def program := seq (extend (LayerSelectedBitSetup.program (alphabet:=alphabet)) 43) copyProgram

def copyCost (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ) :=
  FixedHeaderBankCopy.cost operations
    (fun slot => bits (values precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth slot))

theorem copies (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (caller : Tapes 17 alphabet)
    (sourceTapes : ∀ slot,caller.tape (focus slot)=RadixZeroFill.encodedBinary
      (bits (values precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth slot)))
    (sourceHeads : ∀ slot,caller.head (focus slot)=1) :
    HoareTime (copyProgram (alphabet:=alphabet))
      (· = block caller (fun _ => none))
      (· = block caller (initial precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth))
      (copyCost precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth) := by
  let sourceBits := fun slot => bits (values precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth slot)
  have copied := FixedHeaderBankCopy.list_constructs (a:=alphabet) (by decide : 0<17+28) focus sourceBits
    operations (by decide) caller sourceTapes sourceHeads (fun _ => none) (by intros; rfl)
  have filled : FixedHeaderBankCopy.filled sourceBits operations (fun _ => none)=
      (fun slot => (initial precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth slot).map bits) := by
    funext slot
    fin_cases slot <;> simp [FixedHeaderBankCopy.filled,operations,initial,sourceBits,Function.update]
  rw [filled] at copied
  have emptyBank : FixedHeaderBankCopy.bank (a:=alphabet) (fun _ : Fin 28 => none)=
      ActiveRepairRankHeadersCommands.caller (fun _ => none) := rfl
  have populatedBank : FixedHeaderBankCopy.bank (a:=alphabet)
      (fun slot => (initial precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth slot).map bits)=
      ActiveRepairRankHeadersCommands.caller (initial precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth) := by
    apply congrArg₂ Tapes.mk
    all_goals funext slot; fin_cases slot <;> rfl
  rw [emptyBank,populatedBank] at copied
  exact hoare_extend_eq copied (SharedBank.empty 15 alphabet)

theorem output_sources (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (firstArray secondArray thirdArray : List Bool) (slot : Fin 28) :
    let caller := LayerSelectedBitSetup.output (alphabet:=alphabet) precision axes coefficientCount activeCount outerCount suffixCount
      chunkWidth selectedBit wordWidth firstArray secondArray thirdArray
    caller.head (focus slot)=1 ∧ caller.tape (focus slot)=RadixZeroFill.encodedBinary
      (bits (values precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth slot)) := by
  by_cases small : slot.val<9
  · have ready := LayerSelectedBitSetup.output_native_fields (alphabet:=alphabet) precision axes coefficientCount activeCount outerCount
      suffixCount chunkWidth selectedBit wordWidth firstArray secondArray thirdArray ⟨slot.val,small⟩
    have indexEquation : (Fin.castAdd 2 (Fin.natAdd 6 (⟨slot.val,small⟩ : Fin 9)) : Fin 17)=⟨6+slot.val,by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_castAdd,Fin.val_natAdd]
    simpa only [focus,values,dite_eq_left small,indexEquation] using ready
  · have ready := LayerSelectedBitSetup.output_selected (alphabet:=alphabet) precision axes coefficientCount activeCount outerCount
      suffixCount chunkWidth selectedBit wordWidth firstArray secondArray thirdArray
    simpa only [focus,values,dite_eq_right small] using And.intro ready.1 ready.2.1

def output (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (firstArray secondArray thirdArray : List Bool) : Tapes 60 alphabet :=
  block (LayerSelectedBitSetup.output precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
    firstArray secondArray thirdArray)
    (initial precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)

theorem runs_public (parameters : Spec.SignedRingProduct.LayerParams) (parametersValid : parameters.Valid)
    (precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (precisionPositive : 1≤precision)
    (admissible : Spec.SignedRingProduct.LayerAdmissible parameters precision axes coefficientCount activeCount
      outerCount suffixCount chunkWidth selectedBit wordWidth)
    (firstArray secondArray thirdArray : List Bool) :
    HoareTime (program (alphabet:=alphabet))
      (· = Spec.SignedRingProduct.bank
        (Spec.SignedRingProduct.layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
        firstArray secondArray thirdArray)
      (· = output precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
        firstArray secondArray thirdArray)
      (11*(Spec.SignedRingProduct.layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth).length+
        309+copyCost precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth) := by
  let caller := LayerSelectedBitSetup.output (alphabet:=alphabet) precision axes coefficientCount activeCount outerCount suffixCount
    chunkWidth selectedBit wordWidth firstArray secondArray thirdArray
  have parsed := hoare_extend_eq
    (LayerSelectedBitSetup.runs_public (alphabet:=alphabet) parameters parametersValid precision axes coefficientCount activeCount
      outerCount suffixCount chunkWidth selectedBit wordWidth precisionPositive admissible firstArray secondArray thirdArray)
    (SharedBank.empty 43 alphabet)
  have initialized : caller.append (SharedBank.empty 43 alphabet)=block caller (fun _ => none) := by
    apply congrArg₂ Tapes.mk
    all_goals funext port; fin_cases port <;> rfl
  rw [initialized] at parsed
  have copied := copies precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth caller
    (fun slot => (output_sources _ _ _ _ _ _ _ _ _ firstArray secondArray thirdArray slot).2)
    (fun slot => (output_sources _ _ _ _ _ _ _ _ _ firstArray secondArray thirdArray slot).1)
  have originalBank : (Spec.SignedRingProduct.bank (t:=17) (a:=alphabet)
      (Spec.SignedRingProduct.layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
      firstArray secondArray thirdArray).append (SharedBank.empty 43 alphabet)=
      Spec.SignedRingProduct.bank (t:=60)
        (Spec.SignedRingProduct.layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
        firstArray secondArray thirdArray := by
    apply congrArg₂ Tapes.mk
    all_goals funext port; fin_cases port <;> rfl
  rw [originalBank] at parsed
  unfold program output
  exact (parsed.seq copied).consequence (fun _ equality => equality) (fun _ equality => equality) (by omega)

def nativePlacement : Fin (43+17) ≃ Fin 60 := finAddFlip

theorem native_bank (caller : Tapes 17 alphabet) (state : State) :
    ((ActiveRepairRankHeadersCommands.bank state).append caller).reindex nativePlacement=block caller state := by
  apply congrArg₂ Tapes.mk
  all_goals funext port; fin_cases port <;> rfl

end
end IntegerMultBounds.Machine.LayerControlBank
