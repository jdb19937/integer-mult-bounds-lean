module

public import IntegerMultBounds.Machine.NativeSignExtendArray
public import IntegerMultBounds.Machine.LayerPreparedInput

@[expose] public section
namespace IntegerMultBounds.Machine.LayerNativeWidening
noncomputable section
open SharedPlacementAlphabet (setTape)
open RecoverWorkspace (atProgram erased restored)
open RecursiveChildQuotientsConstant (bits)
open NativeSignExtendArray (native widened word)

def rulerMap : Fin 3 → Fin 70 := ![64,65,66]
theorem rulerMap_injective : Function.Injective rulerMap := by decide
def rulerSlots := InjectivePlacement.placement rulerMap rulerMap_injective (by decide : 3+67=70)
def arrayMap : Fin 5 → Fin 70 := ![64,63,69,67,68]
theorem arrayMap_injective : Function.Injective arrayMap := by decide
def arraySlots := InjectivePlacement.placement arrayMap arrayMap_injective (by decide : 5+65=70)

def program := seq (seq (seq (seq (seq (BinaryDescriptorInstall.program 2 (30 : Fin 70) 66 (by decide))
  (Placement.placed (RecoverBinaryRuler.program (alphabet := 2)) rulerSlots))
  (Placement.placed NativeSignExtendArray.program arraySlots))
  (atProgram RecoverArrayCleanup.eraseOrigin (64 : Fin 70)))
  (atProgram ReturnOrigin.program (63 : Fin 70))) (atProgram ReturnOrigin.program (69 : Fin 70))

def cost (fields : List (List (Fin 2))) (targetWidth : ℕ) :=
  10*targetWidth+11*(bits targetWidth).length+NativeSignExtendArray.cost fields targetWidth+
    (native fields).length+(widened fields targetWidth).length+48

theorem native_nonblank (fields : List (List (Fin 2))) : ∀ symbol ∈ native fields, symbol ≠ (blank : Fin 6) := by
  intro symbol member
  obtain ⟨field, _, fieldMember⟩ := List.mem_flatMap.mp member
  rcases List.mem_append.mp fieldMember with digitMember | separatorMember
  · exact NativeSignExtendField.digits_nonblank field symbol digitMember
  · obtain rfl := List.mem_singleton.mp separatorMember
    decide

theorem runs (caller : Tapes 70 2) (fields : List (List (Fin 2))) (targetWidth : ℕ)
    (fieldFits : ∀ field ∈ fields, field.length ≤ targetWidth)
    (widthReady : caller.tape 30 = RadixZeroFill.encodedBinary (bits targetWidth)) (widthHead : caller.head 30 = 1)
    (sourceReady : caller.tape 63 = word (native fields)) (sourceHead : caller.head 63 = 0)
    (workBlank : ∀ slot : Fin 70, 64 ≤ slot.val → caller.head slot = 0 ∧ caller.tape slot = (fun _ => blank)) :
    HoareTime program (· = caller) (· = setTape caller (69 : Fin 70) (word (widened fields targetWidth)) 0)
      (cost fields targetWidth) := by
  let copied := setTape caller (66 : Fin 70) (RadixZeroFill.encodedBinary (bits targetWidth)) 1
  let ruled := setTape caller (64 : Fin 70) (RecoverCarryStep.word (List.replicate targetWidth true)) 0
  let converted := setTape (setTape ruled (63 : Fin 70) (caller.tape 63) (native fields).length)
    (69 : Fin 70) (word (widened fields targetWidth)) (widened fields targetWidth).length
  let rulerCleared := erased converted (64 : Fin 70)
  let sourceReturned := restored rulerCleared (63 : Fin 70)
  let nativeReturned := restored sourceReturned (69 : Fin 70)
  have rulerBlank := workBlank 64 (by decide)
  have clockBlank := workBlank 65 (by decide)
  have descriptorBlank := workBlank 66 (by decide)
  have copyRun := BinaryDescriptorInstall.install_hoare (30 : Fin 70) 66 (by decide) caller (bits targetWidth)
    widthReady widthHead descriptorBlank.2 descriptorBlank.1
  have rulerReady : Placement.active rulerSlots copied = RecoverBinaryRuler.input (bits targetWidth) := by
    rw [rulerSlots, InjectivePlacement.active_bank, RecoverBinaryRuler.input, CountedGuardConstantsFill.input,
      CountedGuardGadgetPosition.input, ←GammaDescriptorRead.controller_descriptor]
    unfold rulerMap copied setTape
    apply congrArg₂ Tapes.mk
    all_goals funext slot; fin_cases slot <;> simp [rulerBlank, clockBlank]
    exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm
  have rulerEndpoint : Placement.replace rulerSlots copied (RecoverBinaryRuler.output targetWidth) = ruled := by
    apply InjectivePlacement.replace_eq rulerMap rulerMap_injective (by decide : 3+67=70) copied ruled
    · rw [InjectivePlacement.active_bank]
      unfold rulerMap ruled RecoverBinaryRuler.output setTape
      apply congrArg₂ Tapes.mk
      all_goals funext slot; fin_cases slot <;> simp [clockBlank, descriptorBlank]
    · intro slot outside
      have notRuler : slot ≠ 64 := by intro equal; exact outside 0 (by simpa [rulerMap] using equal.symm)
      have notDescriptor : slot ≠ 66 := by intro equal; exact outside 2 (by simpa [rulerMap] using equal.symm)
      simp [ruled, copied, setTape, notRuler, notDescriptor]
  have rulerRun := Placement.hoare_at (RecoverBinaryRuler.runs_build (alphabet := 2) (bits targetWidth) targetWidth
    (RecursiveChildQuotientsConstant.bits_value _)) rulerSlots copied rulerReady
  have rulerExact : HoareTime (Placement.placed (RecoverBinaryRuler.program (alphabet := 2)) rulerSlots)
      (· = copied) (· = ruled) (8*targetWidth+9*(bits targetWidth).length+31) := by
    apply rulerRun.consequence (fun _ ready => ready) _ le_rfl
    rintro bank ⟨localBank, rfl, ready⟩
    exact ready.trans rulerEndpoint
  have arrayReady : Placement.active arraySlots ruled = NativeSignExtendArray.bank
      (RecoverCarryStep.word (List.replicate targetWidth true)) (word ([]++native fields)) (fun _ => blank) 0 0 := by
    rw [arraySlots, InjectivePlacement.active_bank]
    unfold arrayMap ruled setTape NativeSignExtendArray.bank
    apply congrArg₂ Tapes.mk
    all_goals funext slot; fin_cases slot <;> simp [sourceReady, sourceHead, workBlank 67 (by decide),
      workBlank 68 (by decide), workBlank 69 (by decide)]
  have arrayEndpoint : Placement.replace arraySlots ruled (NativeSignExtendArray.bank
      (RecoverCarryStep.word (List.replicate targetWidth true)) (word ([]++native fields))
      (putWord (fun _ => blank) 0 (widened fields targetWidth)) ([]++native fields).length
      (0+(widened fields targetWidth).length)) = converted := by
    apply InjectivePlacement.replace_eq arrayMap arrayMap_injective (by decide : 5+65=70) ruled converted
    · rw [InjectivePlacement.active_bank]
      unfold arrayMap converted ruled setTape NativeSignExtendArray.bank
      apply congrArg₂ Tapes.mk
      all_goals funext slot; fin_cases slot <;> simp [sourceReady, workBlank 67 (by decide), workBlank 68 (by decide), word]
    · intro slot outside
      have notSource : slot ≠ 63 := by intro equal; exact outside 1 (by simpa [arrayMap] using equal.symm)
      have notDestination : slot ≠ 69 := by intro equal; exact outside 2 (by simpa [arrayMap] using equal.symm)
      simp [converted, setTape, notSource, notDestination]
  have arrayRun := Placement.hoare_at (NativeSignExtendArray.runs fields targetWidth [] (fun _ => blank) 0 fieldFits)
    arraySlots ruled arrayReady
  have arrayExact : HoareTime (Placement.placed NativeSignExtendArray.program arraySlots)
      (· = ruled) (· = converted) (NativeSignExtendArray.cost fields targetWidth) := by
    apply arrayRun.consequence (fun _ ready => ready) _ le_rfl
    rintro bank ⟨localBank, rfl, ready⟩
    exact ready.trans arrayEndpoint
  have clearRuler := RecoverArrayCleanup.erase_origin_at (64 : Fin 70) converted
    ((List.replicate targetWidth true).map bitSymbol)
    (by intro symbol member; obtain ⟨bit, _, rfl⟩ := List.mem_map.mp member
        cases bit <;> simp [bitSymbol, blank, Fin.ext_iff])
    (by simp [converted, ruled, setTape]) (by simp [converted, ruled, setTape, RecoverCarryStep.word])
  have returnSource := RecoverWorkspace.return_at (63 : Fin 70) rulerCleared (native fields) (native_nonblank fields)
    (by simp [rulerCleared, erased, converted, setTape])
    (by simp [rulerCleared, erased, converted, setTape, sourceReady, word])
  have returnNative := RecoverWorkspace.return_at (69 : Fin 70) sourceReturned (widened fields targetWidth)
    (native_nonblank _) (by simp [sourceReturned, restored, rulerCleared, erased, converted, setTape])
    (by simp [sourceReturned, restored, rulerCleared, erased, converted, setTape, word])
  have endpoint : nativeReturned = setTape caller (69 : Fin 70) (word (widened fields targetWidth)) 0 := by
    apply Placement.Tapes.ext'
    all_goals
      intro slot
      by_cases isRuler : slot = 64
      · subst slot
        simp [nativeReturned, sourceReturned, restored, rulerCleared, erased, converted, ruled, setTape, rulerBlank]
      · by_cases isSource : slot = 63
        · subst slot
          simp [nativeReturned, sourceReturned, restored, rulerCleared, erased, converted, ruled, setTape, sourceHead]
        · by_cases isDestination : slot = 69
          · subst slot
            simp [nativeReturned, sourceReturned, restored, rulerCleared, erased, converted, ruled, setTape]
          · simp [nativeReturned, sourceReturned, restored, rulerCleared, erased, converted, ruled, setTape,
              isRuler, isSource, isDestination]
  unfold program
  apply (((((copyRun.seq rulerExact).seq arrayExact).seq clearRuler).seq returnSource).seq returnNative).consequence
    (fun _ ready => ready) (fun _ ready => ready.trans endpoint) ?_
  simp only [List.length_map, List.length_replicate]
  unfold cost
  omega

end
end IntegerMultBounds.Machine.LayerNativeWidening
