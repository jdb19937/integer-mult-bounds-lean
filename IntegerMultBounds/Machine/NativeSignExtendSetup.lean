module

public import IntegerMultBounds.Machine.NativeSignExtend
public import IntegerMultBounds.Machine.LayerNativeRecords

@[expose] public section
namespace IntegerMultBounds.Machine.NativeSignExtendSetup
noncomputable section
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)

def rulerMap : Fin 3 → Fin 6 := ![1,2,3]
theorem rulerMap_injective : Function.Injective rulerMap := by decide
def rulerSlots := InjectivePlacement.placement rulerMap rulerMap_injective (by decide : 3+3=6)
def wideningMap : Fin 3 → Fin 6 := ![1,4,5]
theorem wideningMap_injective : Function.Injective wideningMap := by decide
def wideningSlots := InjectivePlacement.placement wideningMap wideningMap_injective (by decide : 3+3=6)

def program := seq (seq (BinaryDescriptorInstall.program 2 (0 : Fin 6) 3 (by decide))
  (Placement.placed (RecoverBinaryRuler.program (alphabet := 2)) rulerSlots))
  (Placement.placed NativeSignExtend.cleanProgram wideningSlots)

def cost (sourceWidth targetWidth : ℕ) := 17*targetWidth+sourceWidth+11*(bits targetWidth).length+59

theorem runs (caller : Tapes 6 2) (source : List (Fin 2)) (targetWidth : ℕ)
    (sourceFits : source.length ≤ targetWidth)
    (widthReady : caller.tape 0 = RadixZeroFill.encodedBinary (bits targetWidth))
    (widthHead : caller.head 0 = 1)
    (sourceReady : caller.tape 4 = NativeSignExtend.nativeTape source) (sourceHead : caller.head 4 = 0)
    (workBlank : ∀ slot : Fin 6, slot = 1 ∨ slot = 2 ∨ slot = 3 ∨ slot = 5 →
      caller.head slot = 0 ∧ caller.tape slot = (fun _ => blank)) :
    HoareTime program (· = caller)
      (· = setTape caller (5 : Fin 6) (NativeSignExtend.nativeTape (NativeSignExtend.extended source targetWidth)) 0)
      (cost source.length targetWidth) := by
  let copied := setTape caller (3 : Fin 6) (RadixZeroFill.encodedBinary (bits targetWidth)) 1
  let ruled := setTape caller (1 : Fin 6) (RecoverCarryStep.word (List.replicate targetWidth true)) 0
  let finished := setTape caller (5 : Fin 6) (NativeSignExtend.nativeTape (NativeSignExtend.extended source targetWidth)) 0
  have rulerBlank := workBlank 1 (by simp)
  have clockBlank := workBlank 2 (by simp)
  have descriptorBlank := workBlank 3 (by simp)
  have destinationBlank := workBlank 5 (by simp)
  have copyRun := BinaryDescriptorInstall.install_hoare (0 : Fin 6) 3 (by decide) caller (bits targetWidth)
    widthReady widthHead descriptorBlank.2 descriptorBlank.1
  have rulerReady : Placement.active rulerSlots copied = RecoverBinaryRuler.input (bits targetWidth) := by
    rw [rulerSlots, InjectivePlacement.active_bank, RecoverBinaryRuler.input, CountedGuardConstantsFill.input,
      CountedGuardGadgetPosition.input, ←GammaDescriptorRead.controller_descriptor]
    unfold rulerMap copied setTape
    apply congrArg₂ Tapes.mk
    all_goals funext slot; fin_cases slot <;> simp [rulerBlank, clockBlank]
    exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm
  have rulerEndpoint : Placement.replace rulerSlots copied (RecoverBinaryRuler.output targetWidth) = ruled := by
    apply InjectivePlacement.replace_eq rulerMap rulerMap_injective (by decide : 3+3=6) copied ruled
    · rw [InjectivePlacement.active_bank]
      unfold rulerMap ruled RecoverBinaryRuler.output setTape
      apply congrArg₂ Tapes.mk
      all_goals funext slot; fin_cases slot <;> simp [clockBlank, descriptorBlank]
    · intro slot outside
      have notRuler : slot ≠ 1 := by intro equal; exact outside 0 (by simpa [rulerMap] using equal.symm)
      have notDescriptor : slot ≠ 3 := by intro equal; exact outside 2 (by simpa [rulerMap] using equal.symm)
      simp [ruled, copied, setTape, notRuler, notDescriptor]
  have rulerRun := Placement.hoare_at (RecoverBinaryRuler.runs_build (alphabet := 2) (bits targetWidth) targetWidth
    (RecursiveChildQuotientsConstant.bits_value _)) rulerSlots copied rulerReady
  have rulerExact : HoareTime (Placement.placed (RecoverBinaryRuler.program (alphabet := 2)) rulerSlots)
      (· = copied) (· = ruled) (8*targetWidth+9*(bits targetWidth).length+31) := by
    apply rulerRun.consequence (fun _ ready => ready) _ le_rfl
    rintro bank ⟨localBank, rfl, ready⟩
    exact ready.trans rulerEndpoint
  have wideningReady : Placement.active wideningSlots ruled = NativeSignExtend.input source targetWidth := by
    rw [wideningSlots, InjectivePlacement.active_bank]
    unfold wideningMap ruled setTape NativeSignExtend.input ChirpSignExtend.bank RulerCopy.cfg Config.tapes
    apply congrArg₂ Tapes.mk
    all_goals funext slot; fin_cases slot <;> simp [sourceReady, sourceHead, destinationBlank]
  have wideningEndpoint : Placement.replace wideningSlots ruled (NativeSignExtend.cleanOutput source targetWidth) = finished := by
    apply InjectivePlacement.replace_eq wideningMap wideningMap_injective (by decide : 3+3=6) ruled finished
    · rw [InjectivePlacement.active_bank]
      unfold wideningMap finished setTape NativeSignExtend.cleanOutput ChirpSignExtend.bank RulerCopy.cfg Config.tapes
      apply congrArg₂ Tapes.mk
      all_goals funext slot; fin_cases slot <;> simp [sourceReady, sourceHead, rulerBlank]
    · intro slot outside
      have notRuler : slot ≠ 1 := by intro equal; exact outside 0 (by simpa [wideningMap] using equal.symm)
      have notDestination : slot ≠ 5 := by intro equal; exact outside 2 (by simpa [wideningMap] using equal.symm)
      simp [finished, ruled, setTape, notRuler, notDestination]
  have wideningRun := Placement.hoare_at (NativeSignExtend.runs_clean source targetWidth sourceFits)
    wideningSlots ruled wideningReady
  have wideningExact : HoareTime (Placement.placed NativeSignExtend.cleanProgram wideningSlots)
      (· = ruled) (· = finished) (9*targetWidth+source.length+21) := by
    apply wideningRun.consequence (fun _ ready => ready) _ le_rfl
    rintro bank ⟨localBank, rfl, ready⟩
    exact ready.trans wideningEndpoint
  unfold program cost
  apply ((copyRun.seq rulerExact).seq wideningExact).consequence (fun _ ready => ready) (fun _ ready => ready) ?_
  omega

theorem runs_signed (caller : Tapes 6 2) (source : List (Fin 2)) (sourcePred targetPred : ℕ)
    (sourceWidth : source.length = sourcePred+1) (sourceFits : sourcePred ≤ targetPred)
    (widthReady : caller.tape 0 = RadixZeroFill.encodedBinary (bits (targetPred+1)))
    (widthHead : caller.head 0 = 1)
    (sourceReady : caller.tape 4 = NativeSignExtend.nativeTape source) (sourceHead : caller.head 4 = 0)
    (workBlank : ∀ slot : Fin 6, slot = 1 ∨ slot = 2 ∨ slot = 3 ∨ slot = 5 →
      caller.head slot = 0 ∧ caller.tape slot = (fun _ => blank)) :
    HoareTime program (· = caller)
      (· = setTape caller (5 : Fin 6) (NativeSignExtend.nativeTape (NativeSignExtend.extended source (targetPred+1))) 0)
      (cost source.length (targetPred+1)) ∧
      (NativeSignExtend.extended source (targetPred+1)).length = targetPred+1 ∧
      ButterflySigned.signedValue targetPred (NativeSignExtend.extended source (targetPred+1)) =
        ButterflySigned.signedValue sourcePred source :=
  ⟨runs caller source _ (by omega) widthReady widthHead sourceReady sourceHead workBlank,
    NativeSignExtend.extended_length source _ (by omega),
    NativeSignExtend.extended_signed source sourcePred targetPred sourceWidth sourceFits⟩

end
end IntegerMultBounds.Machine.NativeSignExtendSetup
