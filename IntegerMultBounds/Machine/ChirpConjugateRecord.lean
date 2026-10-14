module

public import IntegerMultBounds.Machine.ChirpConjugateNumerator
public import IntegerMultBounds.Machine.UnitPhaseRecordIO

/-! Native complex-record conjugation for chirp preparation. Literal record IO,
signed numerator arithmetic and source cleanup compose on one bank; only the
stream cursors and emitted conjugate record change. All private tapes return
blank at origin, allowing immediate reuse for the next coefficient. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpConjugateRecord
noncomputable section
open ChirpConjugateNumerator (words)
open SharedPlacementAlphabet (setTape)
open DelimitedRadixRecord (Context complex)

def slots : Fin 6 → Fin 60 := fun index => ⟨50+index.val,by omega⟩
theorem slots_injective : Function.Injective slots := by
  intro left right equal
  apply Fin.ext
  have values := congrArg Fin.val equal
  simp only [slots] at values
  omega

def placement := InjectivePlacement.placement slots slots_injective (by decide : 6+54=60)
def conjugate := Placement.placed ChirpConjugateNumerator.program placement
def cleanup := Placement.placed UnitPhaseCoreReset.program placement

def program := seq (seq (seq UnitPhaseRecordIO.readProgram conjugate) UnitPhaseRecordIO.emitProgram) cleanup

def sources (context : Context 2) : ℕ → List (Fin 2) := fun index => if index=0 then context.re else context.im

def read (current : Tapes 60 2) (context : Context 2) := UnitPhaseRecordIO.readOutput current context

def applied (current : Tapes 60 2) (context : Context 2) :=
  Placement.replace placement (read current context) (ChirpConjugateNumerator.output (sources context))

def emitted (current : Tapes 60 2) (context : Context 2) :=
  UnitPhaseRecordIO.emitOutput (applied current context) (words 0 (sources context)) (words 1 (sources context))

def output (current : Tapes 60 2) (context : Context 2) :=
  Placement.replace placement (emitted current context) (SharedBank.empty 6 2)

private theorem read_active (current : Tapes 60 2) (context : Context 2)
    (coreBlank : ∀ index : Fin 6,current.head (slots index)=0 ∧ current.tape (slots index)=(fun _ => blank)) :
    Placement.active placement (read current context)=ChirpConjugateNumerator.input (sources context) := by
  rw [placement,InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext index <;> fin_cases index
  all_goals simp [read,UnitPhaseRecordIO.readOutput,UnitPhaseRecordIO.readFirst,TwoTapeAt.result,setTape,
    slots,ChirpConjugateNumerator.input,UnitPhaseNumerator.coreInput,RadixLinearCombinationRefresh.controls,Tapes.append,Fin.addCases,sources]
  all_goals first
    | rfl
    | exact (coreBlank 2).1 | exact (coreBlank 3).1 | exact (coreBlank 4).1 | exact (coreBlank 5).1
    | exact (coreBlank 2).2 | exact (coreBlank 3).2 | exact (coreBlank 4).2 | exact (coreBlank 5).2

private theorem emitted_active (current : Tapes 60 2) (context : Context 2) :
    Placement.active placement (emitted current context)=ChirpConjugateNumerator.input (sources context) := by
  rw [placement,InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext index <;> fin_cases index
  all_goals simp [emitted,UnitPhaseRecordIO.emitOutput,setTape,slots]
  all_goals first
    | rfl
    | exact InjectivePlacement.replace_head_slot slots slots_injective (by decide : 6+54=60) _ _ 0
    | exact InjectivePlacement.replace_head_slot slots slots_injective (by decide : 6+54=60) _ _ 1
    | exact InjectivePlacement.replace_head_slot slots slots_injective (by decide : 6+54=60) _ _ 3
    | exact InjectivePlacement.replace_head_slot slots slots_injective (by decide : 6+54=60) _ _ 5
    | exact InjectivePlacement.replace_tape_slot slots slots_injective (by decide : 6+54=60) _ _ 0
    | exact InjectivePlacement.replace_tape_slot slots slots_injective (by decide : 6+54=60) _ _ 1
    | exact InjectivePlacement.replace_tape_slot slots slots_injective (by decide : 6+54=60) _ _ 3
    | exact InjectivePlacement.replace_tape_slot slots slots_injective (by decide : 6+54=60) _ _ 5

/-- The original delimited native record is read physically; both source
words and all private arithmetic storage are erased after emission. -/
theorem runs (current : Tapes 60 2) (context : Context 2) (width : ℕ)
    (fieldWidths : context.re.length=width ∧ context.im.length=width)
    (sourceReady : current.tape 56=context.tape ∧ current.head 56=context.start)
    (coreBlank : ∀ index : Fin 6,current.head (slots index)=0 ∧ current.tape (slots index)=(fun _ => blank)) :
    HoareTime program (· = current) (· = output current context) (24*width+81) := by
  have widths : ∀ index,(sources context index).length=width := by
    intro index
    dsimp [sources]
    split_ifs <;> first | exact fieldWidths.1 | exact fieldWidths.2
  have readRun := UnitPhaseRecordIO.read_runs current context sourceReady
    ⟨(coreBlank 0).2,(coreBlank 0).1⟩ ⟨(coreBlank 1).2,(coreBlank 1).1⟩
  have conjugateRun := Placement.hoare_at (ChirpConjugateNumerator.runs (sources context) width widths)
    placement (read current context) (read_active current context coreBlank)
  have conjugateExact : HoareTime conjugate (· = read current context) (· = applied current context) (12*width+43) := by
    apply conjugateRun.consequence (fun _ ready => ready) _ le_rfl
    rintro finalBank ⟨localBank,rfl,rfl⟩
    rfl
  have emitRun := UnitPhaseRecordIO.emit_runs (applied current context) (words 0 (sources context)) (words 1 (sources context))
    ⟨InjectivePlacement.replace_tape_slot slots slots_injective (by decide : 6+54=60) _ _ 2,
      InjectivePlacement.replace_head_slot slots slots_injective (by decide : 6+54=60) _ _ 2⟩
    ⟨InjectivePlacement.replace_tape_slot slots slots_injective (by decide : 6+54=60) _ _ 4,
      InjectivePlacement.replace_head_slot slots slots_injective (by decide : 6+54=60) _ _ 4⟩
  have cleanupRun := Placement.hoare_at (UnitPhaseCoreReset.runs (sources context) width widths)
    placement (emitted current context) (emitted_active current context)
  apply (((readRun.seq conjugateExact).seq emitRun).seq cleanupRun).consequence (fun _ ready => ready) _ _
  · rintro finalBank ⟨localBank,rfl,rfl⟩
    rfl
  · rw [fieldWidths.1,fieldWidths.2,ChirpConjugateNumerator.words_length _ _ _ widths,
      ChirpConjugateNumerator.words_length _ _ _ widths]
    omega

theorem core_blank (current : Tapes 60 2) (context : Context 2) (index : Fin 6) :
    (output current context).head (slots index)=0 ∧ (output current context).tape (slots index)=(fun _ => blank) :=
  ⟨InjectivePlacement.replace_head_slot slots slots_injective (by decide : 6+54=60) _ _ index,
    InjectivePlacement.replace_tape_slot slots slots_injective (by decide : 6+54=60) _ _ index⟩

def streamOutput (current : Tapes 60 2) (context : Context 2) :=
  setTape (setTape current 56 context.tape (context.start+context.re.length+context.im.length+2)) 58
    (putWord (current.tape 58) (current.head 58) (complex (words 0 (sources context)) (words 1 (sources context))))
    (current.head 58+(words 0 (sources context)).length+(words 1 (sources context)).length+2)

/-- All complementary tapes, including flags and controllers, are retained
literally. The output is appended to its original background and head. -/
theorem output_eq (current : Tapes 60 2) (context : Context 2)
    (coreBlank : ∀ index : Fin 6,current.head (slots index)=0 ∧ current.tape (slots index)=(fun _ => blank)) :
    output current context=streamOutput current context := by
  have outsideDestination : ∀ index : Fin 6,slots index≠(58 : Fin 60) := by
    intro index equal
    have values := congrArg Fin.val equal
    simp only [slots] at values
    omega
  have destinationHead : (applied current context).head 58=current.head 58 := by
    rw [applied,placement,InjectivePlacement.replace_head_other _ _ _ _ _ _ outsideDestination]
    simp [read,UnitPhaseRecordIO.readOutput,UnitPhaseRecordIO.readFirst,TwoTapeAt.result,setTape]
  have destinationTape : (applied current context).tape 58=current.tape 58 := by
    rw [applied,placement,InjectivePlacement.replace_tape_other _ _ _ _ _ _ outsideDestination]
    simp [read,UnitPhaseRecordIO.readOutput,UnitPhaseRecordIO.readFirst,TwoTapeAt.result,setTape]
  apply Placement.Tapes.ext'
  all_goals
    intro slot
    by_cases activeSlot : 50 ≤ slot.val ∧ slot.val < 56
    · let index : Fin 6 := ⟨slot.val-50,by omega⟩
      have slotEquation : slots index=slot := by apply Fin.ext; simp only [slots]; dsimp [index]; omega
      rw [←slotEquation]
      have notSource : 50+index.val≠56 := by omega
      have notDestination : 50+index.val≠58 := by omega
      first
        | rw [(core_blank current context index).1]; simpa (disch := omega) [streamOutput,setTape,slots,Function.update_apply,Fin.ext_iff,notSource,notDestination] using (coreBlank index).1.symm
        | rw [(core_blank current context index).2]; simpa (disch := omega) [streamOutput,setTape,slots,Function.update_apply,Fin.ext_iff,notSource,notDestination] using (coreBlank index).2.symm
    · have outsideCore : ∀ index : Fin 6,slots index≠slot := by
        intro index equal
        have values := congrArg Fin.val equal
        simp only [slots] at values
        omega
      have notReal : slot.val≠50 := by omega
      have notImaginary : slot.val≠51 := by omega
      have notRealOutput : slot.val≠52 := by omega
      have notImaginaryOutput : slot.val≠54 := by omega
      unfold output placement
      first
        | rw [InjectivePlacement.replace_head_other _ _ _ _ _ _ outsideCore]
        | rw [InjectivePlacement.replace_tape_other _ _ _ _ _ _ outsideCore]
      simp only [emitted,UnitPhaseRecordIO.emitOutput,setTape,Function.update_apply,destinationHead,destinationTape]
      have headRetained : (applied current context).head slot=(read current context).head slot :=
        InjectivePlacement.replace_head_other slots slots_injective (by decide : 6+54=60) _ _ slot outsideCore
      have tapeRetained : (applied current context).tape slot=(read current context).tape slot :=
        InjectivePlacement.replace_tape_other slots slots_injective (by decide : 6+54=60) _ _ slot outsideCore
      simp (disch := omega) [headRetained,tapeRetained,read,UnitPhaseRecordIO.readOutput,UnitPhaseRecordIO.readFirst,
        TwoTapeAt.result,streamOutput,setTape,Function.update_apply,Fin.ext_iff,notReal,notImaginary,notRealOutput,notImaginaryOutput]
      split_ifs <;> simp_all

end
end IntegerMultBounds.Machine.ChirpConjugateRecord
