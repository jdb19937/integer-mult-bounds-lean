module

public import IntegerMultBounds.Machine.ChirpConsumeNumerator

/-! Truncate an actual native numerator word from the sum machine: consume
its cell-one field, generate the unit operand and execute the concrete fast
truncation/publication pipeline. The original native source finishes blank. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpNativeTruncate
noncomputable section
open SharedPlacementAlphabet (setTape setTape_append_left setTape_append_right)
open Schoenhage Strm Tp

abbrev tapeCount := 93
def sourceSlot : Fin tapeCount := Fin.natAdd 92 (0 : Fin 1)
def rawSlot : Fin tapeCount := Fin.castAdd 1 (Fin.castAdd 1 zF)
def slots : Fin 2 → Fin tapeCount := ![sourceSlot,rawSlot]
theorem slots_injective : Function.Injective slots := by decide

def placement := InjectivePlacement.placement slots slots_injective (by decide : 2+91=93)
def setup := Placement.placed ChirpConsumeNumerator.program placement
def program := seq setup (extend ChirpTruncate.program 1)

def nativeBank (digits : List (Fin 2)) : Tapes 1 2 := ⟨fun _ => 0,fun _ => ChirpConsumeNumerator.source digits⟩
def empty : Tapes 1 2 := ⟨fun _ => 0,fun _ _ => blank⟩
def input (digits : List (Fin 2)) (dropPrecision width : ℕ) :=
  (ChirpTruncate.input [] dropPrecision width).append (nativeBank digits)

def after (digits : List (Fin 2)) (dropPrecision width : ℕ) :=
  setTape (setTape (input digits dropPrecision width) sourceSlot (fun _ => blank) 0) rawSlot
    (ChirpConsumeNumerator.destination digits) 0

def output (digits : List (Fin 2)) (dropPrecision width : ℕ) :=
  (ChirpTruncate.output (ChirpArithmeticCodec.rawBits digits) dropPrecision width).append empty

def words (digits : List (Fin 2)) (dropPrecision width : ℕ) :=
  ChirpTruncate.words (ChirpArithmeticCodec.rawBits digits) dropPrecision width

private theorem active_input (digits : List (Fin 2)) (dropPrecision width : ℕ) :
    Placement.active placement (input digits dropPrecision width)=ChirpConsumeNumerator.input digits := by
  rw [placement,InjectivePlacement.active_bank]
  apply Placement.Tapes.ext'
  · intro slot; fin_cases slot <;> rfl
  · intro slot
    fin_cases slot
    · rfl
    · change (ChirpFastProduct.input [] [] dropPrecision width).tape zF=(fun _ => blank)
      simpa [ChirpFastProduct.input,Alphabet.mapTapes,Schoenhage.rawFM,zF,zG,iW,iP,zO,RulerWordMap.word,putWord]
        using ChirpFastNativeProduct.mapped_word []

private theorem after_eq (digits : List (Fin 2)) (dropPrecision width : ℕ) :
    after digits dropPrecision width=(ChirpTruncate.input (ChirpArithmeticCodec.rawBits digits) dropPrecision width).append empty := by
  have cleared : setTape (nativeBank digits) (0 : Fin 1) (fun _ => blank) 0=empty := by
    apply Placement.Tapes.ext'
    · intro slot; fin_cases slot; rfl
    · intro slot; fin_cases slot; rfl
  simp only [after,input,sourceSlot,rawSlot,setTape_append_right,setTape_append_left,cleared]
  unfold ChirpTruncate.input ChirpConsumeNumerator.destination
  rw [ChirpFastNativeProduct.input_left_update]

/-- Actual native-field consumption, internally generated unit, fast signed
truncation and publication, with no converted numerator supplied initially. -/
theorem runs (digits : List (Fin 2)) (dropPrecision width : ℕ)
    (wordWidth : digits.length=width) (widthPositive : 1≤width) (dropFits : dropPrecision≤width) :
    HoareTime program (· = input digits dropPrecision width) (· = output digits dropPrecision width)
      (Schoenhage.fmTime width+13*width+37) := by
  have localRun := ChirpConsumeNumerator.runs digits
  have executed := Placement.hoare_at localRun placement (input digits dropPrecision width) (active_input digits dropPrecision width)
  have different : rawSlot≠sourceSlot := by decide
  have activeAfter : Placement.active placement (after digits dropPrecision width)=ChirpConsumeNumerator.output digits := by
    rw [placement,InjectivePlacement.active_bank]
    apply Placement.Tapes.ext'
    · intro slot
      fin_cases slot <;> simp [after,setTape,slots,ChirpConsumeNumerator.output,ChirpConsumeNumerator.bank,Copy.tapes,Copy.cfg,Config.tapes,different.symm]
    · intro slot
      fin_cases slot <;> simp [after,setTape,slots,ChirpConsumeNumerator.output,ChirpConsumeNumerator.bank,Copy.tapes,Copy.cfg,Config.tapes,different.symm]
  have endpoint := InjectivePlacement.replace_eq slots slots_injective (by decide : 2+91=93)
    (input digits dropPrecision width) (after digits dropPrecision width) _ activeAfter (by
      intro slot outside
      have notSource : sourceSlot≠slot := outside 0
      have notRaw : rawSlot≠slot := outside 1
      simp [after,setTape,Function.update_of_ne notSource.symm,Function.update_of_ne notRaw.symm])
  have setupRun : HoareTime setup (· = input digits dropPrecision width) (· = after digits dropPrecision width) (3*digits.length+10) := by
    apply executed.consequence (fun _ ready => ready) _ le_rfl
    rintro finalBank ⟨localBank,rfl,rfl⟩
    exact endpoint
  rw [after_eq] at setupRun
  have truncated := FamilyPlacementAlphabet.extend_hoare
    (ChirpTruncate.runs (ChirpArithmeticCodec.rawBits digits) dropPrecision width
      (by simpa [ChirpArithmeticCodec.rawBits] using wordWidth) widthPositive dropFits) empty
  unfold program output
  exact (setupRun.seq truncated).consequence (fun _ ready => ready) (fun _ finished => finished) (by omega)

/-- Scale slack derives exact signed truncation of the physically read
native sum, including negative numerators rounded toward zero. -/
theorem words_signed (digits : List (Fin 2)) (numeratorScale dropPrecision width : ℕ)
    (wordWidth : digits.length=width) (wideEnough : numeratorScale+2≤width) (dropFits : dropPrecision≤width)
    (numeratorBound : |ButterflySigned.signedValue (width-1) digits|≤(2 : ℤ)^numeratorScale) :
    ButterflySigned.signedValue (width-1) (words digits dropPrecision width)=
      (ButterflySigned.signedValue (width-1) digits).tdiv (2^dropPrecision) := by
  have decoded := ChirpConsumeNumerator.raw_signed digits (width-1) (by rw [wordWidth]; omega)
  have computed := ChirpTruncate.words_signed_of_scale (ChirpArithmeticCodec.rawBits digits) numeratorScale dropPrecision width
    (by simpa [ChirpArithmeticCodec.rawBits] using wordWidth) wideEnough dropFits (by simpa only [decoded] using numeratorBound)
  simpa only [words,decoded] using computed

theorem words_length (digits : List (Fin 2)) (dropPrecision width : ℕ) :
    (words digits dropPrecision width).length=width := ChirpTruncate.words_length _ _ _

theorem output_result (digits : List (Fin 2)) (dropPrecision width : ℕ) :
    (output digits dropPrecision width).tape (Fin.castAdd 1 ChirpFastNativeProduct.nativeSlot)=
      RulerWordMap.word ((words digits dropPrecision width).map RadixDigits.digitSymbol) := by
  change (ChirpTruncate.output (ChirpArithmeticCodec.rawBits digits) dropPrecision width).tape
    ChirpFastNativeProduct.nativeSlot=_
  exact ChirpTruncate.output_result _ _ _

theorem source_blank (digits : List (Fin 2)) (dropPrecision width : ℕ) :
    (output digits dropPrecision width).tape sourceSlot=(fun _ => blank) := by
  change empty.tape (0 : Fin 1)=_
  rfl

theorem output_head (digits : List (Fin 2)) (dropPrecision width : ℕ) (slot : Fin tapeCount) :
    (output digits dropPrecision width).head slot=0 := by
  refine Fin.addCases (m := 92) (n := 1) (fun index => ?_) (fun index => ?_) slot
  · simp only [output,Tapes.append,Fin.addCases_left]
    exact ChirpTruncate.output_head _ _ _ _
  · simp [output,Tapes.append,empty]

end
end IntegerMultBounds.Machine.ChirpNativeTruncate
