module

public import IntegerMultBounds.Machine.TapeAlphabet
public import IntegerMultBounds.Machine.ChirpSignExtend
public import IntegerMultBounds.Machine.NativePolynomialConjugationData
public import IntegerMultBounds.Machine.RecoverArrayCleanup

@[expose] public section
namespace IntegerMultBounds.Machine.NativeSignExtend
noncomputable section
open NativePolynomialConjugationData (bits digits)
open RecoverCarryStep (word)
open RecoverWorkspace (atProgram)

def swapDigits (symbol : Fin 6) : Fin 6 := ![0,4,5,3,1,2] symbol

def digitEncoding : Alphabet.Encoding 2 2 where
  encode := swapDigits
  decode := swapDigits
  decode_encode := by intro symbol; fin_cases symbol <;> rfl

def encoding (slot : Fin 3) : Alphabet.Encoding 2 2 :=
  if slot = 0 then Alphabet.widen 2 0 else digitEncoding

def program := TapeAlphabet.program encoding ChirpSignExtend.program

def extended (source : List (Fin 2)) (targetWidth : ℕ) :=
  digits (ChirpSignExtend.outputBits (bits source) targetWidth)

def nativeTape (source : List (Fin 2)) :=
  putWord (fun _ => (blank : Fin 6)) 0 (source.map RadixDigits.digitSymbol)

def input (source : List (Fin 2)) (targetWidth : ℕ) : Tapes 3 2 :=
  ChirpSignExtend.bank (word (List.replicate targetWidth true)) (nativeTape source) (fun _ => blank) 0 0 0

def output (source : List (Fin 2)) (targetWidth : ℕ) : Tapes 3 2 :=
  ChirpSignExtend.bank (word (List.replicate targetWidth true)) (nativeTape source)
    (nativeTape (extended source targetWidth)) 0 0 0

theorem swap_bit (bit : Bool) :
    swapDigits (bitSymbol bit) = RadixDigits.digitSymbol (NativePolynomialConjugationData.digit bit) := by
  cases bit <;> rfl

@[simp] theorem swap_blank : swapDigits blank = blank := rfl

@[simp] theorem nativeTape_nil : nativeTape [] = (fun _ => blank) := rfl

private theorem map_putWord (background : ℤ → Fin 6) (origin : ℤ) (symbols : List (Fin 6)) :
    (fun position => swapDigits (putWord background origin symbols position)) =
      putWord (fun position => swapDigits (background position)) origin (symbols.map swapDigits) := by
  induction symbols generalizing origin with
  | nil => rfl
  | cons symbol rest inductionHypothesis =>
    funext position
    by_cases atOrigin : position = origin
    · subst position
      simp [putWord]
    · simp only [putWord, List.map_cons, Function.update_of_ne atOrigin]
      exact congrFun (inductionHypothesis (origin + 1)) position

theorem map_word (booleanWord : List Bool) :
    (fun position => swapDigits (word (alphabet := 2) booleanWord position)) = nativeTape (digits booleanWord) := by
  simpa only [word, nativeTape, digits, List.map_map, Function.comp_def, swap_bit, swap_blank] using
    map_putWord (fun _ => blank) 0 (booleanWord.map bitSymbol)

private theorem map_bank (ruler source destination : List Bool) :
    TapeAlphabet.mapTapes encoding (ChirpSignExtend.bank (word ruler) (word source) (word destination) 0 0 0) =
      ChirpSignExtend.bank (word ruler) (nativeTape (digits source)) (nativeTape (digits destination)) 0 0 0 := by
  unfold TapeAlphabet.mapTapes ChirpSignExtend.bank RulerCopy.cfg Config.tapes
  congr 1
  funext slot
  fin_cases slot
  · rfl
  · exact map_word source
  · exact map_word destination

theorem runs (source : List (Fin 2)) (targetWidth : ℕ) (sourceFits : source.length ≤ targetWidth) :
    HoareTime program (· = input source targetWidth) (· = output source targetWidth)
      (7 * targetWidth + source.length + 17) := by
  have execution := TapeAlphabet.map_hoare encoding
    (ChirpSignExtend.runs (bits source) targetWidth (by simpa [bits] using sourceFits))
  have before : TapeAlphabet.mapTapes encoding (ChirpSignExtend.input (bits source) targetWidth) =
      input source targetWidth := by
    have emptyDigits : digits [] = [] := rfl
    have emptyWord : word (alphabet := 2) [] = (fun _ => blank) := rfl
    simpa only [ChirpSignExtend.input, input, NativePolynomialConjugationData.digits_bits,
      emptyDigits, emptyWord, nativeTape_nil] using
      map_bank (List.replicate targetWidth true) (bits source) []
  have after : TapeAlphabet.mapTapes encoding (ChirpSignExtend.output (bits source) targetWidth) =
      output source targetWidth := by
    simpa only [ChirpSignExtend.output, output, extended, NativePolynomialConjugationData.digits_bits] using
      map_bank (List.replicate targetWidth true) (bits source) (ChirpSignExtend.outputBits (bits source) targetWidth)
  apply execution.consequence
  · intro bank ready
    exact ⟨_, rfl, ready.trans before.symm⟩
  · rintro bank ⟨original, rfl, ready⟩
    exact ready.trans after
  · simp [bits]

theorem extended_length (source : List (Fin 2)) (targetWidth : ℕ) (sourceFits : source.length ≤ targetWidth) :
    (extended source targetWidth).length = targetWidth := by
  simp only [extended, digits, List.length_map]
  exact ChirpSignExtend.output_length (bits source) targetWidth (by simpa [bits] using sourceFits)

theorem extended_signed (source : List (Fin 2)) (sourcePred targetPred : ℕ)
    (sourceWidth : source.length = sourcePred + 1) (sourceFits : sourcePred ≤ targetPred) :
    ButterflySigned.signedValue targetPred (extended source (targetPred + 1)) =
      ButterflySigned.signedValue sourcePred source := by
  rw [NativePolynomialConjugationData.signed_decode targetPred _
    (extended_length source _ (by omega)), extended, NativePolynomialConjugationData.bits_digits,
    NativePolynomialConjugationData.signed_decode sourcePred source sourceWidth]
  apply ChirpSignExtend.output_signed
  · simp only [bits, List.length_map, sourceWidth]
    omega
  · intro empty
    have emptyLength := congrArg List.length empty
    simp [bits, sourceWidth] at emptyLength

def cleanProgram := seq program (atProgram RecoverArrayCleanup.eraseOrigin (0 : Fin 3))

def cleanOutput (source : List (Fin 2)) (targetWidth : ℕ) : Tapes 3 2 :=
  ChirpSignExtend.bank (fun _ => blank) (nativeTape source) (nativeTape (extended source targetWidth)) 0 0 0

theorem runs_clean (source : List (Fin 2)) (targetWidth : ℕ) (sourceFits : source.length ≤ targetWidth) :
    HoareTime cleanProgram (· = input source targetWidth) (· = cleanOutput source targetWidth)
      (9 * targetWidth + source.length + 21) := by
  have cleanup := RecoverWorkspace.runs_one_at RecoverArrayCleanup.eraseOrigin (0 : Fin 3)
    (output source targetWidth) (word (List.replicate targetWidth true)) (fun _ => blank) 0 0 rfl rfl
    (RecoverArrayCleanup.runs_erase_origin _ (by
      intro symbol member
      obtain ⟨bit, _, rfl⟩ := List.mem_map.mp member
      cases bit <;> simp [bitSymbol, blank, Fin.ext_iff]))
  apply ((runs source targetWidth sourceFits).seq cleanup).consequence (fun _ ready => ready) _ ?_
  · intro bank ready
    exact ready.trans (by
      unfold output cleanOutput SharedPlacementAlphabet.setTape ChirpSignExtend.bank RulerCopy.cfg Config.tapes
      congr 1 <;> apply List.ofFn_injective <;> rfl)
  · simp only [List.length_map, List.length_replicate]
    omega

end
end IntegerMultBounds.Machine.NativeSignExtend
