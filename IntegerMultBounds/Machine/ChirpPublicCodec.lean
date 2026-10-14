module

public import IntegerMultBounds.Machine.ChirpConjugateStream
public import IntegerMultBounds.Machine.RecoverRecordFormat

/-! Exact public MSB Boolean / native LSB radix-two complex field codec.
The symbol map is implemented by the mapped-copy transitions; these lemmas
certify its literal words and signed numerical interpretation. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpPublicCodec

def digit (bit : Bool) : Fin 2 := if bit then 1 else 0

def encode (symbol : Fin 6) : Fin 6 :=
  if symbol=bitSymbol false then RadixDigits.digitSymbol 0
  else if symbol=bitSymbol true then RadixDigits.digitSymbol 1 else symbol

def nativeWord (publicWord : List Bool) := publicWord.reverse.map digit

theorem encode_bit (bit : Bool) : encode (bitSymbol bit)=RadixDigits.digitSymbol (digit bit) := by
  cases bit <;> decide

theorem encoded_word (publicWord : List Bool) :
    (publicWord.reverse.map (bitSymbol (a := 2))).map encode=(nativeWord publicWord).map RadixDigits.digitSymbol := by
  simp only [List.map_map,Function.comp_def,encode_bit,nativeWord]

theorem native_length (publicWord : List Bool) : (nativeWord publicWord).length=publicWord.length := by
  simp [nativeWord]

theorem digit_value (bits : List Bool) : RadixDigits.value (bits.map digit)=Counter.value bits := by
  induction bits with
  | nil => rfl
  | cons bit rest inductionHypothesis =>
    cases bit <;> simp [RadixDigits.value,Counter.value,digit,inductionHypothesis]

theorem native_value (publicWord : List Bool) : RadixDigits.value (nativeWord publicWord)=binaryValue publicWord := by
  rw [nativeWord,digit_value,ElementaryMultiplyCore.value_reverse]

/-- Native centered residue decoding agrees exactly with the original public
signed format, including the most negative representable value. -/
theorem native_signed (publicWord : List Bool) (widthPred : ℕ) (wordLength : publicWord.length=widthPred+1) :
    ButterflySigned.signedValue widthPred (nativeWord publicWord)=Spec.SignedRingProduct.compValue publicWord := by
  rw [←RecoverRecordFormat.signed_reverse]
  apply ButterflySigned.signed_unique widthPred _ (by rw [native_length,wordLength])
  · have bounds := TwosComplement.signed_bounds publicWord.reverse (by
      intro empty
      have emptyLength := congrArg List.length empty
      simp only [List.length_reverse,List.length_nil,wordLength] at emptyLength
      omega)
    simpa only [List.length_reverse,wordLength,Nat.add_sub_cancel,Nat.cast_pow,Nat.cast_ofNat] using bounds
  · rw [native_value,←ElementaryMultiplyCore.value_reverse]
    unfold TwosComplement.signed
    rw [List.length_reverse,wordLength]
    split_ifs
    · simp only [Int.cast_sub,Int.cast_natCast,Int.cast_pow,Int.cast_ofNat]
      have modulusZero : (2 : ZMod (2^(widthPred+1)))^(widthPred+1)=0 := by
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using (ZMod.natCast_self (2^(widthPred+1)))
      rw [modulusZero,sub_zero]
    · simp

/-- Public numerator bounds give the exact signed native numerator required
by chirp arithmetic; no separate codec correctness hypothesis is supplied. -/
theorem native_compWord (widthPred : ℕ) (numerator : ℤ)
    (lowerBound : -(2 : ℤ)^widthPred ≤ numerator) (upperBound : numerator<(2 : ℤ)^widthPred) :
    ButterflySigned.signedValue widthPred (nativeWord (Spec.SignedRingProduct.compWord (widthPred+1) numerator))=numerator := by
  rw [native_signed _ widthPred (by simp)]
  exact Spec.SignedRingProduct.compValue_compWord (by omega) (by simpa using lowerBound) (by simpa using upperBound)

end IntegerMultBounds.Machine.ChirpPublicCodec
