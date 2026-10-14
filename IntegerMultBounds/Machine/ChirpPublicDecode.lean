module

public import IntegerMultBounds.Machine.ChirpPublicCodec
public import IntegerMultBounds.Machine.CountedPackedGuarded

/-! Exact native LSB radix-two / public MSB Boolean inverse codec. These are
literal word roundtrips and centered signed decoding identities, including
the most negative representable word. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpPublicDecode

def bit (digit : Fin 2) : Bool := decide (digit=1)
def publicWord (digits : List (Fin 2)) := digits.reverse.map bit

def decode (symbol : Fin 6) : Fin 6 :=
  if symbol=RadixDigits.digitSymbol 0 then bitSymbol false
  else if symbol=RadixDigits.digitSymbol 1 then bitSymbol true else symbol

def live (symbol : Fin 6) : Bool := (RadixDigits.readDigit symbol).isSome

theorem digit_bit (digit : Fin 2) : ChirpPublicCodec.digit (bit digit)=digit := by fin_cases digit <;> decide

theorem bit_digit (value : Bool) : bit (ChirpPublicCodec.digit value)=value := by cases value <;> decide

theorem decode_digit (digit : Fin 2) : decode (RadixDigits.digitSymbol digit)=bitSymbol (bit digit) := by
  fin_cases digit <;> decide

theorem live_digit (digit : Fin 2) : live (RadixDigits.digitSymbol digit)=true := by simp [live]

theorem decoded_symbols (digits : List (Fin 2)) :
    (digits.map RadixDigits.digitSymbol).reverse.map decode=(publicWord digits).map (bitSymbol (a := 2)) := by
  simp only [←List.map_reverse,List.map_map,Function.comp_def,decode_digit,publicWord]

theorem native_public (digits : List (Fin 2)) : ChirpPublicCodec.nativeWord (publicWord digits)=digits := by
  unfold ChirpPublicCodec.nativeWord publicWord
  rw [←List.map_reverse,List.reverse_reverse,List.map_map]
  simp only [Function.comp_def]
  have inverse : (fun digit => ChirpPublicCodec.digit (bit digit))=id := funext digit_bit
  rw [inverse,List.map_id]

theorem public_native (bits : List Bool) : publicWord (ChirpPublicCodec.nativeWord bits)=bits := by
  unfold ChirpPublicCodec.nativeWord publicWord
  rw [←List.map_reverse,List.reverse_reverse,List.map_map]
  simp only [Function.comp_def]
  have inverse : (fun value => bit (ChirpPublicCodec.digit value))=id := funext bit_digit
  rw [inverse,List.map_id]

theorem public_length (digits : List (Fin 2)) : (publicWord digits).length=digits.length := by simp [publicWord]

/-- Actual public serialization retains the native signed numerator exactly.
The representable minimum is covered, so output needs no extra guard. -/
theorem public_signed (digits : List (Fin 2)) (widthPred : ℕ) (wordLength : digits.length=widthPred+1) :
    Spec.SignedRingProduct.compValue (publicWord digits)=ButterflySigned.signedValue widthPred digits := by
  have decoded := ChirpPublicCodec.native_signed (publicWord digits) widthPred (by rw [public_length,wordLength])
  rw [native_public] at decoded
  exact decoded.symm

theorem public_value (digits : List (Fin 2)) : binaryValue (publicWord digits)=RadixDigits.value digits := by
  have value := ChirpPublicCodec.native_value (publicWord digits)
  rw [native_public] at value
  exact value.symm

/-- The native centered integer reduces back to its original full-width
unsigned residue, including the representable minimum and leading padding. -/
theorem signed_residue (digits : List (Fin 2)) (widthPred : ℕ) (wordLength : digits.length=widthPred+1) :
    (ButterflySigned.signedValue widthPred digits % (2 : ℤ)^(widthPred+1)).toNat=RadixDigits.value digits := by
  have valueBound : (RadixDigits.value digits : ℤ)<(2 : ℤ)^(widthPred+1) := by
    have bound := RadixDigits.value_lt (by decide : 2≤2) digits
    rw [wordLength] at bound
    exact_mod_cast bound
  have valueNonnegative : (0 : ℤ)≤RadixDigits.value digits := by positivity
  have modulus : (((2^(widthPred+1) : ℕ) : ℤ))=(2 : ℤ)^(widthPred+1) := by norm_cast
  unfold ButterflySigned.signedValue
  split_ifs
  · rw [Int.emod_eq_of_lt valueNonnegative valueBound]
    simp
  · rw [modulus,Int.sub_emod,Int.emod_self,sub_zero,Int.emod_emod,
      Int.emod_eq_of_lt valueNonnegative valueBound]
    simp

/-- Serialization emits exactly the manuscript's canonical public component
word for the actual native signed value, not just an equal decoded integer. -/
theorem public_compWord (digits : List (Fin 2)) (widthPred : ℕ) (wordLength : digits.length=widthPred+1) :
    publicWord digits=Spec.SignedRingProduct.compWord (widthPred+1) (ButterflySigned.signedValue widthPred digits) := by
  apply List.reverse_inj.mp
  apply CountedPackedGuarded.word_eq_of_length_value
  · simp only [List.length_reverse,public_length,Spec.SignedRingProduct.length_compWord,wordLength]
  · rw [ElementaryMultiplyCore.value_reverse,ElementaryMultiplyCore.value_reverse,public_value,
      Spec.SignedRingProduct.compWord,Spec.SignedRingProduct.binaryValue_msbBits,signed_residue digits widthPred wordLength]
    have valueBound := RadixDigits.value_lt (by decide : 2≤2) digits
    rw [wordLength] at valueBound
    exact (Nat.mod_eq_of_lt valueBound).symm

end IntegerMultBounds.Machine.ChirpPublicDecode
