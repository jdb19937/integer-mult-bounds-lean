module

public import IntegerMultBounds.Machine.RulerWordMap
public import IntegerMultBounds.Machine.ChirpPublicDecode

/-! Forward LSB adapters between raw Boolean fast-product ports and native
radix-two numerator ports. Both adapters physically write blank destinations,
retain sources/rulers and return every head; neither reverses the word. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpArithmeticCodec
noncomputable section

def nativeBits (bits : List Bool) := bits.map ChirpPublicCodec.digit
def rawBits (digits : List (Fin 2)) := digits.map ChirpPublicDecode.bit

def toNative := RulerWordMap.program ChirpPublicCodec.encode
def toRaw := RulerWordMap.program ChirpPublicDecode.decode

private theorem bits_nonblank (bits : List Bool) :
    ∀ symbol ∈ bits.map (bitSymbol (a := 2)),symbol≠blank := by
  intro symbol member
  obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
  cases bit <;> decide

private theorem digits_nonblank (digits : List (Fin 2)) :
    ∀ symbol ∈ digits.map RadixDigits.digitSymbol,symbol≠(blank : Fin 6) := by
  intro symbol member
  obtain ⟨digit,_,rfl⟩ := List.mem_map.mp member
  fin_cases digit <;> decide

theorem encoded (bits : List Bool) :
    (bits.map (bitSymbol (a := 2))).map ChirpPublicCodec.encode=
      (nativeBits bits).map RadixDigits.digitSymbol := by
  simp only [nativeBits,List.map_map,Function.comp_def,ChirpPublicCodec.encode_bit]

theorem decoded (digits : List (Fin 2)) :
    (digits.map RadixDigits.digitSymbol).map ChirpPublicDecode.decode=
      (rawBits digits).map (bitSymbol (a := 2)) := by
  simp only [rawBits,List.map_map,Function.comp_def,ChirpPublicDecode.decode_digit]

theorem runs_toNative (bits : List Bool) :
    HoareTime toNative (· = RulerWordMap.input (bits.map (bitSymbol (a := 2))))
      (· = RulerWordMap.bank
        (RulerWordMap.word (List.replicate bits.length (bitSymbol true)))
        (RulerWordMap.word (bits.map bitSymbol))
        (RulerWordMap.word ((nativeBits bits).map RadixDigits.digitSymbol)) 0 0 0)
      (4*bits.length+9) := by
  have convertedNonblank : ∀ symbol ∈ bits.map (bitSymbol (a := 2)),ChirpPublicCodec.encode symbol≠blank := by
    intro symbol member
    obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
    rw [ChirpPublicCodec.encode_bit]
    cases bit <;> decide
  have execution := RulerWordMap.runs ChirpPublicCodec.encode (bits.map (bitSymbol (a := 2)))
    (bits_nonblank bits) convertedNonblank
  simpa only [toNative,RulerWordMap.output,List.length_map,nativeBits,List.map_map,Function.comp_def,ChirpPublicCodec.encode_bit] using execution

theorem runs_toRaw (digits : List (Fin 2)) :
    HoareTime toRaw (· = RulerWordMap.input (digits.map RadixDigits.digitSymbol))
      (· = RulerWordMap.bank
        (RulerWordMap.word (List.replicate digits.length (bitSymbol true)))
        (RulerWordMap.word (digits.map RadixDigits.digitSymbol))
        (RulerWordMap.word ((rawBits digits).map bitSymbol)) 0 0 0)
      (4*digits.length+9) := by
  have convertedNonblank : ∀ symbol ∈ digits.map RadixDigits.digitSymbol,ChirpPublicDecode.decode symbol≠(blank : Fin 6) := by
    intro symbol member
    obtain ⟨digit,_,rfl⟩ := List.mem_map.mp member
    rw [ChirpPublicDecode.decode_digit]
    cases ChirpPublicDecode.bit digit <;> decide
  have execution := RulerWordMap.runs ChirpPublicDecode.decode (digits.map RadixDigits.digitSymbol)
    (digits_nonblank digits) convertedNonblank
  simpa only [toRaw,RulerWordMap.output,List.length_map,rawBits,List.map_map,Function.comp_def,ChirpPublicDecode.decode_digit] using execution

/-- Raw LSB words and native digits have identical centered signed values. -/
theorem native_signed (bits : List Bool) (widthPred : ℕ) (wordLength : bits.length=widthPred+1) :
    ButterflySigned.signedValue widthPred (nativeBits bits)=TwosComplement.signed bits := by
  have converted := ChirpPublicCodec.native_signed bits.reverse widthPred (by simpa using wordLength)
  rw [←RecoverRecordFormat.signed_reverse,List.reverse_reverse] at converted
  simpa only [ChirpPublicCodec.nativeWord,List.reverse_reverse,nativeBits] using converted

theorem native_raw (digits : List (Fin 2)) : nativeBits (rawBits digits)=digits := by
  simp [nativeBits,rawBits,List.map_map,Function.comp_def,ChirpPublicDecode.digit_bit]

theorem raw_native (bits : List Bool) : rawBits (nativeBits bits)=bits := by
  simp [nativeBits,rawBits,List.map_map,Function.comp_def,ChirpPublicDecode.bit_digit]

theorem raw_signed (digits : List (Fin 2)) (widthPred : ℕ) (wordLength : digits.length=widthPred+1) :
    TwosComplement.signed (rawBits digits)=ButterflySigned.signedValue widthPred digits := by
  have converted := native_signed (rawBits digits) widthPred (by simpa [rawBits] using wordLength)
  rw [native_raw] at converted
  exact converted.symm

end
end IntegerMultBounds.Machine.ChirpArithmeticCodec
