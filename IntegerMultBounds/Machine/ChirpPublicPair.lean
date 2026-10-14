module

public import IntegerMultBounds.Machine.ChirpPublicField

/-! Both public contiguous MSB fields become one native LSB complex record.
Two real physical field adapters share the same restored width ruler. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpPublicPair
noncomputable section
open ChirpPublicField (bank)
open RecoverCarryStep (word)
open ChirpPublicCodec (nativeWord)

def program := seq ChirpPublicField.program ChirpPublicField.program

/-- Read both components without a source delimiter or a decoded-field tape.
The source cursor advances to the next public pair and every ruler cell is
retained, ready at origin for the next iteration. -/
theorem runs_pair (rulerBits real imaginary : List Bool)
    (realWidth : real.length=rulerBits.length) (imaginaryWidth : imaginary.length=rulerBits.length)
    (background destination : ℤ → Fin 6) (origin destinationHead : ℤ) :
    HoareTime program
      (· = bank (word rulerBits) (putWord background origin ((real++imaginary).map bitSymbol)) destination 0 origin destinationHead)
      (· = bank (word rulerBits) (putWord background origin ((real++imaginary).map bitSymbol))
        (putWord destination destinationHead (DelimitedRadixRecord.complex (nativeWord real) (nativeWord imaginary)))
        0 (origin+2*rulerBits.length) (destinationHead+2*(rulerBits.length+1))) (14*rulerBits.length+39) := by
  let source := putWord background origin ((real++imaginary).map (bitSymbol (a := 2)))
  let firstDestination := putWord destination destinationHead (DelimitedRadixRecord.field (nativeWord real))
  have realSource : putWord source origin (real.map bitSymbol)=source := by
    simpa only [source,List.map_append,List.nil_append,List.append_nil,List.length_nil,Nat.cast_zero,add_zero] using
      WordSegments.middle background origin [] (real.map (bitSymbol (a := 2))) (imaginary.map bitSymbol)
  have imaginarySource : putWord source (origin+real.length) (imaginary.map bitSymbol)=source := by
    simpa only [source,List.map_append,List.append_nil,List.length_map] using
      WordSegments.middle background origin (real.map (bitSymbol (a := 2))) (imaginary.map bitSymbol) []
  have realRun := ChirpPublicField.runs_native rulerBits real realWidth.symm source destination origin destinationHead
  rw [realSource] at realRun
  have imaginaryRun := ChirpPublicField.runs_native rulerBits imaginary imaginaryWidth.symm source firstDestination
    (origin+real.length) (destinationHead+real.length+1)
  rw [imaginarySource] at imaginaryRun
  have realFieldLength : (DelimitedRadixRecord.field (nativeWord real)).length=real.length+1 := by
    rw [DelimitedRadixRecord.field_length,ChirpPublicCodec.native_length]
  have appended : putWord firstDestination (destinationHead+real.length+1) (DelimitedRadixRecord.field (nativeWord imaginary)) =
      putWord destination destinationHead (DelimitedRadixRecord.complex (nativeWord real) (nativeWord imaginary)) := by
    unfold firstDestination DelimitedRadixRecord.complex
    have nextPosition : destinationHead+real.length+1=destinationHead+(DelimitedRadixRecord.field (nativeWord real)).length := by
      rw [realFieldLength]
      push_cast
      ring
    rw [nextPosition,putWord_append_forward]
  rw [appended] at imaginaryRun
  have sourceEnd : origin+real.length+imaginary.length=origin+2*rulerBits.length := by
    rw [realWidth,imaginaryWidth]
    push_cast
    ring
  have destinationEnd : destinationHead+real.length+1+imaginary.length+1=destinationHead+2*(rulerBits.length+1) := by
    rw [realWidth,imaginaryWidth]
    push_cast
    ring
  rw [sourceEnd,destinationEnd] at imaginaryRun
  unfold program
  apply (realRun.seq imaginaryRun).consequence (fun _ ready => ready) (fun _ finished => finished)
  rw [realWidth,imaginaryWidth]
  omega

end
end IntegerMultBounds.Machine.ChirpPublicPair
