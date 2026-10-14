module

public import IntegerMultBounds.Machine.ChirpPublicPair

/-! Convert every contiguous public complex record to the native arithmetic
format, preserving both real and imaginary fields. One reusable width ruler
controls field boundaries; the original source's actual blank end controls
array termination, without a record counter or decoded payload. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpPublicArray
noncomputable section
abbrev alphabet := 2
open RecoverCarryStep (word)
open ChirpPublicField (bank)

abbrev Pair := List Bool × List Bool

def raw (pairs : List Pair) : List Bool := pairs.flatMap fun pair => pair.1 ++ pair.2
def native (pairs : List Pair) : List (Fin (alphabet+4)) :=
  pairs.flatMap fun pair => DelimitedRadixRecord.complex (ChirpPublicCodec.nativeWord pair.1) (ChirpPublicCodec.nativeWord pair.2)
def test (symbols : Fin 3 → Fin (alphabet+4)) := decide (symbols 1 ≠ blank)
def program : Program 3 41 alphabet := whileLoop ChirpPublicPair.program test

private theorem source_overwrite (done : List Bool) (pair : Pair) (rest : List Pair) :
    putWord (word (alphabet := alphabet) (done ++ raw (pair :: rest))) done.length
      ((pair.1 ++ pair.2).map bitSymbol) = word (done ++ raw (pair :: rest)) := by
  have middle := WordSegments.middle (fun _ => (blank : Fin (alphabet+4))) 0
    (done.map bitSymbol) ((pair.1 ++ pair.2).map bitSymbol) ((raw rest).map bitSymbol)
  simpa only [word, raw, List.flatMap_cons, List.map_append, List.length_map, zero_add, List.append_assoc] using middle

private theorem test_end (rulerBits done : List Bool) (destination : ℤ → Fin (alphabet+4)) (destinationHead : ℤ) :
    test (bank (word rulerBits) (word done) destination 0 done.length destinationHead).reads = false := by
  change decide (word (alphabet := alphabet) done done.length ≠ blank) = false
  rw [word, putWord_outside _ _ _ _ (Or.inr (by simp))]
  rfl

private theorem test_pair (rulerBits done : List Bool) (pair : Pair) (rest : List Pair)
    (destination : ℤ → Fin (alphabet+4)) (destinationHead : ℤ) (realNonempty : pair.1 ≠ []) :
    test (bank (word rulerBits) (word (done ++ raw (pair :: rest))) destination 0 done.length destinationHead).reads = true := by
  change decide (word (alphabet := alphabet) (done ++ raw (pair :: rest)) done.length ≠ blank) = true
  have view : putWord (word (alphabet := alphabet) (done++raw (pair::rest))) done.length (pair.1.map bitSymbol)=
      word (done++raw (pair::rest)) := by
    have middle := WordSegments.middle (fun _ => (blank : Fin (alphabet+4))) 0
      (done.map bitSymbol) (pair.1.map bitSymbol) ((pair.2++raw rest).map bitSymbol)
    simpa only [word,raw,List.flatMap_cons,List.map_append,List.length_map,zero_add,List.append_assoc] using middle
  rcases pair with ⟨real, imaginary⟩
  cases real with
  | nil => exact False.elim (realNonempty rfl)
  | cons bit tail =>
    have firstCell := congrFun view (done.length : ℤ)
    rw [List.map_cons, putWord_head] at firstCell
    rw [← firstCell]
    cases bit <;> simp [bitSymbol, blank, Fin.ext_iff]

/-- Convert both physical components in every original public record.
The array's actual blank end terminates the loop, including an empty array.
All ruler cells return to origin after each pair; source cells are retained. -/
theorem runs_array (pairs : List Pair) (rulerBits done : List Bool)
    (destination : ℤ → Fin (alphabet+4)) (destinationHead : ℤ)
    (widthPositive : 0 < rulerBits.length)
    (fieldWidths : ∀ pair ∈ pairs, pair.1.length = rulerBits.length ∧ pair.2.length = rulerBits.length) :
    HoareTime program
      (· = bank (word rulerBits) (word (done ++ raw pairs)) destination 0 done.length destinationHead)
      (· = bank (word rulerBits) (word (done ++ raw pairs))
        (putWord destination destinationHead (native pairs)) 0 (done ++ raw pairs).length
        (destinationHead + (native pairs).length))
      ((14 * rulerBits.length + 41) * pairs.length) := by
  induction pairs generalizing done destination destinationHead with
  | nil =>
    intro current equal
    subst current
    refine ⟨0, _, by simp, rfl, ?_, ?_⟩
    · exact while_step_exit ChirpPublicPair.program test _ (by simpa [raw] using test_end rulerBits done destination destinationHead)
    · simp [raw, native, putWord, Config.tapes, Tapes.start]
  | cons pair rest inductionHypothesis =>
    obtain ⟨realWidth, imaginaryWidth⟩ := fieldWidths pair (by simp)
    have fieldRun := ChirpPublicPair.runs_pair rulerBits pair.1 pair.2 realWidth imaginaryWidth
      (word (done ++ raw (pair :: rest))) destination done.length destinationHead
    rw [source_overwrite] at fieldRun
    rw [← realWidth] at fieldRun
    have nextSource : word (alphabet := alphabet) ((done ++ pair.1 ++ pair.2) ++ raw rest) =
        word (done ++ raw (pair :: rest)) := by simp [raw, List.append_assoc]
    have nextPosition : ((done ++ pair.1 ++ pair.2).length : ℤ) = done.length + 2 * pair.1.length := by
      simp only [List.length_append, realWidth, imaginaryWidth, Nat.cast_add]
      ring
    have tailRun := inductionHypothesis (done ++ pair.1 ++ pair.2)
      (putWord destination destinationHead (DelimitedRadixRecord.complex (ChirpPublicCodec.nativeWord pair.1) (ChirpPublicCodec.nativeWord pair.2)))
      (destinationHead + 2 * (pair.1.length + 1))
      (fun next member => fieldWidths next (List.mem_cons_of_mem pair member))
    rw [nextSource, nextPosition] at tailRun
    intro current equal
    subst current
    obtain ⟨bodyElapsed,bodyConfig,bodyBound,bodyExecuted,bodyHalted,bodyEndpoint⟩ := fieldRun _ rfl
    obtain ⟨tailElapsed,finalConfig,tailBound,tailExecuted,finalHalted,finalEndpoint⟩ := tailRun _ bodyEndpoint
    have firstIteration := while_run_iteration ChirpPublicPair.program test _
      (test_pair rulerBits done pair rest destination destinationHead (by
        intro emptyReal
        have : pair.1.length = 0 := by rw [emptyReal]; rfl
        omega)) bodyExecuted bodyHalted
    refine ⟨bodyElapsed + 2 + tailElapsed, finalConfig, ?_, ?_, finalHalted, ?_⟩
    · simp only [List.length_cons]
      rw [realWidth] at bodyBound
      nlinarith
    · unfold program
      rw [run_add, firstIteration]
      exact tailExecuted
    · have recordLength : (DelimitedRadixRecord.complex (ChirpPublicCodec.nativeWord pair.1)
          (ChirpPublicCodec.nativeWord pair.2)).length=2*(pair.1.length+1) := by
        rw [DelimitedRadixRecord.complex_length _ _ pair.1.length
          (ChirpPublicCodec.native_length _) (by rw [ChirpPublicCodec.native_length,imaginaryWidth,realWidth])]
      have destinationPosition : destinationHead+2*(pair.1.length+1) =
          destinationHead+(DelimitedRadixRecord.complex (ChirpPublicCodec.nativeWord pair.1)
            (ChirpPublicCodec.nativeWord pair.2)).length := by
        rw [recordLength]
        push_cast
        ring
      rw [destinationPosition,putWord_append_forward] at finalEndpoint
      simpa only [native,List.flatMap_cons,raw,List.length_append,recordLength,
        Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,List.append_assoc,add_assoc] using finalEndpoint

def nativePairs (pairs : List Pair) : List ChirpConjugateArray.Pair := pairs.map fun pair =>
  (ChirpPublicCodec.nativeWord pair.1,ChirpPublicCodec.nativeWord pair.2)

/-- This is exactly the physical input format of the checked chirp arithmetic
stream, including its two native separators per complex coefficient. -/
theorem native_format (pairs : List Pair) : native pairs=ChirpConjugateArray.native (nativePairs pairs) := by
  simp only [native,nativePairs,ChirpConjugateArray.native,List.flatMap_map]

theorem stream_lengths (pairs : List Pair) (width : ℕ)
    (fieldWidths : ∀ pair ∈ pairs,pair.1.length=width ∧ pair.2.length=width) :
    (raw pairs).length=2*width*pairs.length ∧ (native pairs).length=2*(width+1)*pairs.length := by
  induction pairs with
  | nil => simp [raw,native]
  | cons pair rest inductionHypothesis =>
    obtain ⟨realWidth,imaginaryWidth⟩ := fieldWidths pair (by simp)
    obtain ⟨tailRaw,tailNative⟩ := inductionHypothesis (fun next member => fieldWidths next (List.mem_cons_of_mem pair member))
    have realNative : (ChirpPublicCodec.nativeWord pair.1).length=width := by
      rw [ChirpPublicCodec.native_length,realWidth]
    have imaginaryNative : (ChirpPublicCodec.nativeWord pair.2).length=width := by
      rw [ChirpPublicCodec.native_length,imaginaryWidth]
    simp only [raw,native,List.flatMap_cons,List.length_append,List.length_cons,
      DelimitedRadixRecord.complex_length _ _ _ realNative imaginaryNative] at *
    constructor <;> nlinarith

/-- Original public bit volume pays conversion of both components and all
cursor/ruler resets; no record-count or separate native-volume budget is used. -/
theorem runs_array_volume (pairs : List Pair) (rulerBits done : List Bool)
    (destination : ℤ → Fin 6) (destinationHead : ℤ)
    (widthPositive : 0<rulerBits.length)
    (fieldWidths : ∀ pair ∈ pairs,pair.1.length=rulerBits.length ∧ pair.2.length=rulerBits.length) :
    HoareTime program
      (· = bank (word rulerBits) (word (done++raw pairs)) destination 0 done.length destinationHead)
      (· = bank (word rulerBits) (word (done++raw pairs))
        (putWord destination destinationHead (native pairs)) 0 (done++raw pairs).length
        (destinationHead+(native pairs).length)) (30*(raw pairs).length) := by
  apply (runs_array pairs rulerBits done destination destinationHead widthPositive fieldWidths).consequence
    (fun _ ready => ready) (fun _ finished => finished)
  have lengths := stream_lengths pairs rulerBits.length fieldWidths
  rw [lengths.1]
  nlinarith

def publicPairs {size : ℕ} (width : ℕ) (real imaginary : Fin size → ℤ) : List Pair :=
  (List.finRange size).map fun index =>
    (Spec.SignedRingProduct.compWord width (real index),Spec.SignedRingProduct.compWord width (imaginary index))

theorem raw_public {size : ℕ} (width : ℕ) (real imaginary : Fin size → ℤ) :
    raw (publicPairs width real imaginary)=Spec.SignedRingProduct.record width real imaginary := by
  simp only [raw,publicPairs,Spec.SignedRingProduct.record,List.flatMap_map]

/-- Native decoding of the literal converted public coefficient array gives
the original signed Gaussian dyadics, with no rounding or extra scale change. -/
theorem native_values_public {size : ℕ} (widthPred precision : ℕ) (real imaginary : Fin size → ℤ)
    (realLower : ∀ index,-(2 : ℤ)^widthPred ≤ real index) (realUpper : ∀ index,real index<(2 : ℤ)^widthPred)
    (imaginaryLower : ∀ index,-(2 : ℤ)^widthPred ≤ imaginary index)
    (imaginaryUpper : ∀ index,imaginary index<(2 : ℤ)^widthPred) :
    (nativePairs (publicPairs (widthPred+1) real imaginary)).map (ChirpConjugateArray.value widthPred precision) =
      (List.finRange size).map (fun index => ButterflySigned.complexValue (real index) (imaginary index) precision) := by
  simp only [nativePairs,publicPairs,List.map_map,Function.comp_def,ChirpConjugateArray.value]
  apply List.map_congr_left
  intro index member
  rw [ChirpPublicCodec.native_compWord widthPred (real index) (realLower index) (realUpper index),
    ChirpPublicCodec.native_compWord widthPred (imaginary index) (imaginaryLower index) (imaginaryUpper index)]

/-- The original public signed-product record is physically converted to the
exact native complex-array format in time linear in its original bit length. -/
theorem runs_public {size : ℕ} (width : ℕ) (real imaginary : Fin size → ℤ) (widthPositive : 0<width) :
    HoareTime program
      (· = bank (word (List.replicate width true)) (word (Spec.SignedRingProduct.record width real imaginary))
        (fun _ => blank) 0 0 0)
      (· = bank (word (List.replicate width true)) (word (Spec.SignedRingProduct.record width real imaginary))
        (putWord (fun _ => blank) 0 (ChirpConjugateArray.native (nativePairs (publicPairs width real imaginary))))
        0 (Spec.SignedRingProduct.record width real imaginary).length (native (publicPairs width real imaginary)).length)
      (30*(Spec.SignedRingProduct.record width real imaginary).length) := by
  have execution := runs_array_volume (publicPairs width real imaginary) (List.replicate width true) []
    (fun _ => blank) 0 (by simpa using widthPositive) (by
      intro pair member
      obtain ⟨index,_,rfl⟩ := List.mem_map.mp member
      simp)
  simpa only [raw_public,native_format,List.nil_append,List.length_nil,Nat.cast_zero,zero_add] using execution

end
end IntegerMultBounds.Machine.ChirpPublicArray
