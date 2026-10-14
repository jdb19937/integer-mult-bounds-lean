module

public import IntegerMultBounds.Machine.ChirpPublicEmitArray
public import IntegerMultBounds.Machine.ChirpPublicArray

/-! A complete reusable native-to-public stream serializer. Delimiters discover
all field widths, actual blank-end termination discovers the field count, and
both source/output heads are physically returned to origin. No private ruler,
length descriptor, count descriptor or decoded output is supplied. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpPublicEmitStream
noncomputable section
open ChirpPublicEmitArray (serialized publicBits word)
open RecoverWorkspace (atProgram)

def program := seq (seq ChirpPublicEmitArray.program (atProgram ReturnOrigin.program (0 : Fin 2)))
  (atProgram ReturnOrigin.program (1 : Fin 2))

def input (fields : List (List (Fin 2))) : Tapes 2 2 := Copy.tapes (word (serialized fields)) (fun _ => blank) 0 0

def output (fields : List (List (Fin 2))) : Tapes 2 2 :=
  Copy.tapes (word (serialized fields)) (word ((publicBits fields).map bitSymbol)) 0 0

private theorem native_nonblank (fields : List (List (Fin 2))) : ∀ symbol ∈ serialized fields,symbol ≠ (blank : Fin 6) := by
  intro symbol member
  obtain ⟨digits,_,inField⟩ := List.mem_flatMap.mp member
  simp only [DelimitedRadixRecord.field,List.mem_append,List.mem_singleton] at inField
  rcases inField with dataMember | rfl
  · obtain ⟨digit,_,rfl⟩ := List.mem_map.mp dataMember
    intro equal
    have values := congrArg Fin.val equal
    change digit.val+4=0 at values
    omega
  · decide

private theorem bits_nonblank (bits : List Bool) : ∀ symbol ∈ bits.map (bitSymbol (a := 2)),symbol ≠ blank := by
  intro symbol member
  obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
  cases bit <;> simp [bitSymbol,blank,Fin.ext_iff]

theorem public_length_le (fields : List (List (Fin 2))) : (publicBits fields).length≤(serialized fields).length := by
  induction fields with
  | nil => simp [publicBits,serialized]
  | cons digits rest inductionHypothesis =>
    simp only [publicBits,serialized,List.flatMap_cons,List.length_append,ChirpPublicDecode.public_length,
      DelimitedRadixRecord.field_length] at inductionHypothesis ⊢
    omega

/-- Native field/array boundaries physically drive the serializer. Every
original source cell is retained; the only other tape contains exact public
MSB bits, blank outside them, with both heads at origin. -/
theorem runs (fields : List (List (Fin 2))) :
    HoareTime program (· = input fields) (· = output fields) (12*(serialized fields).length+6) := by
  have arrayRun := ChirpPublicEmitArray.runs_array fields [] (fun _ => blank) 0 (by
    change ChirpPublicDecode.live (putWord (fun _ => blank) 0 ([]++serialized fields) (-1))=false
    rw [putWord_outside _ _ _ _ (Or.inl (by omega))]
    decide)
  simp only [List.nil_append,List.length_nil,Nat.cast_zero,zero_add] at arrayRun
  let finished := Copy.tapes (word (serialized fields)) (word ((publicBits fields).map bitSymbol))
    (serialized fields).length (publicBits fields).length
  let sourceReturned := RecoverWorkspace.restored finished (0 : Fin 2)
  have returnSource := RecoverWorkspace.return_at (0 : Fin 2) finished (serialized fields) (native_nonblank fields) rfl rfl
  have returnDestination := RecoverWorkspace.return_at (1 : Fin 2) sourceReturned ((publicBits fields).map bitSymbol)
    (bits_nonblank _) (by simp [sourceReturned,RecoverWorkspace.restored,finished,SharedPlacementAlphabet.setTape,Copy.tapes,Copy.cfg,Config.tapes,List.length_map])
    (by simp [sourceReturned,RecoverWorkspace.restored,finished,SharedPlacementAlphabet.setTape,Copy.tapes,Copy.cfg,Config.tapes]; rfl)
  have endpoint : RecoverWorkspace.restored sourceReturned (1 : Fin 2)=output fields := by
    unfold sourceReturned RecoverWorkspace.restored finished SharedPlacementAlphabet.setTape output Copy.tapes Copy.cfg Config.tapes
    congr 1 <;> apply List.ofFn_injective <;> rfl
  unfold program input
  apply ((arrayRun.seq returnSource).seq returnDestination).consequence
    (fun _ ready => ready) (fun _ finished => finished.trans endpoint)
  simp only [List.length_map]
  have payloadBound := public_length_le fields
  omega

def fields (pairs : List ChirpConjugateArray.Pair) : List (List (Fin 2)) := pairs.flatMap fun pair => [pair.1,pair.2]
def publicPairs (pairs : List ChirpConjugateArray.Pair) : List ChirpPublicArray.Pair :=
  pairs.map fun pair => (ChirpPublicDecode.publicWord pair.1,ChirpPublicDecode.publicWord pair.2)

theorem native_format (pairs : List ChirpConjugateArray.Pair) : serialized (fields pairs)=ChirpConjugateArray.native pairs := by
  simp only [serialized,fields,ChirpConjugateArray.native,List.flatMap_assoc,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,DelimitedRadixRecord.complex]

theorem public_format (pairs : List ChirpConjugateArray.Pair) :
    publicBits (fields pairs)=ChirpPublicArray.raw (publicPairs pairs) := by
  simp only [publicBits,fields,publicPairs,ChirpPublicArray.raw,List.flatMap_assoc,List.flatMap_map,
    List.flatMap_cons,List.flatMap_nil,List.append_nil]

/-- The complete actual serializer on complex records, with no supplied field
width or coefficient count. Cost is linear in original native record cells. -/
theorem runs_records (pairs : List ChirpConjugateArray.Pair) :
    HoareTime program
      (· = Copy.tapes (word (ChirpConjugateArray.native pairs)) (fun _ => blank) 0 0)
      (· = Copy.tapes (word (ChirpConjugateArray.native pairs))
        (word ((ChirpPublicArray.raw (publicPairs pairs)).map bitSymbol)) 0 0)
      (12*(ChirpConjugateArray.native pairs).length+6) := by
  simpa only [input,output,native_format,public_format] using runs (fields pairs)

/-- The emitted real/imaginary public words decode to exactly the original
native Gaussian dyadic values. Fixed-width bounds are representation facts,
not initialization or execution premises. -/
theorem record_values (pairs : List ChirpConjugateArray.Pair) (widthPred precision : ℕ)
    (fieldWidths : ∀ pair ∈ pairs,pair.1.length=widthPred+1 ∧ pair.2.length=widthPred+1) :
    (publicPairs pairs).map (fun pair => ButterflySigned.complexValue
      (Spec.SignedRingProduct.compValue pair.1) (Spec.SignedRingProduct.compValue pair.2) precision) =
        pairs.map (ChirpConjugateArray.value widthPred precision) := by
  simp only [publicPairs,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro pair member
  rw [ChirpPublicDecode.public_signed pair.1 widthPred (fieldWidths pair member).1,
    ChirpPublicDecode.public_signed pair.2 widthPred (fieldWidths pair member).2]
  rfl

/-- Every emitted public component is the literal canonical manuscript word
of its actual signed native value, including leading padding and signed minima. -/
theorem publicPairs_compWords (pairs : List ChirpConjugateArray.Pair) (widthPred : ℕ)
    (fieldWidths : ∀ pair ∈ pairs,pair.1.length=widthPred+1 ∧ pair.2.length=widthPred+1) :
    publicPairs pairs=pairs.map (fun pair =>
      (Spec.SignedRingProduct.compWord (widthPred+1) (ButterflySigned.signedValue widthPred pair.1),
        Spec.SignedRingProduct.compWord (widthPred+1) (ButterflySigned.signedValue widthPred pair.2))) := by
  unfold publicPairs
  apply List.map_congr_left
  intro pair member
  rw [ChirpPublicDecode.public_compWord pair.1 widthPred (fieldWidths pair member).1,
    ChirpPublicDecode.public_compWord pair.2 widthPred (fieldWidths pair member).2]

def coefficients {size : ℕ} (real imaginary : Fin size → List (Fin 2)) : List ChirpConjugateArray.Pair :=
  (List.finRange size).map fun index => (real index,imaginary index)

theorem emitted_record {size : ℕ} (widthPred : ℕ) (real imaginary : Fin size → List (Fin 2))
    (realWidth : ∀ index,(real index).length=widthPred+1) (imaginaryWidth : ∀ index,(imaginary index).length=widthPred+1) :
    ChirpPublicArray.raw (publicPairs (coefficients real imaginary)) =
      Spec.SignedRingProduct.record (widthPred+1)
        (fun index => ButterflySigned.signedValue widthPred (real index))
        (fun index => ButterflySigned.signedValue widthPred (imaginary index)) := by
  rw [publicPairs_compWords _ widthPred (by
    intro pair member
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp member
    exact ⟨realWidth index,imaginaryWidth index⟩)]
  simp only [coefficients,ChirpPublicArray.raw,Spec.SignedRingProduct.record,List.flatMap_map]

/-- Actual emission and both rewinds in the exact original public polynomial
format. The original native source is retained; all bit lengths and component
values are those of the physically read numerator words. -/
theorem runs_finite {size : ℕ} (widthPred : ℕ) (real imaginary : Fin size → List (Fin 2))
    (realWidth : ∀ index,(real index).length=widthPred+1) (imaginaryWidth : ∀ index,(imaginary index).length=widthPred+1) :
    HoareTime program
      (· = Copy.tapes (word (ChirpConjugateArray.native (coefficients real imaginary))) (fun _ => blank) 0 0)
      (· = Copy.tapes (word (ChirpConjugateArray.native (coefficients real imaginary)))
        (word ((Spec.SignedRingProduct.record (widthPred+1)
          (fun index => ButterflySigned.signedValue widthPred (real index))
          (fun index => ButterflySigned.signedValue widthPred (imaginary index))).map bitSymbol)) 0 0)
      (12*(ChirpConjugateArray.native (coefficients real imaginary)).length+6) := by
  simpa only [emitted_record widthPred real imaginary realWidth imaginaryWidth] using runs_records (coefficients real imaginary)

end
end IntegerMultBounds.Machine.ChirpPublicEmitStream
