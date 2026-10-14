module

public import IntegerMultBounds.Machine.ChirpPublicConjugate
public import IntegerMultBounds.Machine.ChirpPublicEmitStream

/-! Public complex conjugation with actual publication and full native-work
reclamation. Header parsing, control generation, native conversion/arithmetic,
public serialization and erasure execute on one fixed complete tape bank. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpPublicPublished
noncomputable section
open ChirpPublicArray (Pair raw nativePairs)
open RecoverCarryStep (word)
open SharedPlacementAlphabet (setTape)
open RecoverWorkspace (atProgram erased)

def emitMap : Fin 2 → Fin 64 := ![58,63]
theorem emitMap_injective : Function.Injective emitMap := by decide

def emitSlots := InjectivePlacement.placement emitMap emitMap_injective (by decide : 2+62=64)

def program := seq (seq (seq ChirpPublicConjugate.program
  (Placement.placed ChirpPublicEmitStream.program emitSlots))
  (atProgram RecoverArrayCleanup.eraseOrigin (56 : Fin 64)))
  (atProgram RecoverArrayCleanup.eraseOrigin (58 : Fin 64))

def resultPairs (pairs : List Pair) := ChirpConjugateArray.resultPairs (nativePairs pairs)
def publicBits (pairs : List Pair) := raw (ChirpPublicEmitStream.publicPairs (resultPairs pairs))

def input (precision size width : ℕ) (pairs : List Pair) := ChirpPublicConjugate.input precision size width pairs

def output (precision size width : ℕ) (pairs : List Pair) :=
  setTape (input precision size width pairs) (63 : Fin 64) (word (publicBits pairs)) 0

def cost (precision size width : ℕ) (pairs : List Pair) :=
  ChirpPublicConjugate.cost precision size width pairs+
    2*(ChirpConjugateArray.native (nativePairs pairs)).length+
    14*(ChirpConjugateArray.native (resultPairs pairs)).length+15

private theorem native_nonblank (pairs : List ChirpConjugateArray.Pair) :
    ∀ symbol ∈ ChirpConjugateArray.native pairs,symbol ≠ (blank : Fin 6) := by
  intro symbol member
  obtain ⟨pair,_,inPair⟩ := List.mem_flatMap.mp member
  simp only [DelimitedRadixRecord.complex,DelimitedRadixRecord.field,List.mem_append,List.mem_singleton] at inPair
  rcases inPair with (realMember | rfl) | (imaginaryMember | rfl)
  · obtain ⟨digit,_,rfl⟩ := List.mem_map.mp realMember
    intro equal
    have values := congrArg Fin.val equal
    change digit.val+4=0 at values
    omega
  · decide
  · obtain ⟨digit,_,rfl⟩ := List.mem_map.mp imaginaryMember
    intro equal
    have values := congrArg Fin.val equal
    change digit.val+4=0 at values
    omega
  · decide

/-- All phases and native-array erasures run on the same actual bank. The
original public source/header and final public output remain at origin; no
native array or precomputed conjugate is supplied to this complete procedure. -/
theorem runs (precision size width : ℕ) (pairs : List Pair)
    (precisionPositive : 1≤precision) (sizePositive : 1≤size) (widthPositive : 1≤width)
    (fieldWidths : ∀ pair ∈ pairs,pair.1.length=width ∧ pair.2.length=width) :
    HoareTime program (· = input precision size width pairs) (· = output precision size width pairs)
      (cost precision size width pairs) := by
  let conjugated := ChirpPublicConjugate.output precision size width pairs
  let emitted := setTape conjugated (63 : Fin 64) (word (publicBits pairs)) 0
  let originalCleared := erased emitted (56 : Fin 64)
  have conjugateRun := ChirpPublicConjugate.runs precision size width pairs precisionPositive sizePositive widthPositive fieldWidths
  have emitReady : Placement.active emitSlots conjugated=
      Copy.tapes (ChirpPublicEmitArray.word (ChirpConjugateArray.native (resultPairs pairs))) (fun _ => blank) 0 0 := by
    rw [emitSlots,InjectivePlacement.active_bank]
    unfold emitMap conjugated ChirpPublicConjugate.output ChirpPublicConjugate.frame ChirpConjugateStream.output
      ChirpConjugateStream.input Tapes.append setTape SharedBank.empty Copy.tapes Copy.cfg Config.tapes
    unfold resultPairs ChirpPublicEmitArray.word
    rw [←ChirpConjugateArray.conjugated_native]
    congr 1 <;> apply List.ofFn_injective <;> rfl
  have emitEndpoint : Placement.replace emitSlots conjugated
      (Copy.tapes (ChirpPublicEmitArray.word (ChirpConjugateArray.native (resultPairs pairs)))
        (ChirpPublicEmitArray.word ((raw (ChirpPublicEmitStream.publicPairs (resultPairs pairs))).map bitSymbol)) 0 0)=emitted := by
    apply InjectivePlacement.replace_eq emitMap emitMap_injective (by decide : 2+62=64) conjugated emitted
    · rw [InjectivePlacement.active_bank]
      unfold emitMap emitted publicBits conjugated ChirpPublicConjugate.output ChirpPublicConjugate.frame
        ChirpConjugateStream.output ChirpConjugateStream.input Tapes.append setTape SharedBank.empty Copy.tapes Copy.cfg Config.tapes
      unfold resultPairs ChirpPublicEmitArray.word
      rw [←ChirpConjugateArray.conjugated_native]
      congr 1 <;> apply List.ofFn_injective <;> rfl
    · intro slot outside
      have notOutput : slot≠63 := by intro equal; exact outside 1 (by simpa [emitMap] using equal.symm)
      simp [emitted,setTape,notOutput]
  have emitRun := InjectivePlacement.hoare_exact (ChirpPublicEmitStream.runs_records (resultPairs pairs))
    emitMap emitMap_injective (by decide : 2+62=64) conjugated emitted emitReady emitEndpoint
  have clearOriginal := RecoverArrayCleanup.erase_origin_at (56 : Fin 64) emitted
    (ChirpConjugateArray.native (nativePairs pairs)) (native_nonblank _) (by
      simp [emitted,conjugated,setTape,ChirpPublicConjugate.output,ChirpConjugateStream.output,ChirpConjugateStream.input,Tapes.append]; rfl)
    (by
      simp [emitted,conjugated,setTape,ChirpPublicConjugate.output,ChirpConjugateStream.output,ChirpConjugateStream.input,Tapes.append]; rfl)
  have clearConjugate := RecoverArrayCleanup.erase_origin_at (58 : Fin 64) originalCleared
    (ChirpConjugateArray.native (resultPairs pairs)) (native_nonblank _) (by
      simp [originalCleared,erased,emitted,conjugated,setTape,ChirpPublicConjugate.output,ChirpConjugateStream.output,Tapes.append]; rfl)
    (by
      simp [originalCleared,erased,emitted,conjugated,setTape,ChirpPublicConjugate.output,ChirpConjugateStream.output,Tapes.append]
      exact congrArg (putWord (fun _ => (blank : Fin 6)) 0) (ChirpConjugateArray.conjugated_native _))
  have endpoint : erased originalCleared (58 : Fin 64)=output precision size width pairs := by
    unfold erased originalCleared emitted conjugated output input ChirpPublicConjugate.input
      ChirpPublicConjugate.output ChirpPublicConjugate.frame ChirpConjugateStream.output ChirpConjugateStream.input
      setTape SharedBank.empty Tapes.append
    apply Placement.Tapes.ext'
    all_goals intro slot; fin_cases slot <;> rfl
  unfold program input
  apply (((conjugateRun.seq emitRun).seq clearOriginal).seq clearConjugate).consequence
    (fun _ ready => ready) (fun _ finished => finished.trans endpoint)
  unfold cost
  omega

theorem workspace_blank (precision size width : ℕ) (pairs : List Pair) (slot : Fin 64)
    (notSource : slot≠61) (notHeader : slot≠62) (notOutput : slot≠63) :
    (output precision size width pairs).tape slot=(fun _ => blank) ∧ (output precision size width pairs).head slot=0 := by
  simp [output,input,ChirpPublicConjugate.input,setTape,SharedBank.empty,notSource,notHeader,notOutput]

/-- The physically published bits are exactly the original public real
numerators followed by negated imaginary numerators, in original order. -/
theorem public_record {size : ℕ} (precision widthPred : ℕ) (real imaginary : Fin size → ℤ)
    (precisionFits : precision+2≤widthPred+1) (diskGrid : Spec.SignedRingProduct.DiskGrid precision real imaginary) :
    publicBits (ChirpPublicArray.publicPairs (widthPred+1) real imaginary)=
      Spec.SignedRingProduct.record (widthPred+1) real (fun index => -imaginary index) := by
  let originals := nativePairs (ChirpPublicArray.publicPairs (widthPred+1) real imaginary)
  have originalWidths : ∀ pair ∈ originals,pair.1.length=widthPred+1 ∧ pair.2.length=widthPred+1 := by
    intro pair member
    obtain ⟨originalPair,originalMember,rfl⟩ := List.mem_map.mp member
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp originalMember
    simp [ChirpPublicCodec.native_length]
  have resultWidths := ChirpConjugateArray.result_widths originals (widthPred+1) originalWidths
  unfold publicBits resultPairs
  rw [ChirpPublicEmitStream.publicPairs_compWords _ widthPred resultWidths]
  simp only [originals,raw,ChirpConjugateArray.resultPairs,nativePairs,ChirpPublicArray.publicPairs,
    List.flatMap_map,List.map_map,Function.comp_def,Spec.SignedRingProduct.record]
  apply congrArg (fun encode => (List.finRange size).flatMap encode)
  funext index
  let sources := ChirpConjugateArray.pairSources
    (ChirpPublicCodec.nativeWord (Spec.SignedRingProduct.compWord (widthPred+1) (real index)),
      ChirpPublicCodec.nativeWord (Spec.SignedRingProduct.compWord (widthPred+1) (imaginary index)))
  have widths : ∀ field,(sources field).length=widthPred+1 := by
    intro field
    dsimp [sources,ChirpConjugateArray.pairSources]
    split_ifs <;> simp [ChirpPublicCodec.native_length]
  have realSigned : ButterflySigned.signedValue widthPred (sources 0)=real index := by
    change ButterflySigned.signedValue widthPred (ChirpPublicCodec.nativeWord
      (Spec.SignedRingProduct.compWord (widthPred+1) (real index)))=real index
    rw [ChirpPublicCodec.native_signed _ widthPred (by simp)]
    exact (diskGrid.fits precisionFits index).1
  have imaginarySigned : ButterflySigned.signedValue widthPred (sources 1)=imaginary index := by
    change ButterflySigned.signedValue widthPred (ChirpPublicCodec.nativeWord
      (Spec.SignedRingProduct.compWord (widthPred+1) (imaginary index)))=imaginary index
    rw [ChirpPublicCodec.native_signed _ widthPred (by simp)]
    exact (diskGrid.fits precisionFits index).2
  have notMinimum : ButterflySigned.signedValue widthPred (sources 1)≠-(2^widthPred : ℕ) := by
    apply ChirpConjugateNumerator.imaginary_not_minimum_of_bound _ widthPred precision precisionFits
    rw [imaginarySigned]
    exact_mod_cast (diskGrid.abs_le index).2
  have realResult : ButterflySigned.signedValue widthPred (ChirpConjugateNumerator.words 0 sources)=real index := by
    have signed := ChirpConjugateNumerator.words_signed 0 sources widthPred widths notMinimum
    simpa only [ChirpConjugateNumerator.numerator,Fin.reduceEq,ite_true,Fin.val_zero,realSigned] using signed
  have imaginaryResult : ButterflySigned.signedValue widthPred (ChirpConjugateNumerator.words 1 sources) = -imaginary index := by
    have signed := ChirpConjugateNumerator.words_signed 1 sources widthPred widths notMinimum
    simpa only [ChirpConjugateNumerator.numerator,Fin.reduceEq,ite_false,Fin.val_one,imaginarySigned] using signed
  rw [realResult,imaginaryResult]

/-- Setup, publication, both native-work erasures and every join are paid by
original public record volume under the original parameter allowances. -/
theorem cost_public_le {size : ℕ} (precision width : ℕ) (real imaginary : Fin size → ℤ)
    (precisionPositive : 1≤precision) (sizePositive : 1≤size) (precisionFits : precision≤width)
    (sizeFits : size<2^precision) :
    cost precision size width (ChirpPublicArray.publicPairs width real imaginary) ≤
      3700*(Spec.SignedRingProduct.record width real imaginary).length := by
  let pairs := ChirpPublicArray.publicPairs width real imaginary
  have widths : ∀ pair ∈ pairs,pair.1.length=width ∧ pair.2.length=width := by
    intro pair member
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp member
    simp
  have nativeWidths : ∀ pair ∈ nativePairs pairs,pair.1.length=width ∧ pair.2.length=width := by
    intro pair member
    obtain ⟨originalPair,originalMember,rfl⟩ := List.mem_map.mp member
    simpa only [ChirpPublicCodec.native_length] using widths originalPair originalMember
  have conjugateLength := ChirpConjugateArray.conjugated_length (nativePairs pairs) width nativeWidths
  rw [ChirpConjugateArray.conjugated_native] at conjugateLength
  have lengths := ChirpPublicArray.stream_lengths pairs width widths
  have nativeBound : (ChirpConjugateArray.native (nativePairs pairs)).length ≤ 2*(raw pairs).length := by
    rw [←ChirpPublicArray.native_format,lengths.1,lengths.2]
    nlinarith [Nat.mul_le_mul_right pairs.length (show 2*(width+1)≤4*width by omega)]
  have originalBound := ChirpPublicConjugate.cost_public_le precision width real imaginary
    precisionPositive sizePositive precisionFits sizeFits
  have sourcePositive : 1≤(Spec.SignedRingProduct.record width real imaginary).length := by
    rw [Spec.SignedRingProduct.length_record]
    nlinarith
  unfold cost resultPairs
  rw [conjugateLength]
  simp only [pairs,ChirpPublicArray.raw_public] at nativeBound ⊢
  omega

/-- The complete literal program publishes the exact public conjugate record
and erases all native/control workspace, with every remaining head at origin. -/
theorem runs_public {size : ℕ} (precision widthPred : ℕ) (real imaginary : Fin size → ℤ)
    (precisionPositive : 1≤precision) (sizePositive : 1≤size) (precisionFits : precision+2≤widthPred+1)
    (sizeFits : size<2^precision) (diskGrid : Spec.SignedRingProduct.DiskGrid precision real imaginary) :
    HoareTime program
      (· = input precision size (widthPred+1) (ChirpPublicArray.publicPairs (widthPred+1) real imaginary))
      (· = setTape (input precision size (widthPred+1) (ChirpPublicArray.publicPairs (widthPred+1) real imaginary))
        (63 : Fin 64) (word (Spec.SignedRingProduct.record (widthPred+1) real (fun index => -imaginary index))) 0)
      (3700*(Spec.SignedRingProduct.record (widthPred+1) real imaginary).length) := by
  have execution := runs precision size (widthPred+1) (ChirpPublicArray.publicPairs (widthPred+1) real imaginary)
    precisionPositive sizePositive (by omega) (by
      intro pair member
      obtain ⟨index,_,rfl⟩ := List.mem_map.mp member
      simp)
  unfold output at execution
  rw [public_record precision widthPred real imaginary precisionFits diskGrid] at execution
  apply execution.consequence (fun _ ready => ready) (fun _ finished => finished)
  exact cost_public_le precision (widthPred+1) real imaginary precisionPositive sizePositive (by omega) sizeFits

end
end IntegerMultBounds.Machine.ChirpPublicPublished
