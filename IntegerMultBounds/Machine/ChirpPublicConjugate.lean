module

public import IntegerMultBounds.Machine.ChirpHeaderWidth
public import IntegerMultBounds.Machine.ChirpPublicArray
public import IntegerMultBounds.Machine.PlacementBankEndpoint

/-! One complete bank derives field width from the original public header,
converts both contiguous MSB components, and produces the exact native
conjugate array. Every private ruler/descriptor/arithmetic tape is cleared;
original header and public source plus both native arrays are ready at origin. -/

@[expose] public section
namespace IntegerMultBounds.Machine.ChirpPublicConjugate
noncomputable section
open SharedPlacementAlphabet (setTape)
open RecoverWorkspace (atProgram erased restored)
open RecoverCarryStep (word)
open ChirpPublicArray (Pair raw native nativePairs)
open Spec.SignedRingProduct (header)

def widthMap : Fin 6 → Fin 64 := ![60,62,0,1,2,3]
theorem widthMap_injective : Function.Injective widthMap := by decide

def widthSlots := InjectivePlacement.placement widthMap widthMap_injective (by decide : 6+58=64)

def arrayMap : Fin 3 → Fin 64 := ![60,61,56]
theorem arrayMap_injective : Function.Injective arrayMap := by decide

def arraySlots := InjectivePlacement.placement arrayMap arrayMap_injective (by decide : 3+61=64)

def program := seq (seq (seq (seq (seq (Placement.placed (ChirpHeaderWidth.program (alphabet := 2)) widthSlots)
  (Placement.placed ChirpPublicArray.program arraySlots))
  (atProgram RecoverArrayCleanup.eraseOrigin (60 : Fin 64)))
  (atProgram ReturnOrigin.program (61 : Fin 64)))
  (atProgram ReturnOrigin.program (56 : Fin 64))) (extend ChirpConjugateStream.program 4)

def input (precision size width : ℕ) (pairs : List Pair) : Tapes 64 2 :=
  setTape (setTape (SharedBank.empty 64 2) 62 (word (header precision size width)) 0) 61 (word (raw pairs)) 0

def frame (precision size width : ℕ) (pairs : List Pair) : Tapes 4 2 :=
  ⟨fun _ => 0,![fun _ => blank,word (raw pairs),word (header precision size width),fun _ => blank]⟩

def output (precision size width : ℕ) (pairs : List Pair) : Tapes 64 2 :=
  (ChirpConjugateStream.output (nativePairs pairs)).append (frame precision size width pairs)

def cost (precision size width : ℕ) (pairs : List Pair) :=
  ChirpHeaderWidth.cost precision size width+31*(raw pairs).length+45*(native pairs).length+2*width+18

private theorem bits_nonblank (bits : List Bool) :
    ∀ symbol ∈ bits.map (bitSymbol (a := 2)),symbol ≠ blank := by
  intro symbol member
  obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
  cases bit <;> simp [bitSymbol,blank,Fin.ext_iff]

private theorem native_nonblank (pairs : List Pair) : ∀ symbol ∈ native pairs,symbol ≠ (blank : Fin 6) := by
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

/-- Read actual public parameters, create all controls, convert all records
and conjugate them on one bank. The original source and header are preserved;
no decoded payload, descriptor, unary ruler or private clock is supplied. -/
theorem runs (precision size width : ℕ) (pairs : List Pair)
    (precisionPositive : 1≤precision) (sizePositive : 1≤size) (widthPositive : 1≤width)
    (fieldWidths : ∀ pair ∈ pairs,pair.1.length=width ∧ pair.2.length=width) :
    HoareTime program (· = input precision size width pairs) (· = output precision size width pairs)
      (cost precision size width pairs) := by
  let initial := input precision size width pairs
  let ruled := setTape initial (60 : Fin 64) (word (List.replicate width true)) 0
  let converted := setTape (setTape ruled (61 : Fin 64) (word (raw pairs)) (raw pairs).length)
    (56 : Fin 64) (putWord (fun _ => blank) 0 (native pairs)) (native pairs).length
  let rulerCleared := erased converted (60 : Fin 64)
  let sourceReturned := restored rulerCleared (61 : Fin 64)
  let nativeReturned := restored sourceReturned (56 : Fin 64)
  have widthReady : Placement.active widthSlots initial=ChirpHeaderWidth.input precision size width := by
    rw [widthSlots,InjectivePlacement.active_bank]
    unfold widthMap initial input setTape SharedBank.empty ChirpHeaderWidth.input
      GammaHeaderRead.input GammaHeaderRead.bank
    congr 1 <;> apply List.ofFn_injective <;> rfl
  have widthRun := Placement.hoare_at (ChirpHeaderWidth.runs_setup (alphabet := 2) precision size width
    precisionPositive sizePositive widthPositive) widthSlots initial widthReady
  have widthEndpoint : Placement.replace widthSlots initial (ChirpHeaderWidth.output precision size width)=ruled := by
    apply InjectivePlacement.replace_eq widthMap widthMap_injective (by decide : 6+58=64) initial ruled
    · rw [InjectivePlacement.active_bank]
      unfold ruled widthMap initial input ChirpHeaderWidth.output setTape SharedBank.empty
      congr 1 <;> apply List.ofFn_injective <;> rfl
    · intro slot outside
      have notRuler : slot≠60 := by
        intro equal
        exact outside 0 (by simpa [widthMap] using equal.symm)
      simp [ruled,setTape,notRuler]
  have widthExact : HoareTime (Placement.placed (ChirpHeaderWidth.program (alphabet := 2)) widthSlots)
      (· = initial) (· = ruled) (ChirpHeaderWidth.cost precision size width) := by
    apply widthRun.consequence (fun _ ready => ready) _ le_rfl
    rintro finalBank ⟨localBank,localReady,finalReady⟩
    rw [localReady] at finalReady
    exact finalReady.trans widthEndpoint
  have arrayReady : Placement.active arraySlots ruled=
      ChirpPublicField.bank (word (List.replicate width true)) (word ([]++raw pairs)) (fun _ => blank) 0 0 0 := by
    rw [arraySlots,InjectivePlacement.active_bank]
    unfold arrayMap ruled initial input setTape SharedBank.empty ChirpPublicField.bank RulerCopy.cfg Config.tapes
    congr 1 <;> apply List.ofFn_injective <;> rfl
  have arrayRun := Placement.hoare_at (ChirpPublicArray.runs_array_volume pairs (List.replicate width true) []
    (fun _ => blank) 0 (by simp only [List.length_replicate]; omega) (by simpa using fieldWidths)) arraySlots ruled arrayReady
  have arrayEndpoint : Placement.replace arraySlots ruled
      (ChirpPublicField.bank (word (List.replicate width true)) (word ([]++raw pairs))
        (putWord (fun _ => blank) 0 (native pairs)) 0 ([]++raw pairs).length (0+(native pairs).length))=converted := by
    simp only [List.nil_append,zero_add]
    apply InjectivePlacement.replace_eq arrayMap arrayMap_injective (by decide : 3+61=64) ruled converted
    · rw [InjectivePlacement.active_bank]
      unfold arrayMap converted ruled initial input ChirpPublicField.bank RulerCopy.cfg Config.tapes setTape SharedBank.empty
      congr 1 <;> apply List.ofFn_injective <;> rfl
    · intro slot outside
      have notSource : slot≠61 := by intro equal; exact outside 1 (by simpa [arrayMap] using equal.symm)
      have notNative : slot≠56 := by intro equal; exact outside 2 (by simpa [arrayMap] using equal.symm)
      simp [converted,setTape,notSource,notNative]
  have arrayExact : HoareTime (Placement.placed ChirpPublicArray.program arraySlots) (· = ruled) (· = converted)
      (30*(raw pairs).length) := by
    apply arrayRun.consequence (fun _ ready => ready) _ le_rfl
    rintro finalBank ⟨localBank,localReady,finalReady⟩
    rw [localReady] at finalReady
    exact finalReady.trans arrayEndpoint
  have clearRuler := RecoverArrayCleanup.erase_origin_at (60 : Fin 64) converted
    ((List.replicate width true).map bitSymbol) (bits_nonblank _) (by simp [converted,ruled,setTape])
    (by simp [converted,ruled,setTape,word])
  have returnSource := RecoverWorkspace.return_at (61 : Fin 64) rulerCleared ((raw pairs).map bitSymbol)
    (bits_nonblank _) (by simp [rulerCleared,erased,converted,setTape,List.length_map])
    (by simp [rulerCleared,erased,converted,setTape]; rfl)
  have returnNative := RecoverWorkspace.return_at (56 : Fin 64) sourceReturned (native pairs) (native_nonblank _)
    (by simp [sourceReturned,restored,rulerCleared,erased,converted,setTape])
    (by simp [sourceReturned,restored,rulerCleared,erased,converted,setTape])
  have ready : nativeReturned=(ChirpConjugateStream.input (nativePairs pairs)).append (frame precision size width pairs) := by
    unfold ChirpConjugateStream.input
    rw [←ChirpPublicArray.native_format]
    unfold nativeReturned sourceReturned restored rulerCleared erased converted ruled initial input
      frame setTape SharedBank.empty Tapes.append
    congr 1 <;> apply List.ofFn_injective <;> rfl
  have nativeWidths : ∀ pair ∈ nativePairs pairs,pair.1.length=width ∧ pair.2.length=width := by
    intro pair member
    obtain ⟨originalPair,originalMember,rfl⟩ := List.mem_map.mp member
    simpa only [ChirpPublicCodec.native_length] using fieldWidths originalPair originalMember
  have conjugateRun := FamilyPlacementAlphabet.extend_hoare
    (ChirpConjugateStream.runs (nativePairs pairs) width nativeWidths) (frame precision size width pairs)
  rw [←ready,←ChirpPublicArray.native_format] at conjugateRun
  unfold program input
  apply (((((widthExact.seq arrayExact).seq clearRuler).seq returnSource).seq returnNative).seq conjugateRun).consequence
    (fun _ ready => ready) (fun _ finished => finished)
  simp only [List.length_map,List.length_replicate]
  unfold cost
  omega

theorem workspace_blank (precision size width : ℕ) (pairs : List Pair) (slot : Fin 64)
    (notNative : slot≠56) (notConjugate : slot≠58) (notSource : slot≠61) (notHeader : slot≠62) :
    (output precision size width pairs).tape slot=(fun _ => blank) ∧ (output precision size width pairs).head slot=0 := by
  fin_cases slot <;> first | contradiction | exact ⟨rfl,rfl⟩

theorem cost_le (precision size width : ℕ) (pairs : List Pair)
    (precisionPositive : 1≤precision) (sizePositive : 1≤size) (widthPositive : 1≤width)
    (fieldWidths : ∀ pair ∈ pairs,pair.1.length=width ∧ pair.2.length=width) :
    cost precision size width pairs ≤ 400*((header precision size width).length+width+(raw pairs).length+1) := by
  have setupBound := ChirpHeaderWidth.cost_le precision size width precisionPositive sizePositive widthPositive
  obtain ⟨rawLength,nativeLength⟩ := ChirpPublicArray.stream_lengths pairs width fieldWidths
  have paddingBound : (native pairs).length≤2*(raw pairs).length := by
    rw [rawLength,nativeLength]
    nlinarith [Nat.mul_le_mul_right pairs.length (show 2*(width+1)≤4*width by omega)]
  unfold cost
  omega

/-- Under the original public size/word-width allowances, header setup and all
conversion/conjugation work are paid by the original contiguous record bits. -/
theorem cost_public_le {size : ℕ} (precision width : ℕ) (real imaginary : Fin size → ℤ)
    (precisionPositive : 1≤precision) (sizePositive : 1≤size) (precisionFits : precision≤width)
    (sizeFits : size<2^precision) :
    cost precision size width (ChirpPublicArray.publicPairs width real imaginary) ≤
      3600*(Spec.SignedRingProduct.record width real imaginary).length := by
  have widthPositive : 1≤width := by omega
  have budget := cost_le precision size width (ChirpPublicArray.publicPairs width real imaginary)
    precisionPositive sizePositive widthPositive (by
      intro pair member
      obtain ⟨index,_,rfl⟩ := List.mem_map.mp member
      simp)
  rw [ChirpPublicArray.raw_public] at budget
  have precisionSize : Nat.size precision≤precision := Nat.size_le.mpr Nat.lt_two_pow_self
  have sizeSize : Nat.size size≤precision := Nat.size_le.mpr sizeFits
  have widthSize : Nat.size width≤width := Nat.size_le.mpr Nat.lt_two_pow_self
  have headerBound : (header precision size width).length≤6*width := by
    simp only [header,List.length_append,Spec.SignedRingProduct.length_gamma precisionPositive,
      Spec.SignedRingProduct.length_gamma sizePositive,Spec.SignedRingProduct.length_gamma widthPositive]
    omega
  have widthPaid : width≤(Spec.SignedRingProduct.record width real imaginary).length := by
    rw [Spec.SignedRingProduct.length_record]
    nlinarith
  have constantPaid : 1≤(Spec.SignedRingProduct.record width real imaginary).length := by omega
  omega

/-- The original disk-grid numerator bounds and word-width slack suffice for
exact public-array conjugation. The native conjugate values are the actual
emitted words, with original precision and no extra rounding error. -/
theorem runs_public {size : ℕ} (precision widthPred : ℕ) (real imaginary : Fin size → ℤ)
    (precisionPositive : 1≤precision) (sizePositive : 1≤size) (precisionFits : precision+2≤widthPred+1)
    (sizeFits : size<2^precision) (diskGrid : Spec.SignedRingProduct.DiskGrid precision real imaginary) :
    HoareTime program
      (· = input precision size (widthPred+1) (ChirpPublicArray.publicPairs (widthPred+1) real imaginary))
      (· = output precision size (widthPred+1) (ChirpPublicArray.publicPairs (widthPred+1) real imaginary))
      (3600*(Spec.SignedRingProduct.record (widthPred+1) real imaginary).length) ∧
      (ChirpConjugateArray.resultPairs (nativePairs (ChirpPublicArray.publicPairs (widthPred+1) real imaginary))).map
        (ChirpConjugateArray.value widthPred precision) =
        (List.finRange size).map (fun index => (starRingEnd ℂ) (ButterflySigned.complexValue (real index) (imaginary index) precision)) := by
  have realBound (index : Fin size) : |real index|≤(2 : ℤ)^precision := by
    have squared := diskGrid index
    have scaleSquare : (2 : ℤ)^(2*precision)=((2 : ℤ)^precision)^2 := by rw [mul_comm,pow_mul]
    rw [scaleSquare] at squared
    nlinarith [sq_nonneg (imaginary index),sq_abs (real index),abs_nonneg (real index),show 0≤(2 : ℤ)^precision by positivity]
  have imaginaryBound (index : Fin size) : |imaginary index|≤(2 : ℤ)^precision := by
    have squared := diskGrid index
    have scaleSquare : (2 : ℤ)^(2*precision)=((2 : ℤ)^precision)^2 := by rw [mul_comm,pow_mul]
    rw [scaleSquare] at squared
    nlinarith [sq_nonneg (real index),sq_abs (imaginary index),abs_nonneg (imaginary index),show 0≤(2 : ℤ)^precision by positivity]
  have scaleFits : (2 : ℤ)^precision<(2 : ℤ)^widthPred := by
    exact_mod_cast Nat.pow_lt_pow_right (by decide : 1<2) (show precision<widthPred by omega)
  have realLower (index : Fin size) : -(2 : ℤ)^widthPred≤real index := by have bounded := abs_le.mp (realBound index); omega
  have realUpper (index : Fin size) : real index<(2 : ℤ)^widthPred := by have bounded := abs_le.mp (realBound index); omega
  have imaginaryLower (index : Fin size) : -(2 : ℤ)^widthPred≤ imaginary index := by have bounded := abs_le.mp (imaginaryBound index); omega
  have imaginaryUpper (index : Fin size) : imaginary index<(2 : ℤ)^widthPred := by have bounded := abs_le.mp (imaginaryBound index); omega
  have fieldWidths : ∀ pair ∈ ChirpPublicArray.publicPairs (widthPred+1) real imaginary,
      pair.1.length=widthPred+1 ∧ pair.2.length=widthPred+1 := by
    intro pair member
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp member
    simp
  have execution := runs precision size (widthPred+1) (ChirpPublicArray.publicPairs (widthPred+1) real imaginary)
    precisionPositive sizePositive (by omega) fieldWidths
  refine ⟨execution.consequence (fun _ ready => ready) (fun _ finished => finished)
    (cost_public_le precision (widthPred+1) real imaginary precisionPositive sizePositive (by omega) sizeFits),?_⟩
  have nativeWidths : ∀ pair ∈ nativePairs (ChirpPublicArray.publicPairs (widthPred+1) real imaginary),
      pair.1.length=widthPred+1 ∧ pair.2.length=widthPred+1 := by
    intro pair member
    obtain ⟨originalPair,originalMember,rfl⟩ := List.mem_map.mp member
    simpa only [ChirpPublicCodec.native_length] using fieldWidths originalPair originalMember
  have notMinimum : ∀ pair ∈ nativePairs (ChirpPublicArray.publicPairs (widthPred+1) real imaginary),
      ButterflySigned.signedValue widthPred pair.2≠-(2^widthPred : ℕ) := by
    intro pair member
    obtain ⟨originalPair,originalMember,rfl⟩ := List.mem_map.mp member
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp originalMember
    rw [ChirpPublicCodec.native_compWord widthPred (imaginary index) (imaginaryLower index) (imaginaryUpper index)]
    have bounded := abs_le.mp (imaginaryBound index)
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    omega
  rw [ChirpConjugateArray.result_values _ widthPred precision nativeWidths notMinimum]
  have originalValues := ChirpPublicArray.native_values_public widthPred precision real imaginary
    realLower realUpper imaginaryLower imaginaryUpper
  have mapped := congrArg (List.map (starRingEnd ℂ)) originalValues
  simpa only [List.map_map,Function.comp_def] using mapped

end
end IntegerMultBounds.Machine.ChirpPublicConjugate
