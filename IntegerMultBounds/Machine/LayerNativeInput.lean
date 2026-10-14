module

public import IntegerMultBounds.Machine.LayerNativeRecords
public import IntegerMultBounds.Machine.LayerPolynomialHeaders

@[expose] public section
namespace IntegerMultBounds.Machine.LayerNativeInput
noncomputable section
open Spec.SignedRingProduct (Rec array layerHeader DiskGrid)
open ChirpPublicArray (raw native)
open SharedPlacementAlphabet (setTape)
open RecoverCarryStep (word)
variable {coefficientCount : ℕ}

def publicPairs (width : ℕ) (polynomials : List (Rec coefficientCount)) :=
  polynomials.flatMap fun polynomial => ChirpPublicArray.publicPairs width polynomial.1 polynomial.2

theorem raw_public (width : ℕ) (polynomials : List (Rec coefficientCount)) :
    raw (publicPairs width polynomials)=array width polynomials := by
  induction polynomials with
  | nil => rfl
  | cons polynomial polynomials inductionHypothesis =>
    simp only [publicPairs,List.flatMap_cons,raw,List.flatMap_append,array,List.flatMap_cons] at *
    rw [←ChirpPublicArray.raw_public,inductionHypothesis]
    rfl

theorem pair_widths (width : ℕ) (polynomials : List (Rec coefficientCount)) :
    ∀ pair ∈ publicPairs width polynomials,pair.1.length=width ∧ pair.2.length=width := by
  intro pair member
  obtain ⟨polynomial,_,inRecord⟩ := List.mem_flatMap.mp member
  obtain ⟨coordinate,_,rfl⟩ := List.mem_map.mp inRecord
  simp

def program (roleCount arity : ℕ) := seq (extend (LayerPolynomialHeaders.program (alphabet:=2) roleCount arity) 4)
  LayerNativeRecords.prepare

def prepared (roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (polynomials : List (Rec coefficientCount)) (secondArray thirdArray : List Bool) :=
  (LayerPolynomialHeaders.output (alphabet:=2) roleCount arity precision axes coefficientCount activeCount outerCount suffixCount
    chunkWidth selectedBit wordWidth (array wordWidth polynomials) secondArray thirdArray).append (SharedBank.empty 4 2)

def output (roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (polynomials : List (Rec coefficientCount)) (secondArray thirdArray : List Bool) : Tapes 64 2 :=
  setTape (prepared roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
    polynomials secondArray thirdArray) (63 : Fin 64)
    (putWord (fun _ => blank) 0 (native (publicPairs wordWidth polynomials))) 0

def cost (roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (polynomials : List (Rec coefficientCount)) :=
  LayerPolynomialHeaders.cost roleCount arity precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth+1+
    LayerNativeRecords.cost wordWidth (publicPairs wordWidth polynomials)

theorem runs_public (parameters : Spec.SignedRingProduct.LayerParams) (parametersValid : parameters.Valid)
    (roleCount arity : ℕ) (rolesPositive : 2≤roleCount) (arityPositive : 2≤arity)
    (precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (precisionPositive : 1≤precision)
    (admissible : Spec.SignedRingProduct.LayerAdmissible parameters precision axes coefficientCount activeCount
      outerCount suffixCount chunkWidth selectedBit wordWidth)
    (polynomials : List (Rec coefficientCount)) (secondArray thirdArray : List Bool) :
    HoareTime (program roleCount arity)
      (· = Spec.SignedRingProduct.bank
        (layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
        (array wordWidth polynomials) secondArray thirdArray)
      (· = output roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
        polynomials secondArray thirdArray)
      (cost roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth polynomials) := by
  have reservationRun := hoare_extend_eq
    (LayerPolynomialHeaders.runs_public (alphabet:=2) parameters parametersValid roleCount arity rolesPositive arityPositive
      precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth precisionPositive admissible
      (array wordWidth polynomials) secondArray thirdArray) (SharedBank.empty 4 2)
  have publicInput : (Spec.SignedRingProduct.bank (t:=60) (a:=2)
      (layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
      (array wordWidth polynomials) secondArray thirdArray).append (SharedBank.empty 4 2)=
      Spec.SignedRingProduct.bank (t:=64)
        (layerHeader precision axes coefficientCount activeCount outerCount suffixCount chunkWidth selectedBit wordWidth)
        (array wordWidth polynomials) secondArray thirdArray := by
    apply Placement.Tapes.ext'
    all_goals intro slot; fin_cases slot <;> rfl
  rw [publicInput] at reservationRun
  let caller := prepared roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
    polynomials secondArray thirdArray
  have originalWidth := LayerSelectedBitSetup.output_native_fields (alphabet:=2) precision axes coefficientCount activeCount outerCount suffixCount
    chunkWidth selectedBit wordWidth (array wordWidth polynomials) secondArray thirdArray (8 : Fin 9)
  have retainedWidth := LayerPolynomialHeaders.original_fields (alphabet:=2) roleCount arity precision axes coefficientCount activeCount outerCount
    suffixCount chunkWidth selectedBit wordWidth (array wordWidth polynomials) secondArray thirdArray (14 : Fin 17)
  have widthReady : caller.tape 14=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits wordWidth) := by
    change (LayerPolynomialHeaders.output (alphabet:=2) roleCount arity precision axes coefficientCount activeCount outerCount suffixCount
      chunkWidth selectedBit wordWidth (array wordWidth polynomials) secondArray thirdArray).tape 14=_
    exact retainedWidth.2.trans originalWidth.2
  have widthHead : caller.head 14=1 := by
    change (LayerPolynomialHeaders.output (alphabet:=2) roleCount arity precision axes coefficientCount activeCount outerCount suffixCount
      chunkWidth selectedBit wordWidth (array wordWidth polynomials) secondArray thirdArray).head 14=1
    exact retainedWidth.1.trans originalWidth.1
  have sourceReady : caller.tape 1=word (raw (publicPairs wordWidth polynomials)) := by
    rw [raw_public]
    change Spec.SignedRingProduct.wordAt (array wordWidth polynomials)=word (array wordWidth polynomials)
    exact (putWord_blank_origin _).symm
  have sourceHead : caller.head 1=0 := rfl
  have widthPositive : 0<wordWidth := by
    have widthFits := admissible.2.2.2.2.2.2.2.2.2.2.2.2.1
    omega
  have converted := LayerNativeRecords.runs_prepare caller wordWidth (publicPairs wordWidth polynomials)
    widthPositive (pair_widths _ _) widthReady widthHead sourceReady sourceHead ⟨rfl,rfl⟩ ⟨rfl,rfl⟩ ⟨rfl,rfl⟩ ⟨rfl,rfl⟩
  unfold program output cost prepared
  exact reservationRun.seq converted

theorem native_values (precision width : ℕ) (polynomials : List (Rec coefficientCount))
    (widthFits : precision+2≤width) (diskGrid : ∀ polynomial ∈ polynomials,DiskGrid precision polynomial.1 polynomial.2) :
    (ChirpPublicArray.nativePairs (publicPairs width polynomials)).map (ChirpConjugateArray.value (width-1) precision)=
      polynomials.flatMap (fun polynomial => (List.finRange coefficientCount).map
        (fun coordinate => ButterflySigned.complexValue (polynomial.1 coordinate) (polynomial.2 coordinate) precision)) := by
  have values (polynomial : Rec coefficientCount) (member : polynomial ∈ polynomials) :
      (ChirpPublicArray.nativePairs (ChirpPublicArray.publicPairs width polynomial.1 polynomial.2)).map
        (ChirpConjugateArray.value (width-1) precision)=
      (List.finRange coefficientCount).map
        (fun coordinate => ButterflySigned.complexValue (polynomial.1 coordinate) (polynomial.2 coordinate) precision) := by
    simp only [ChirpPublicArray.nativePairs,ChirpPublicArray.publicPairs,List.map_map,Function.comp_def,ChirpConjugateArray.value]
    apply List.map_congr_left
    intro coordinate _
    rw [ChirpPublicCodec.native_signed _ (width-1) (by simp; omega),
      ChirpPublicCodec.native_signed _ (width-1) (by simp; omega),
      ((diskGrid polynomial member).fits widthFits coordinate).1,((diskGrid polynomial member).fits widthFits coordinate).2]
  simp only [publicPairs,ChirpPublicArray.nativePairs,List.map_flatMap]
  apply List.flatMap_congr
  intro polynomial member
  exact values polynomial member

theorem original_retained (roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth : ℕ)
    (polynomials : List (Rec coefficientCount)) (secondArray thirdArray : List Bool) (slot : Fin 63) :
    (output roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
      polynomials secondArray thirdArray).head (Fin.castAdd 1 slot)=
      (prepared roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
        polynomials secondArray thirdArray).head (Fin.castAdd 1 slot) ∧
      (output roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
        polynomials secondArray thirdArray).tape (Fin.castAdd 1 slot)=
        (prepared roleCount arity precision axes activeCount outerCount suffixCount chunkWidth selectedBit wordWidth
          polynomials secondArray thirdArray).tape (Fin.castAdd 1 slot) := by
  have distinct : (Fin.castAdd 1 slot : Fin 64)≠63 := by
    intro equal
    exact (ne_of_lt (show (Fin.castAdd 1 slot : Fin 64).val<(63 : Fin 64).val from slot.isLt))
      (congrArg Fin.val equal)
  simp only [output,setTape,Function.update_of_ne distinct,and_self]

end
end IntegerMultBounds.Machine.LayerNativeInput
