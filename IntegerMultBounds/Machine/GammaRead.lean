module

public import IntegerMultBounds.Machine.GammaPrefix

/-! Extract an actual self-delimiting gamma code into a raw MSB binary word.
The prefix scanner discovers its width, that ruler copies exactly the value
field, and both work heads are restored. The complete source is preserved and
its cursor advances to the next code, with no supplied width or parsed value. -/

@[expose] public section
namespace IntegerMultBounds.Machine.GammaRead
noncomputable section
variable {alphabet : ℕ}
open RecoverCarryStep (word)
open RecoverRecordField (bank)
open Spec.SignedRingProduct (gamma msbBits length_gamma msbBits_size binaryValue_msbBits)

def program : Program 3 12 alphabet :=
  seq (seq (seq (seq (extend GammaPrefix.program 1)
    (RecoverWorkspace.atProgram ReturnOrigin.program (0 : Fin 3))) RulerCopy.program)
    (RecoverWorkspace.atProgram EraseBack.program (0 : Fin 3)))
    (RecoverWorkspace.atProgram ReturnOrigin.program (2 : Fin 3))

private theorem prefix_bank (ruler source destination : ℤ → Fin (alphabet+4))
    (rulerHead sourceHead destinationHead : ℤ) (state : Fin 2) :
    (GammaPrefix.cfg ruler source rulerHead sourceHead state).tapes.append
      (⟨fun _ => destinationHead,fun _ => destination⟩ : Tapes 1 alphabet) =
        bank ruler source destination rulerHead sourceHead destinationHead := by
  unfold GammaPrefix.cfg Config.tapes Tapes.append bank RulerCopy.cfg
  congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem bits_nonblank (bits : List Bool) :
    ∀ symbol ∈ bits.map (bitSymbol (a := alphabet)), symbol ≠ blank := by
  intro symbol member
  obtain ⟨bit,_,rfl⟩ := List.mem_map.mp member
  cases bit <;> simp [bitSymbol,blank,Fin.ext_iff]

/-- The field width is discovered by executing the scan. All representation
premises concern source cells; neither a prewritten ruler nor a parsed field is
part of the input bank. -/
theorem runs_field (source : ℤ → Fin (alphabet+4)) (sourceHead : ℤ) (zeroCount : ℕ) (field : List Bool)
    (leadingZeros : ∀ index < zeroCount, source (sourceHead+index) = bitSymbol false)
    (firstOne : source (sourceHead+zeroCount) = bitSymbol true)
    (fieldLength : field.length = zeroCount+1)
    (fieldCells : CopyCells.cells source (sourceHead+zeroCount) (zeroCount+1) = field.map bitSymbol) :
    HoareTime (program (alphabet := alphabet))
      (· = bank (fun _ => blank) source (fun _ => blank) 0 sourceHead 0)
      (· = bank (fun _ => blank) source (word field) 0 (sourceHead+zeroCount+(zeroCount+1)) 0)
      (5 * (zeroCount+1) + 10) := by
  have scanned := FamilyPlacementAlphabet.extend_hoare
    (GammaPrefix.prefix_hoare (fun _ => (blank : Fin (alphabet+4))) source 0 sourceHead zeroCount leadingZeros firstOne)
    (⟨fun _ => 0,fun _ => fun _ => blank⟩ : Tapes 1 alphabet)
  rw [prefix_bank,prefix_bank] at scanned
  have rulerWritten : putWord (fun _ => (blank : Fin (alphabet+4))) 0
      (List.replicate (zeroCount+1) (bitSymbol true)) = word (List.replicate (zeroCount+1) true) := by simp [word]
  have rulerPosition : (0 : ℤ)+zeroCount+1 = (zeroCount+1 : ℕ) := by omega
  rw [rulerWritten,rulerPosition] at scanned
  let ruler := word (alphabet := alphabet) (List.replicate (zeroCount+1) true)
  have reset := RecoverWorkspace.return_at (0 : Fin 3)
    (bank ruler source (fun _ => blank) (zeroCount+1) (sourceHead+zeroCount) 0)
    ((List.replicate (zeroCount+1) true).map bitSymbol) (bits_nonblank _) (by
      change (zeroCount+1 : ℤ) = _; simp) rfl
  have resetEndpoint : RecoverWorkspace.restored
      (bank ruler source (fun _ => blank) (zeroCount+1) (sourceHead+zeroCount) 0) (0 : Fin 3) =
        bank ruler source (fun _ => blank) 0 (sourceHead+zeroCount) 0 := by
    unfold RecoverWorkspace.restored SharedPlacementAlphabet.setTape bank RulerCopy.cfg Config.tapes
    congr 1 <;> apply List.ofFn_injective <;> rfl
  rw [resetEndpoint] at reset
  have copied := RulerCopy.copy_hoare (fun _ => (blank : Fin (alphabet+4))) source (fun _ => blank) 0
    (sourceHead+zeroCount) 0 ((List.replicate (zeroCount+1) true).map bitSymbol) (bits_nonblank _) rfl
  simp only [List.length_map,List.length_replicate,zero_add,fieldCells] at copied
  have erased := RecoverWorkspace.erase_at (0 : Fin 3)
    (bank ruler source (word field) (zeroCount+1) (sourceHead+zeroCount+(zeroCount+1)) (zeroCount+1))
    ((List.replicate (zeroCount+1) true).map bitSymbol) (bits_nonblank _)
    (by change (zeroCount+1 : ℤ) = _; simp) rfl
  have erasedEndpoint : RecoverWorkspace.erased
      (bank ruler source (word field) (zeroCount+1) (sourceHead+zeroCount+(zeroCount+1)) (zeroCount+1)) (0 : Fin 3) =
        bank (fun _ => blank) source (word field) 0 (sourceHead+zeroCount+(zeroCount+1)) (zeroCount+1) := by
    unfold RecoverWorkspace.erased SharedPlacementAlphabet.setTape bank RulerCopy.cfg Config.tapes
    congr 1 <;> apply List.ofFn_injective <;> rfl
  rw [erasedEndpoint] at erased
  have returned := RecoverWorkspace.return_at (2 : Fin 3)
    (bank (fun _ => blank) source (word field) 0 (sourceHead+zeroCount+(zeroCount+1)) (zeroCount+1))
    (field.map bitSymbol) (bits_nonblank _) (by change (zeroCount+1 : ℤ) = _; simp [fieldLength]) rfl
  have returnedEndpoint : RecoverWorkspace.restored
      (bank (fun _ => blank) source (word field) 0 (sourceHead+zeroCount+(zeroCount+1)) (zeroCount+1)) (2 : Fin 3) =
        bank (fun _ => blank) source (word field) 0 (sourceHead+zeroCount+(zeroCount+1)) 0 := by
    unfold RecoverWorkspace.restored SharedPlacementAlphabet.setTape bank RulerCopy.cfg Config.tapes
    congr 1 <;> apply List.ofFn_injective <;> rfl
  rw [returnedEndpoint] at returned
  unfold program
  apply ((((scanned.seq reset).seq copied).seq erased).seq returned).consequence (fun _ ready => ready) (fun _ finished => finished)
  simp only [List.length_map,List.length_replicate,fieldLength]
  omega

/-- Read a gamma code at any boundary in an immutable concatenated header.
The output is exactly its binary integer word; the source cursor points to the
following code and the temporary width ruler is fully blank/head zero. -/
theorem runs_gamma (beforeCode suffix : List Bool) (value : ℕ) (valuePositive : 1 ≤ value) :
    HoareTime (program (alphabet := alphabet))
      (· = bank (fun _ => blank) (word (beforeCode ++ gamma value ++ suffix)) (fun _ => blank) 0 beforeCode.length 0)
      (· = bank (fun _ => blank) (word (beforeCode ++ gamma value ++ suffix))
        (word (msbBits (Nat.size value) value)) 0 (beforeCode.length+(gamma value).length) 0)
      (5 * Nat.size value + 10) := by
  let field := msbBits (Nat.size value) value
  let source := word (alphabet := alphabet) (beforeCode ++ gamma value ++ suffix)
  have widthPositive : 0 < Nat.size value := Nat.size_pos.mpr valuePositive
  have zeroView : putWord source beforeCode.length
      ((List.replicate (Nat.size value-1) false).map bitSymbol) = source := by
    have viewed := WordSegments.middle (fun _ => (blank : Fin (alphabet+4))) 0 (beforeCode.map bitSymbol)
      ((List.replicate (Nat.size value-1) false).map bitSymbol) ((field++suffix).map bitSymbol)
    simpa only [source,field,word,gamma,List.map_append,List.length_map,zero_add,List.append_assoc] using viewed
  have fieldView : putWord source ((beforeCode.length : ℤ)+((Nat.size value-1 : ℕ) : ℤ)) (field.map bitSymbol) = source := by
    have viewed := WordSegments.middle (fun _ => (blank : Fin (alphabet+4))) 0
      ((beforeCode++List.replicate (Nat.size value-1) false).map bitSymbol) (field.map bitSymbol) (suffix.map bitSymbol)
    simpa only [source,field,word,gamma,List.map_append,List.length_map,List.length_append,List.length_replicate,
      Nat.cast_add,zero_add,List.append_assoc] using viewed
  have leadingZeros : ∀ index < Nat.size value-1, source ((beforeCode.length : ℤ)+index) = bitSymbol false := by
    intro index bound
    have cell := WordSegments.get source beforeCode.length
      ((List.replicate (Nat.size value-1) false).map (bitSymbol (a := alphabet))) index (by simp; omega)
    rw [zeroView] at cell
    simpa using cell
  have firstOne : source ((beforeCode.length : ℤ)+((Nat.size value-1 : ℕ) : ℤ)) = bitSymbol true := by
    have cell := congrFun fieldView ((beforeCode.length : ℤ)+((Nat.size value-1 : ℕ) : ℤ) : ℤ)
    rw [show field = true :: msbBits (Nat.size value-1) value from msbBits_size valuePositive,
      List.map_cons,putWord_head] at cell
    exact cell.symm
  have fieldCells := CopyCells.cells_putWord source ((beforeCode.length : ℤ)+((Nat.size value-1 : ℕ) : ℤ)) field
  rw [fieldView] at fieldCells
  have fieldLength : field.length = Nat.size value-1+1 := by simp [field]; omega
  have extracted := runs_field source beforeCode.length (Nat.size value-1) field leadingZeros firstOne fieldLength
    (by simpa [fieldLength] using fieldCells)
  have widthEquation : Nat.size value-1+1 = Nat.size value := by omega
  have nextPosition : (beforeCode.length : ℤ)+((Nat.size value-1 : ℕ) : ℤ)+(((Nat.size value-1 : ℕ) : ℤ)+1) =
      beforeCode.length+(gamma value).length := by rw [length_gamma valuePositive]; omega
  rw [nextPosition] at extracted
  simpa only [widthEquation] using extracted

/-- The extracted integer value is the one encoded by the public gamma code. -/
theorem decoded_value (value : ℕ) : binaryValue (msbBits (Nat.size value) value) = value := by
  rw [binaryValue_msbBits,Nat.mod_eq_of_lt (Nat.lt_size_self value)]

end
end IntegerMultBounds.Machine.GammaRead
