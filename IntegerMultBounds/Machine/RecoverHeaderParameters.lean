module

public import IntegerMultBounds.Machine.RecoverResidualPrecision

/-! One fixed bank reads the public precision/size/word-width gamma header,
then derives the chunk-width descriptor by actual division of the parsed
precision. Parsing and division share blank private storage; no decoded header
or chunk descriptor is supplied, and every private tape is cleared afterward. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverHeaderParameters
noncomputable section
variable {alphabet : ℕ}
open RecoverCarryStep (word)
open Spec.SignedRingProduct (header)

def divisionSlots : Fin (12+5) ≃ Fin 17 where
  toFun := ![3,6,7,8,9,10,11,12,13,14,15,16,0,1,2,4,5]
  invFun := ![12,13,14,0,15,16,1,2,3,4,5,6,7,8,9,10,11]
  left_inv := by decide
  right_inv := by decide

def program := seq (extend (GammaHeaderRead.program (alphabet := alphabet)) 11)
  (Placement.placed (RecoverChunkParameter.program (alphabet := alphabet)) divisionSlots)

def input (precision size wordWidth : ℕ) : Tapes 17 alphabet :=
  (GammaHeaderRead.input precision size wordWidth).append (SharedBank.empty 11 alphabet)

def frame (precision size wordWidth : ℕ) : Tapes 5 alphabet :=
  ⟨![0,(header precision size wordWidth).length,0,1,1],
    ![fun _ => blank,word (header precision size wordWidth),fun _ => blank,
      BinaryDescriptorStack.descriptor (GammaHeaderRead.bits size),BinaryDescriptorStack.descriptor (GammaHeaderRead.bits wordWidth)]⟩

def output (precision size wordWidth : ℕ) (chunkBits : List Bool) : Tapes 17 alphabet :=
  ((RecoverChunkParameter.output (GammaHeaderRead.bits precision) chunkBits).append (frame precision size wordWidth)).reindex divisionSlots

private theorem prepared_bank (precision size wordWidth : ℕ) :
    ((RecoverChunkParameter.input (alphabet := alphabet) (GammaHeaderRead.bits precision)).append
      (frame precision size wordWidth)).reindex divisionSlots =
      (GammaHeaderRead.output precision size wordWidth).append (SharedBank.empty 11 alphabet) := by
  unfold RecoverChunkParameter.input SharedPlacementAlphabet.setTape BinaryDescriptorDivision.input
    BinaryDescriptorDivisionBoundary.input BinaryDescriptorDivisionRaw.bank frame Tapes.append Tapes.reindex
    divisionSlots GammaHeaderRead.output GammaHeaderRead.bank SharedBank.empty
  congr 1 <;> apply List.ofFn_injective <;> rfl

/-- Actual parsing and derived chunk calculation execute on the same bank.
The three original fields become marked binary descriptors at slots three,
four and five; the canonical chunk quotient is produced at slot ten. -/
theorem runs_prepare (precision size wordWidth : ℕ) (precisionPositive : 1 ≤ precision)
    (sizePositive : 1 ≤ size) (widthPositive : 1 ≤ wordWidth) :
    ∃ chunkBits : List Bool, GrowingCounterData.Canonical chunkBits ∧
      Counter.value chunkBits = precision / 6 ∧ chunkBits.length ≤ Nat.size precision ∧
      HoareTime (program (alphabet := alphabet)) (· = input precision size wordWidth)
        (· = output precision size wordWidth chunkBits)
        (4 * (header precision size wordWidth).length +
          32 * (Nat.size precision * (4 * Nat.size precision + 48)) + 824) := by
  have parsed := FamilyPlacementAlphabet.extend_hoare
    (GammaHeaderRead.runs_header (alphabet := alphabet) precision size wordWidth precisionPositive sizePositive widthPositive)
    (SharedBank.empty 11 alphabet)
  obtain ⟨chunkBits,canonical,chunkValue,chunkWidth,calculated⟩ := RecoverChunkParameter.runs_derive (alphabet := alphabet)
    (GammaHeaderRead.bits precision)
  have derived := hoare_place calculated divisionSlots (frame (alphabet := alphabet) precision size wordWidth)
  rw [prepared_bank] at derived
  refine ⟨chunkBits,canonical,?_,?_,?_⟩
  · simpa only [GammaHeaderRead.decoded_value] using chunkValue
  · simpa only [GammaHeaderRead.bits,List.length_reverse,Spec.SignedRingProduct.length_msbBits] using chunkWidth
  · unfold program
    apply (parsed.seq derived).consequence (fun _ ready => ready) (fun _ finished => finished)
    simp only [GammaHeaderRead.bits,List.length_reverse,Spec.SignedRingProduct.length_msbBits]
    omega

/-- Every private parsing/division tape is entirely blank with a zero head;
only the retained header and the four produced descriptors survive. -/
theorem workspace_blank (precision size wordWidth : ℕ) (chunkBits : List Bool) (slot : Fin 17)
    (notHeader : slot ≠ 1) (notPrecision : slot ≠ 3) (notSize : slot ≠ 4)
    (notWidth : slot ≠ 5) (notChunk : slot ≠ 10) :
    (output (alphabet := alphabet) precision size wordWidth chunkBits).tape slot = (fun _ => blank) ∧
      (output (alphabet := alphabet) precision size wordWidth chunkBits).head slot = 0 := by
  fin_cases slot
  · exact ⟨rfl,rfl⟩
  · exact False.elim (notHeader rfl)
  · exact ⟨rfl,rfl⟩
  · exact False.elim (notPrecision rfl)
  · exact False.elim (notSize rfl)
  · exact False.elim (notWidth rfl)
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact False.elim (notChunk rfl)
  all_goals exact ⟨rfl,rfl⟩

/-- The parsed precision `6k` supplies exactly the native chunk width `k`. -/
theorem chunk_value (precision chunkWidth : ℕ) (chunkBits : List Bool)
    (precisionEquation : precision = 6 * chunkWidth) (quotientValue : Counter.value chunkBits = precision / 6) :
    Counter.value chunkBits = chunkWidth := by
  rw [quotientValue,precisionEquation]
  omega

end
end IntegerMultBounds.Machine.RecoverHeaderParameters
