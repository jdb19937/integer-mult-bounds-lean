module

public import IntegerMultBounds.Machine.GammaHeaderRead
public import IntegerMultBounds.Machine.BinaryDescriptorDivision

/-! Derive the section 8 chunk width from the parsed precision descriptor.
The fixed divisor six is written into blank storage, actual marked division
produces the canonical quotient, and the divisor and every private division
tape are erased. No chunk descriptor is supplied. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverChunkParameter
noncomputable section
variable {alphabet : ℕ}

def sixBits : List Bool := RecursiveChildQuotientsConstant.bits 6

def constantInit := RecoverWorkspace.atProgram
  (RecursiveChildQuotientsConstant.program (a := alphabet) 6) (1 : Fin 12)
def program := seq (seq (constantInit (alphabet := alphabet)) (BinaryDescriptorDivision.program alphabet))
  (BinaryDescriptorCleanupList.oneProgram (a := alphabet) (1 : Fin 12))

def input (precisionBits : List Bool) : Tapes 12 alphabet :=
  SharedPlacementAlphabet.setTape (BinaryDescriptorDivision.input precisionBits sixBits) (1 : Fin 12) (fun _ => blank) 0

def output (precisionBits chunkBits : List Bool) : Tapes 12 alphabet :=
  SharedPlacementAlphabet.setTape (BinaryDescriptorDivision.output precisionBits sixBits chunkBits) (1 : Fin 12) (fun _ => blank) 0

/-- The original precision descriptor is retained at head one, a canonical
chunk descriptor is generated at slot five/head one, and every other tape is
entirely blank/head zero. All input private storage begins genuinely blank. -/
theorem runs_derive (precisionBits : List Bool) :
    ∃ chunkBits : List Bool, GrowingCounterData.Canonical chunkBits ∧
      Counter.value chunkBits = Counter.value precisionBits / 6 ∧ chunkBits.length ≤ precisionBits.length ∧
      HoareTime (program (alphabet := alphabet)) (· = input precisionBits) (· = output precisionBits chunkBits)
        (32 * (precisionBits.length * (4 * precisionBits.length + 48)) + 737) := by
  have sixValue : Counter.value sixBits = 6 := RecursiveChildQuotientsConstant.bits_value 6
  have sixLength : sixBits.length = 3 := by decide
  have initialized := RecoverWorkspace.runs_one_at (RecursiveChildQuotientsConstant.program (a := alphabet) 6)
    (1 : Fin 12) (input (alphabet := alphabet) precisionBits) (fun _ => blank)
    (BinaryDescriptorStack.descriptor sixBits) 0 1 (by simp [input,SharedPlacementAlphabet.setTape])
    (by simp [input,SharedPlacementAlphabet.setTape]) (RecursiveChildQuotientsConstant.initialize_hoare 6)
  have prepared : SharedPlacementAlphabet.setTape (input (alphabet := alphabet) precisionBits) (1 : Fin 12)
      (BinaryDescriptorStack.descriptor sixBits) 1 = BinaryDescriptorDivision.input precisionBits sixBits := by
    unfold input SharedPlacementAlphabet.setTape BinaryDescriptorDivision.input BinaryDescriptorDivisionBoundary.input
      BinaryDescriptorDivisionRaw.bank Tapes.append SharedBank.empty
    congr 1 <;> apply List.ofFn_injective <;> rfl
  rw [prepared] at initialized
  obtain ⟨chunkBits, canonical, quotientValue, quotientWidth, divided⟩ :=
    BinaryDescriptorDivision.divide_hoare (a := alphabet) precisionBits sixBits (by rw [sixValue]; decide)
  have cleared := BinaryDescriptorCleanupList.one_hoare (1 : Fin 12)
    (BinaryDescriptorDivision.output (a := alphabet) precisionBits sixBits chunkBits) sixBits rfl rfl
  refine ⟨chunkBits,canonical,by simpa only [sixValue] using quotientValue,quotientWidth,?_⟩
  unfold program constantInit
  apply ((initialized.seq divided).seq cleared).consequence (fun _ ready => ready) (fun _ finished => finished)
  have divisionBound := BinaryDescriptorDivision.cost_le precisionBits sixBits
  unfold RecursiveChildQuotientsConstant.cost
  have constantLength : (RecursiveChildQuotientsConstant.bits 6).length = 3 := by decide
  simp only [sixLength,constantLength] at divisionBound ⊢
  norm_num at divisionBound ⊢
  have normalized : 4 * precisionBits.length + 18 + 30 = 4 * precisionBits.length + 48 := by omega
  rw [normalized] at divisionBound
  omega

theorem workspace_blank (precisionBits chunkBits : List Bool) (slot : Fin 12)
    (notPrecision : slot ≠ 0) (notChunk : slot ≠ 5) :
    (output (alphabet := alphabet) precisionBits chunkBits).tape slot = (fun _ => blank) ∧
      (output (alphabet := alphabet) precisionBits chunkBits).head slot = 0 := by
  fin_cases slot
  · exact False.elim (notPrecision rfl)
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact False.elim (notChunk rfl)
  all_goals exact ⟨rfl,rfl⟩

/-- At the manuscript precision the physically generated quotient is exactly
its chunk width, with no independent chunk-value hypothesis. -/
theorem chunk_value (precisionBits chunkBits : List Bool) (chunkWidth : ℕ)
    (precisionValue : Counter.value precisionBits = 6 * chunkWidth)
    (quotientValue : Counter.value chunkBits = Counter.value precisionBits / 6) :
    Counter.value chunkBits = chunkWidth := by
  rw [quotientValue,precisionValue]
  omega

end
end IntegerMultBounds.Machine.RecoverChunkParameter
