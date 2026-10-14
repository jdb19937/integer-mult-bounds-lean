module

public import IntegerMultBounds.Machine.RecoverPublicOutput
public import IntegerMultBounds.Machine.CountedGuardConstantsFill

/-! Construct one recovery ruler from an actual binary descriptor. The
existing reusable countdown writes one true bit per count, then the ruler is
physically rewound and its consumed descriptor is erased. Only the ruler
remains; no unary output, execution oracle or prepared clock is supplied. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverBinaryRuler
noncomputable section
variable {alphabet : ℕ}
open RecoverCarryStep (word)
open SharedPlacementAlphabet (setTape)

def program : Program 3 31 alphabet :=
  seq (seq (CountedGuardConstantsFill.fill true)
    (RecoverWorkspace.atProgram ReturnOrigin.program (0 : Fin 3)))
    (BinaryDescriptorCleanupList.oneProgram (2 : Fin 3))

def input (descriptorBits : List Bool) : Tapes 3 alphabet :=
  CountedGuardConstantsFill.input (fun _ => blank) 0 descriptorBits

def output (width : ℕ) : Tapes 3 alphabet :=
  ⟨![0,0,0], ![word (List.replicate width true),fun _ => blank,fun _ => blank]⟩

private theorem binary_descriptor (descriptorBits : List Bool) :
    CountedLoopReuseAlphabet.binary (a := alphabet) descriptorBits = BinaryDescriptorStack.descriptor descriptorBits := by
  rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]
  exact CountedLoopReuseAlphabet.encoding_binary descriptorBits |>.symm

/-- Arbitrarily padded descriptors and zero widths are supported. The input
value is physically read by the binary countdown; its bit width is charged,
without a canonical-word assumption. Every consumed control cell is erased. -/
theorem runs_build (descriptorBits : List Bool) (width : ℕ)
    (descriptorValue : Counter.value descriptorBits = width) :
    HoareTime (program (alphabet := alphabet)) (· = input descriptorBits) (· = output width)
      (8 * width + 9 * descriptorBits.length + 31) := by
  have filled := CountedGuardConstantsFill.fills (a := alphabet) true (fun _ => blank) 0 descriptorBits width descriptorValue
  simp only [zero_add, ← List.map_replicate] at filled
  let filledBank := CountedGuardConstantsFill.input (word (alphabet := alphabet) (List.replicate width true)) width descriptorBits
  let returnedBank := RecoverWorkspace.restored filledBank (0 : Fin 3)
  have returned := RecoverWorkspace.return_at (0 : Fin 3) filledBank
    ((List.replicate width true).map bitSymbol) (by
      intro symbol member
      obtain ⟨bit, _, rfl⟩ := List.mem_map.mp member
      cases bit <;> simp [bitSymbol, blank, Fin.ext_iff])
    (by simp [filledBank, CountedGuardConstantsFill.input, CountedGuardGadgetPosition.input]) rfl
  have cleared := BinaryDescriptorCleanupList.one_hoare (2 : Fin 3) returnedBank descriptorBits
    (by simp [returnedBank, RecoverWorkspace.restored, setTape, filledBank, CountedGuardConstantsFill.input,
      CountedGuardGadgetPosition.input]; exact binary_descriptor descriptorBits)
    (by simp [returnedBank, RecoverWorkspace.restored, setTape, filledBank, CountedGuardConstantsFill.input,
      CountedGuardGadgetPosition.input])
  have endpoint : setTape returnedBank (2 : Fin 3) (fun _ => blank) 0 = output (alphabet := alphabet) width := by
    unfold returnedBank RecoverWorkspace.restored filledBank CountedGuardConstantsFill.input
      CountedGuardGadgetPosition.input setTape output
    congr 1 <;> apply List.ofFn_injective <;> rfl
  unfold program
  apply ((filled.seq returned).seq cleared).consequence (fun _ ready => ready) (fun _ finished => finished.trans endpoint)
  simp only [List.length_map, List.length_replicate]
  omega

end
end IntegerMultBounds.Machine.RecoverBinaryRuler
