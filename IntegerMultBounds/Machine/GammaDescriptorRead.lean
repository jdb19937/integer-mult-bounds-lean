module

public import IntegerMultBounds.Machine.RawMsbDescriptor

/-! Read an actual gamma code directly into a marked LSB binary descriptor.
The four-tape machine discovers the value width, extracts and reverses the
field, erases both temporary tapes, and leaves the descriptor at its first bit.
The immutable header cursor advances to the next code. -/

@[expose] public section
namespace IntegerMultBounds.Machine.GammaDescriptorRead
noncomputable section
variable {alphabet : ℕ}
open RecoverCarryStep (word)
open Spec.SignedRingProduct (gamma msbBits)

def slots : Fin (2+2) ≃ Fin 4 where
  toFun := ![2,3,0,1]
  invFun := ![2,3,0,1]
  left_inv := by decide
  right_inv := by decide

def bank (source temporary descriptor : ℤ → Fin (alphabet+4))
    (sourceHead temporaryHead descriptorHead : ℤ) : Tapes 4 alphabet :=
  ⟨![0,sourceHead,temporaryHead,descriptorHead], ![fun _ => blank,source,temporary,descriptor]⟩

def convert : Program 4 13 alphabet := Placement.placed RawMsbDescriptor.program slots
def program : Program 4 25 alphabet := seq (extend GammaRead.program 1) convert

def input (beforeCode suffix : List Bool) (value : ℕ) : Tapes 4 alphabet :=
  bank (word (beforeCode ++ gamma value ++ suffix)) (fun _ => blank) (fun _ => blank) beforeCode.length 0 0

def output (beforeCode suffix : List Bool) (value : ℕ) : Tapes 4 alphabet :=
  bank (word (beforeCode ++ gamma value ++ suffix)) (fun _ => blank)
    (BinaryDescriptorStack.descriptor (msbBits (Nat.size value) value).reverse)
    (beforeCode.length+(gamma value).length) 0 1

private theorem reader_bank (source temporary descriptor : ℤ → Fin (alphabet+4))
    (sourceHead temporaryHead descriptorHead : ℤ) :
    (RecoverRecordField.bank (fun _ => blank) source temporary 0 sourceHead temporaryHead).append
      (⟨fun _ => descriptorHead,fun _ => descriptor⟩ : Tapes 1 alphabet) =
        bank source temporary descriptor sourceHead temporaryHead descriptorHead := by
  unfold RecoverRecordField.bank RulerCopy.cfg Config.tapes Tapes.append bank
  congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem converter_bank (source temporary descriptor : ℤ → Fin (alphabet+4))
    (sourceHead temporaryHead descriptorHead : ℤ) :
    ((Copy.tapes temporary descriptor temporaryHead descriptorHead).append
      (⟨![0,sourceHead], ![fun _ => blank,source]⟩ : Tapes 2 alphabet)).reindex slots =
        bank source temporary descriptor sourceHead temporaryHead descriptorHead := by
  unfold Copy.tapes Copy.cfg Config.tapes Tapes.append Tapes.reindex slots bank
  congr 1 <;> apply List.ofFn_injective <;> rfl

/-- A caller supplies only the encoded gamma source; the machine creates the
marked descriptor from blank storage and clears both parsing work tapes. -/
theorem runs_gamma (beforeCode suffix : List Bool) (value : ℕ) (valuePositive : 1 ≤ value) :
    HoareTime (program (alphabet := alphabet)) (· = input beforeCode suffix value)
      (· = output beforeCode suffix value) (8 * Nat.size value + 24) := by
  have read := FamilyPlacementAlphabet.extend_hoare
    (GammaRead.runs_gamma (alphabet := alphabet) beforeCode suffix value valuePositive)
    (⟨fun _ => 0,fun _ => fun _ => blank⟩ : Tapes 1 alphabet)
  rw [reader_bank,reader_bank] at read
  have converted := hoare_place (RawMsbDescriptor.runs_convert (alphabet := alphabet) (msbBits (Nat.size value) value)) slots
    (⟨![0,beforeCode.length+(gamma value).length],
      ![fun _ => blank,word (beforeCode ++ gamma value ++ suffix)]⟩ : Tapes 2 alphabet)
  rw [converter_bank,converter_bank] at converted
  unfold program convert
  apply (read.seq converted).consequence (fun _ ready => ready) (fun _ finished => finished)
  simp only [Spec.SignedRingProduct.length_msbBits]
  omega

/-- The generated descriptor has the actual integer encoded by the header. -/
theorem decoded_value (value : ℕ) : Counter.value (msbBits (Nat.size value) value).reverse = value := by
  rw [RawMsbDescriptor.converted_value,GammaRead.decoded_value]

/-- The marked representation is exactly the counted controller's format. -/
theorem controller_descriptor (bits : List Bool) :
    BinaryDescriptorStack.descriptor (a := alphabet) bits = CountedLoopReuseAlphabet.binary bits := by
  rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]
  exact CountedLoopReuseAlphabet.encoding_binary bits

end
end IntegerMultBounds.Machine.GammaDescriptorRead
