module

public import IntegerMultBounds.Machine.RecoverHeaderParameters

/-! Read public recovery parameters and construct all four unary controls on
one bank. The binary countdowns share cleared work storage; the exponent is
read from the actual power-of-two size descriptor. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverHeaderRulers
noncomputable section
variable {alphabet : ℕ}
open RecoverCarryStep (word)
open SharedPlacementAlphabet (setTape)
open Spec.SignedRingProduct (header)

def rulerSlot : Fin 3 → Fin 20 := ![18,17,19]
def descriptorSlot : Fin 3 → Fin 20 := ![10,3,5]

def rulerSlots0 : Fin (3+17) ≃ Fin 20 where
  toFun := ![18,6,10,0,1,2,3,4,5,7,8,9,11,12,13,14,15,16,17,19]
  invFun := ![3,4,5,6,7,8,1,9,10,11,2,12,13,14,15,16,17,18,0,19]
  left_inv := by decide
  right_inv := by decide

def rulerSlots1 : Fin (3+17) ≃ Fin 20 where
  toFun := ![17,6,3,0,1,2,4,5,7,8,9,10,11,12,13,14,15,16,18,19]
  invFun := ![3,4,5,2,6,7,1,8,9,10,11,12,13,14,15,16,17,0,18,19]
  left_inv := by decide
  right_inv := by decide

def rulerSlots2 : Fin (3+17) ≃ Fin 20 where
  toFun := ![19,6,5,0,1,2,3,4,7,8,9,10,11,12,13,14,15,16,17,18]
  invFun := ![3,4,5,6,7,2,1,8,9,10,11,12,13,14,15,16,17,18,19,0]
  left_inv := by decide
  right_inv := by decide

def rulerSlots : Fin 3 → Fin (3+17) ≃ Fin 20
  | 0 => rulerSlots0
  | 1 => rulerSlots1
  | 2 => rulerSlots2

def exponentSlots : Fin (4+16) ≃ Fin 20 where
  toFun := ![0,4,6,7,1,2,3,5,8,9,10,11,12,13,14,15,16,17,18,19]
  invFun := ![0,4,5,6,1,7,2,3,8,9,10,11,12,13,14,15,16,17,18,19]
  left_inv := by decide
  right_inv := by decide


def build (field : Fin 3) : Program 20 31 alphabet :=
  Placement.placed RecoverBinaryRuler.program (rulerSlots field)

def built (field : Fin 3) (current : Tapes 20 alphabet) (width : ℕ) : Tapes 20 alphabet :=
  setTape (setTape (setTape current (rulerSlot field) (word (List.replicate width true)) 0)
    (6 : Fin 20) (fun _ => blank) 0) (descriptorSlot field) (fun _ => blank) 0

private theorem binary_descriptor (descriptorBits : List Bool) :
    CountedLoopReuseAlphabet.binary (a := alphabet) descriptorBits = BinaryDescriptorStack.descriptor descriptorBits := by
  rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]
  exact CountedLoopReuseAlphabet.encoding_binary descriptorBits |>.symm

private theorem replace_built (field : Fin 3) (current : Tapes 20 alphabet) (width : ℕ) :
    Placement.replace (rulerSlots field) current (RecoverBinaryRuler.output width) = built field current width := by
  fin_cases field <;> unfold Placement.replace Placement.combine Placement.extra Tapes.append Tapes.reindex
    rulerSlots rulerSlots0 rulerSlots1 rulerSlots2 RecoverBinaryRuler.output built setTape rulerSlot descriptorSlot
  all_goals congr 1 <;> apply List.ofFn_injective <;> rfl

theorem build_at (field : Fin 3) (current : Tapes 20 alphabet) (descriptorBits : List Bool) (width : ℕ)
    (descriptorValue : Counter.value descriptorBits = width)
    (activeReady : Placement.active (rulerSlots field) current = RecoverBinaryRuler.input descriptorBits) :
    HoareTime (build field) (· = current) (· = built field current width)
      (8 * width + 9 * descriptorBits.length + 31) := by
  have placed := Placement.hoare_at (RecoverBinaryRuler.runs_build descriptorBits width descriptorValue)
    (rulerSlots field) current activeReady
  apply placed.consequence (fun _ ready => ready) _ le_rfl
  rintro finalBank ⟨localBank, localReady, finalReady⟩
  rw [localReady] at finalReady
  exact finalReady.trans (replace_built field current width)

def program := seq (seq (seq (seq (extend (RecoverHeaderParameters.program (alphabet := alphabet)) 3)
  (build 0)) (build 1)) (build 2)) (Placement.placed RecoverExponentRuler.program exponentSlots)

def input (precision lengthExponent wordWidth : ℕ) : Tapes 20 alphabet :=
  (RecoverHeaderParameters.input precision (2 ^ lengthExponent) wordWidth).append (SharedBank.empty 3 alphabet)

def output (precision lengthExponent wordWidth chunkWidth : ℕ) : Tapes 20 alphabet :=
  ⟨![0,(header precision (2 ^ lengthExponent) wordWidth).length,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![word (List.replicate lengthExponent true),word (header precision (2 ^ lengthExponent) wordWidth),
      fun _ => blank,fun _ => blank,BinaryDescriptorStack.descriptor (GammaHeaderRead.bits (2 ^ lengthExponent)),
      fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,
      fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,
      word (List.replicate precision true),word (List.replicate chunkWidth true),word (List.replicate wordWidth true)]⟩

def cost (precision lengthExponent wordWidth : ℕ) :=
  4 * (header precision (2 ^ lengthExponent) wordWidth).length +
  32 * (Nat.size precision * (4 * Nat.size precision + 48)) +
  8 * (precision / 6 + precision + wordWidth) +
  9 * (2 * Nat.size precision + Nat.size wordWidth) + 10 * lengthExponent + 989

/-- Actual public gamma codes supply every ruler. No binary descriptor,
unary control or private clock is supplied. Parsing, division, all three
countdowns and exponent extraction run on the same twenty-tape bank. -/
theorem runs_setup (precision lengthExponent wordWidth : ℕ)
    (precisionPositive : 1 ≤ precision) (widthPositive : 1 ≤ wordWidth) :
    HoareTime (program (alphabet := alphabet)) (· = input precision lengthExponent wordWidth)
      (· = output precision lengthExponent wordWidth (precision / 6))
      (cost precision lengthExponent wordWidth) := by
  obtain ⟨chunkBits,canonical,chunkValue,chunkLength,prepared⟩ := RecoverHeaderParameters.runs_prepare
    (alphabet := alphabet) precision (2 ^ lengthExponent) wordWidth precisionPositive (by have sizePositive := Nat.two_pow_pos lengthExponent; omega) widthPositive
  have parsed := FamilyPlacementAlphabet.extend_hoare prepared (SharedBank.empty 3 alphabet)
  let initial := (RecoverHeaderParameters.output (alphabet := alphabet) precision (2 ^ lengthExponent) wordWidth chunkBits).append
    (SharedBank.empty 3 alphabet)
  let first := built (0 : Fin 3) initial (precision / 6)
  let second := built (1 : Fin 3) first precision
  let third := built (2 : Fin 3) second wordWidth
  have chunkReady : Placement.active (rulerSlots 0) initial = RecoverBinaryRuler.input chunkBits := by
    simp only [RecoverBinaryRuler.input,CountedGuardConstantsFill.input,CountedGuardGadgetPosition.input,binary_descriptor]
    unfold initial Placement.active rulerSlots rulerSlots0 RecoverHeaderParameters.output RecoverHeaderParameters.frame
      RecoverHeaderParameters.divisionSlots RecoverChunkParameter.output BinaryDescriptorDivision.output
      BinaryDescriptorDivision.retained BinaryDescriptorDivisionRaw.bank Tapes.append Tapes.reindex SharedBank.empty
    congr 1 <;> apply List.ofFn_injective <;> rfl
  have precisionReady : Placement.active (rulerSlots 1) first = RecoverBinaryRuler.input (GammaHeaderRead.bits precision) := by
    simp only [RecoverBinaryRuler.input,CountedGuardConstantsFill.input,CountedGuardGadgetPosition.input,binary_descriptor]
    unfold first built initial Placement.active rulerSlots rulerSlots1 RecoverHeaderParameters.output RecoverHeaderParameters.frame
      RecoverHeaderParameters.divisionSlots RecoverChunkParameter.output BinaryDescriptorDivision.output
      BinaryDescriptorDivision.retained BinaryDescriptorDivisionRaw.bank Tapes.append Tapes.reindex SharedBank.empty
      setTape rulerSlot descriptorSlot
    congr 1 <;> apply List.ofFn_injective <;> rfl
  have widthReady : Placement.active (rulerSlots 2) second = RecoverBinaryRuler.input (GammaHeaderRead.bits wordWidth) := by
    simp only [RecoverBinaryRuler.input,CountedGuardConstantsFill.input,CountedGuardGadgetPosition.input,binary_descriptor]
    unfold second first built initial Placement.active rulerSlots rulerSlots2 RecoverHeaderParameters.output RecoverHeaderParameters.frame
      RecoverHeaderParameters.divisionSlots RecoverChunkParameter.output BinaryDescriptorDivision.output
      BinaryDescriptorDivision.retained BinaryDescriptorDivisionRaw.bank Tapes.append Tapes.reindex SharedBank.empty
      setTape rulerSlot descriptorSlot
    congr 1 <;> apply List.ofFn_injective <;> rfl
  have exponentReady : Placement.active exponentSlots third = RecoverExponentRuler.input lengthExponent := by
    unfold third second first built initial Placement.active exponentSlots RecoverHeaderParameters.output RecoverHeaderParameters.frame
      RecoverHeaderParameters.divisionSlots RecoverChunkParameter.output BinaryDescriptorDivision.output
      BinaryDescriptorDivision.retained BinaryDescriptorDivisionRaw.bank Tapes.append Tapes.reindex SharedBank.empty
      RecoverExponentRuler.input RecoverExponentRuler.bank RecoverExponentRuler.sizeBits setTape rulerSlot descriptorSlot
    congr 1 <;> apply List.ofFn_injective <;> rfl
  have chunkRun := build_at (0 : Fin 3) initial chunkBits (precision / 6) chunkValue chunkReady
  have precisionRun := build_at (1 : Fin 3) first (GammaHeaderRead.bits precision) precision
    (GammaHeaderRead.decoded_value precision) precisionReady
  have widthRun := build_at (2 : Fin 3) second (GammaHeaderRead.bits wordWidth) wordWidth
    (GammaHeaderRead.decoded_value wordWidth) widthReady
  have exponentRun := Placement.hoare_at (RecoverExponentRuler.runs_derive (alphabet := alphabet) lengthExponent)
    exponentSlots third exponentReady
  have endpoint : Placement.replace exponentSlots third (RecoverExponentRuler.output lengthExponent) =
      output precision lengthExponent wordWidth (precision / 6) := by
    unfold Placement.replace Placement.combine Placement.extra exponentSlots third second first built initial
      RecoverHeaderParameters.output RecoverHeaderParameters.frame RecoverHeaderParameters.divisionSlots
      RecoverChunkParameter.output BinaryDescriptorDivision.output BinaryDescriptorDivision.retained BinaryDescriptorDivisionRaw.bank Tapes.append Tapes.reindex SharedBank.empty setTape rulerSlot descriptorSlot
      RecoverExponentRuler.output RecoverExponentRuler.bank RecoverExponentRuler.sizeBits output
    congr 1 <;> apply List.ofFn_injective <;> rfl
  have exponentExact := exponentRun.consequence (fun _ ready => ready) (by
    rintro finalBank ⟨localBank,localReady,finalReady⟩
    rw [localReady] at finalReady
    exact finalReady.trans endpoint) le_rfl
  unfold program input
  apply ((((parsed.seq chunkRun).seq precisionRun).seq widthRun).seq exponentExact).consequence
    (fun _ ready => ready) (fun _ finished => finished)
  simp only [GammaHeaderRead.bits,List.length_reverse,Spec.SignedRingProduct.length_msbBits]
  unfold cost
  omega

end
end IntegerMultBounds.Machine.RecoverHeaderRulers
