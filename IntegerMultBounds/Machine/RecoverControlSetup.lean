module

public import IntegerMultBounds.Machine.RecoverBinaryRuler

/-! Construct all three public recovery rulers on their actual tapes from
binary descriptors. Fixed placements share the three-tape ruler builder;
all consumed descriptor/clock storage is blank at the native handoff. -/

@[expose] public section
namespace IntegerMultBounds.Machine.RecoverControlSetup
noncomputable section
variable {alphabet : ℕ}
open RecoverCarryStep (word)
open SharedPlacementAlphabet (setTape)
open RecoverRecordArray (Pair)

def rulerSlot : Fin 3 → Fin 20 := ![2,8,13]
def clockSlot : Fin 3 → Fin 20 := ![14,16,18]
def descriptorSlot : Fin 3 → Fin 20 := ![15,17,19]

def slots : Fin 3 → Fin (3+17) ≃ Fin 20
  | 0 => {
      toFun := ![2,14,15,0,1,3,4,5,6,7,8,9,10,11,12,13,16,17,18,19]
      invFun := ![3,4,0,5,6,7,8,9,10,11,12,13,14,15,1,2,16,17,18,19]
      left_inv := by decide
      right_inv := by decide }
  | 1 => {
      toFun := ![8,16,17,0,1,2,3,4,5,6,7,9,10,11,12,13,14,15,18,19]
      invFun := ![3,4,5,6,7,8,9,10,0,11,12,13,14,15,16,17,1,2,18,19]
      left_inv := by decide
      right_inv := by decide }
  | 2 => {
      toFun := ![13,18,19,0,1,2,3,4,5,6,7,8,9,10,11,12,14,15,16,17]
      invFun := ![3,4,5,6,7,8,9,10,11,12,13,14,15,0,16,17,18,19,1,2]
      left_inv := by decide
      right_inv := by decide }

def build (field : Fin 3) : Program 20 31 alphabet := Placement.placed RecoverBinaryRuler.program (slots field)
def program : Program 20 93 alphabet := seq (seq (build 0) (build 1)) (build 2)

def built (field : Fin 3) (current : Tapes 20 alphabet) (width : ℕ) : Tapes 20 alphabet :=
  setTape (setTape (setTape current (rulerSlot field) (word (List.replicate width true)) 0)
    (clockSlot field) (fun _ => blank) 0) (descriptorSlot field) (fun _ => blank) 0

private theorem replace_built (field : Fin 3) (current : Tapes 20 alphabet) (width : ℕ) :
    Placement.replace (slots field) current (RecoverBinaryRuler.output width) = built field current width := by
  fin_cases field <;> unfold Placement.replace Placement.combine Placement.extra Tapes.append Tapes.reindex
    slots RecoverBinaryRuler.output built setTape rulerSlot clockSlot descriptorSlot
  all_goals congr 1 <;> apply List.ofFn_injective <;> rfl

/-- Place the same ruler builder into any of the three recovery control slots,
retaining the complete other seventeen-tape bank. -/
theorem build_at (field : Fin 3) (current : Tapes 20 alphabet) (descriptorBits : List Bool) (width : ℕ)
    (descriptorValue : Counter.value descriptorBits = width)
    (activeReady : Placement.active (slots field) current = RecoverBinaryRuler.input descriptorBits) :
    HoareTime (build field) (· = current) (· = built field current width)
      (8 * width + 9 * descriptorBits.length + 31) := by
  have placed := Placement.hoare_at (RecoverBinaryRuler.runs_build descriptorBits width descriptorValue)
    (slots field) current activeReady
  apply placed.consequence (fun _ ready => ready) _ le_rfl
  rintro finalBank ⟨localBank, localReady, finalReady⟩
  rw [localReady] at finalReady
  exact finalReady.trans (replace_built field current width)

def work (chunkBits precisionBits widthBits : List Bool) : Tapes 6 alphabet :=
  ⟨![0,1,0,1,0,1], ![fun _ => blank,CountedLoopReuseAlphabet.binary chunkBits,
    fun _ => blank,CountedLoopReuseAlphabet.binary precisionBits,fun _ => blank,CountedLoopReuseAlphabet.binary widthBits]⟩
def emptyWork : Tapes 6 alphabet := ⟨fun _ => 0,fun _ => fun _ => blank⟩

def input (pairs : List Pair) (chunkBits precisionBits widthBits clock : List Bool) : Tapes 20 alphabet :=
  (setTape (setTape (setTape
    (RecoverPublicOutput.input pairs (Counter.value widthBits) (Counter.value chunkBits) (Counter.value precisionBits) clock)
    (2 : Fin 14) (fun _ => blank) 0) (8 : Fin 14) (fun _ => blank) 0) (13 : Fin 14) (fun _ => blank) 0).append
      (work chunkBits precisionBits widthBits)

def output (pairs : List Pair) (chunkWidth precision wordWidth : ℕ) (clock : List Bool) : Tapes 20 alphabet :=
  (RecoverPublicOutput.input pairs wordWidth chunkWidth precision clock).append emptyWork

/-- Runtime synthesis on the exact recovery bank. The only supplied controls
are three binary descriptors; all initially blank unary rulers are constructed,
all six private controller tapes are erased and their heads return to zero. -/
theorem runs_setup (pairs : List Pair) (chunkBits precisionBits widthBits clock : List Bool)
    (chunkWidth precision wordWidth : ℕ)
    (chunkValue : Counter.value chunkBits = chunkWidth)
    (precisionValue : Counter.value precisionBits = precision)
    (widthValue : Counter.value widthBits = wordWidth) :
    HoareTime (program (alphabet := alphabet)) (· = input pairs chunkBits precisionBits widthBits clock)
      (· = output pairs chunkWidth precision wordWidth clock)
      (8 * (chunkWidth + precision + wordWidth) +
        9 * (chunkBits.length + precisionBits.length + widthBits.length) + 95) := by
  let initial := input (alphabet := alphabet) pairs chunkBits precisionBits widthBits clock
  let first := built (0 : Fin 3) initial chunkWidth
  let second := built (1 : Fin 3) first precision
  have chunkReady : Placement.active (slots 0) initial = RecoverBinaryRuler.input chunkBits := by
    unfold initial input work Placement.active slots RecoverBinaryRuler.input CountedGuardConstantsFill.input
      CountedGuardGadgetPosition.input Tapes.append setTape
    congr 1 <;> apply List.ofFn_injective <;> rfl
  have precisionReady : Placement.active (slots 1) first = RecoverBinaryRuler.input precisionBits := by
    unfold first built initial input work Placement.active slots RecoverBinaryRuler.input CountedGuardConstantsFill.input
      CountedGuardGadgetPosition.input Tapes.append setTape rulerSlot clockSlot descriptorSlot
    congr 1 <;> apply List.ofFn_injective <;> rfl
  have widthReady : Placement.active (slots 2) second = RecoverBinaryRuler.input widthBits := by
    unfold second first built initial input work Placement.active slots RecoverBinaryRuler.input CountedGuardConstantsFill.input
      CountedGuardGadgetPosition.input Tapes.append setTape rulerSlot clockSlot descriptorSlot
    congr 1 <;> apply List.ofFn_injective <;> rfl
  have chunkRun := build_at (0 : Fin 3) initial chunkBits chunkWidth chunkValue chunkReady
  have precisionRun := build_at (1 : Fin 3) first precisionBits precision precisionValue precisionReady
  have widthRun := build_at (2 : Fin 3) second widthBits wordWidth widthValue widthReady
  have endpoint : built (2 : Fin 3) second wordWidth = output pairs chunkWidth precision wordWidth clock := by
    unfold second first built initial input work output emptyWork
    rw [chunkValue,precisionValue,widthValue]
    unfold setTape rulerSlot clockSlot descriptorSlot Tapes.append RecoverPublicOutput.input
      RecoverPublicOutput.controls RecoverPublicOutput.slots Tapes.reindex RecoverRecordReady.input
      RecoverRecordField.bank RulerCopy.cfg Config.tapes
    congr 1 <;> apply List.ofFn_injective <;> rfl
  unfold program
  apply ((chunkRun.seq precisionRun).seq widthRun).consequence (fun _ ready => ready)
    (fun _ finished => finished.trans endpoint)
  omega

end
end IntegerMultBounds.Machine.RecoverControlSetup
