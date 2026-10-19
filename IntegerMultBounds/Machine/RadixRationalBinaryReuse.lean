module

public import IntegerMultBounds.Machine.RadixRationalBinary
public import IntegerMultBounds.Machine.BinaryDescriptorReset

/-! Recurring fixed-rational conversion. The previous binary output is erased
by actual transitions before the next computation, and all radix workspace is
again completely blank afterward. Alphabet lifting touches only binary output. -/

@[expose] public section

namespace IntegerMultBounds.Machine.RadixRationalBinaryReuse

open RadixDigits
variable {q : ℕ}

def input (old : List Bool) (xs : List (Fin q)) : Tapes 4 q :=
  RadixRationalBinary.bank ((RadixToBinary.binaryState q old).tape 0) 1 xs []

private def frame (xs : List (Fin q)) : Tapes 3 q :=
  ⟨![0,0,1],![fun _ => blank,fun _ => blank,RadixRationalBinary.source xs]⟩

/-- Decode/encode only the selected binary tape; radix source is an exact frame. -/
def resetProgram : Program 4 4 q :=
  extend (Alphabet.program (RadixToBinary.binaryEncoding (q := q)) BinaryDescriptorReset.program) 3

private theorem reset_binary (old : List Bool) :
    HoareTime (Alphabet.program (RadixToBinary.binaryEncoding (q := q)) BinaryDescriptorReset.program)
      (fun v => v = RadixToBinary.binaryState q old)
      (fun v => v = MarkedWordCleanup.one (fun _ => blank) 0) (2*old.length+4) := by
  have hh := Alphabet.map_hoare (RadixToBinary.binaryEncoding (q := q)) (BinaryDescriptorReset.reset_hoare old)
  apply hh.consequence _ _ le_rfl
  · intro v hv; exact ⟨_,rfl,hv⟩
  · rintro v ⟨w,rfl,hv⟩; exact hv

private theorem input_frame (old : List Bool) (xs : List (Fin q)) :
    (RadixToBinary.binaryState q old).append (frame xs) = input old xs := by
  unfold Tapes.append frame input RadixRationalBinary.bank
  congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem blank_frame (xs : List (Fin q)) :
    (MarkedWordCleanup.one (fun _ => (blank : Fin (q+4))) 0).append (frame xs) = RadixRationalBinary.input xs := by
  unfold Tapes.append frame MarkedWordCleanup.one RadixRationalBinary.input RadixRationalBinary.bank
  congr 1 <;> apply List.ofFn_injective <;> rfl

theorem reset_hoare (old : List Bool) (xs : List (Fin q)) :
    HoareTime resetProgram (fun v => v = input old xs) (fun v => v = RadixRationalBinary.input xs)
      (2*old.length+4) := by
  have hh := (reset_binary old).extend (frame xs)
  apply hh.consequence _ _ le_rfl
  · intro v hv; exact ⟨_,rfl,by simpa only [input_frame] using hv⟩
  · rintro v ⟨w,rfl,hv⟩; simpa only [blank_frame] using hv

variable [Fact q.Prime]

def program (r : ℚ) : Program 4 (4+((2+(2*r.num.natAbs+r.den+1)+2)+18+6)) q :=
  seq resetProgram (RadixRationalBinary.program r)

/-- Complete recurring computation; no stale binary suffix or radix scratch remains. -/
theorem compute_hoare (r : ℚ) (old : List Bool) (xs : List (Fin q)) :
    HoareTime (program r) (fun v => v = input old xs) (fun v => v = RadixRationalBinary.output r xs)
      (2*old.length+10*value (RadixRationalBinary.result r xs)+10*xs.length+32) := by
  exact ((reset_hoare old xs).seq (RadixRationalBinary.compute_hoare r xs)).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.RadixRationalBinaryReuse
