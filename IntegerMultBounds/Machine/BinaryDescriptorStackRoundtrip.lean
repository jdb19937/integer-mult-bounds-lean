module

public import IntegerMultBounds.Machine.BinaryDescriptorStack
public import IntegerMultBounds.Machine.Placement
public import IntegerMultBounds.Machine.RadixZeroFill

/-! A concrete push/pop roundtrip on three tapes: preserved source descriptor,
stack, and initially blank restoration destination. -/

@[expose] public section

namespace IntegerMultBounds.Machine.BinaryDescriptorStackRoundtrip
open BinaryDescriptorStack
variable {a : ℕ}

/-- The descriptor representation is exactly the one used by the runtime
binary length-header machinery. -/
theorem descriptor_encoded (xs : List Bool) :
    descriptor (a := a) xs = RadixZeroFill.encodedBinary xs := by
  have hw (f : ℤ → Fin 4) (p : ℤ) (bs : List Bool) :
      putWord (fun z => (RadixToBinary.binaryEncoding (q := a)).encode (f z)) p (bs.map bitSymbol) =
      (fun z => (RadixToBinary.binaryEncoding (q := a)).encode (putBits f p bs z)) := by
    induction bs generalizing p with
    | nil => rfl
    | cons b bs ih =>
      funext z
      by_cases hz : z = p
      · subst z; cases b <;> simp [putWord,putBits,RadixToBinary.binaryEncoding,bitSymbol]
      · simpa [putWord,putBits,hz] using congrFun (ih (p+1)) z
  have he : (fun z => (RadixToBinary.binaryEncoding (q := a)).encode (CountedCopyReuse.empty z)) = empty := by
    funext z
    by_cases hz : z = 0 <;> simp [CountedCopyReuse.empty,empty,hz,RadixToBinary.binaryEncoding,separator,blank]
  have h := hw CountedCopyReuse.empty 1 xs
  rw [he] at h
  exact h

def bank (src stack dst : ℤ → Fin (a+4)) (p q r : ℤ) : Tapes 3 a :=
  ⟨![p,q,r],![src,stack,dst]⟩

def pushSlots : Fin (2+1) ≃ Fin 3 := Equiv.refl _
def popSlots : Fin (2+1) ≃ Fin 3 where
  toFun := ![1,2,0]
  invFun := ![2,0,1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def program : Program 3 16 a :=
  seq (Placement.placed push pushSlots) (Placement.placed pop popSlots)

end IntegerMultBounds.Machine.BinaryDescriptorStackRoundtrip
