module

public import IntegerMultBounds.Machine.GammaDescriptorRead

/-! Parse the public three-value gamma header into actual marked binary
control descriptors. One fixed decoder is placed three times; it preserves
all original header cells, discovers each code boundary itself, and erases
both shared parsing tapes after every code. -/

@[expose] public section
namespace IntegerMultBounds.Machine.GammaHeaderRead
noncomputable section
variable {alphabet : ℕ}
open RecoverCarryStep (word)
open Spec.SignedRingProduct (gamma header msbBits)

def bits (value : ℕ) := (msbBits (Nat.size value) value).reverse

def slots : Fin 3 → Fin (4+2) ≃ Fin 6
  | 0 => {
      toFun := ![0,1,2,3,4,5]
      invFun := ![0,1,2,3,4,5]
      left_inv := by decide
      right_inv := by decide }
  | 1 => {
      toFun := ![0,1,2,4,3,5]
      invFun := ![0,1,2,4,3,5]
      left_inv := by decide
      right_inv := by decide }
  | 2 => {
      toFun := ![0,1,2,5,3,4]
      invFun := ![0,1,2,4,5,3]
      left_inv := by decide
      right_inv := by decide }

def read (field : Fin 3) : Program 6 25 alphabet := Placement.placed GammaDescriptorRead.program (slots field)
def program : Program 6 75 alphabet := seq (seq (read 0) (read 1)) (read 2)

def bank (source : ℤ → Fin (alphabet+4)) (sourceHead : ℤ) (first second third : Option ℕ) : Tapes 6 alphabet :=
  ⟨![0,sourceHead,0,(if first.isSome then 1 else 0),(if second.isSome then 1 else 0),(if third.isSome then 1 else 0)],
    ![fun _ => blank,source,fun _ => blank,
      (first.elim (fun _ => blank) (fun value => BinaryDescriptorStack.descriptor (bits value))),
      (second.elim (fun _ => blank) (fun value => BinaryDescriptorStack.descriptor (bits value))),
      (third.elim (fun _ => blank) (fun value => BinaryDescriptorStack.descriptor (bits value)))]⟩

def input (first second third : ℕ) : Tapes 6 alphabet := bank (word (header first second third)) 0 none none none

def output (first second third : ℕ) : Tapes 6 alphabet :=
  bank (word (header first second third)) (header first second third).length (some first) (some second) (some third)

private theorem first_bank (source : ℤ → Fin (alphabet+4)) (sourceHead : ℤ)
    (descriptor : ℤ → Fin (alphabet+4)) (descriptorHead : ℤ) :
    ((GammaDescriptorRead.bank source (fun _ => blank) descriptor sourceHead 0 descriptorHead).append
      (⟨![0,0],![fun _ => blank,fun _ => blank]⟩ : Tapes 2 alphabet)).reindex (slots 0) =
      ⟨![0,sourceHead,0,descriptorHead,0,0],![fun _ => blank,source,fun _ => blank,descriptor,fun _ => blank,fun _ => blank]⟩ := by
  unfold GammaDescriptorRead.bank Tapes.append Tapes.reindex slots
  congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem second_bank (source first descriptor : ℤ → Fin (alphabet+4)) (sourceHead descriptorHead : ℤ) :
    ((GammaDescriptorRead.bank source (fun _ => blank) descriptor sourceHead 0 descriptorHead).append
      (⟨![1,0],![first,fun _ => blank]⟩ : Tapes 2 alphabet)).reindex (slots 1) =
      ⟨![0,sourceHead,0,1,descriptorHead,0],![fun _ => blank,source,fun _ => blank,first,descriptor,fun _ => blank]⟩ := by
  unfold GammaDescriptorRead.bank Tapes.append Tapes.reindex slots
  congr 1 <;> apply List.ofFn_injective <;> rfl

private theorem third_bank (source first second descriptor : ℤ → Fin (alphabet+4)) (sourceHead descriptorHead : ℤ) :
    ((GammaDescriptorRead.bank source (fun _ => blank) descriptor sourceHead 0 descriptorHead).append
      (⟨![1,1],![first,second]⟩ : Tapes 2 alphabet)).reindex (slots 2) =
      ⟨![0,sourceHead,0,1,1,descriptorHead],![fun _ => blank,source,fun _ => blank,first,second,descriptor]⟩ := by
  unfold GammaDescriptorRead.bank Tapes.append Tapes.reindex slots
  congr 1 <;> apply List.ofFn_injective <;> rfl

/-- All three codes are physically read from the public header. No decoded
values, boundaries, widths or initialized private rulers occur in the input. -/
theorem runs_at (beforeCode suffix : List Bool) (first second third : ℕ) (firstPositive : 1 ≤ first)
    (secondPositive : 1 ≤ second) (thirdPositive : 1 ≤ third) :
    HoareTime (program (alphabet := alphabet))
      (· = bank (word (beforeCode ++ header first second third ++ suffix)) beforeCode.length none none none)
      (· = bank (word (beforeCode ++ header first second third ++ suffix))
        (beforeCode.length + (header first second third).length) (some first) (some second) (some third))
      (4 * (header first second third).length + 86) := by
  have firstRead := hoare_place
    (GammaDescriptorRead.runs_gamma (alphabet := alphabet) beforeCode (gamma second++gamma third++suffix) first firstPositive)
    (slots 0) (⟨![0,0],![fun _ => blank,fun _ => blank]⟩ : Tapes 2 alphabet)
  simp only [GammaDescriptorRead.input,GammaDescriptorRead.output] at firstRead
  rw [first_bank,first_bank] at firstRead
  have secondRead := hoare_place
    (GammaDescriptorRead.runs_gamma (alphabet := alphabet) (beforeCode++gamma first) (gamma third++suffix) second secondPositive)
    (slots 1) (⟨![1,0],![BinaryDescriptorStack.descriptor (bits first),fun _ => blank]⟩ : Tapes 2 alphabet)
  simp only [GammaDescriptorRead.input,GammaDescriptorRead.output] at secondRead
  rw [second_bank,second_bank] at secondRead
  have thirdRead := hoare_place
    (GammaDescriptorRead.runs_gamma (alphabet := alphabet) (beforeCode++gamma first++gamma second) suffix third thirdPositive)
    (slots 2) (⟨![1,1],![BinaryDescriptorStack.descriptor (bits first),BinaryDescriptorStack.descriptor (bits second)]⟩ : Tapes 2 alphabet)
  simp only [GammaDescriptorRead.input,GammaDescriptorRead.output] at thirdRead
  rw [third_bank,third_bank] at thirdRead
  simp only [List.length_append,Nat.cast_add,List.append_assoc,add_assoc] at firstRead secondRead thirdRead
  unfold program read bank header bits
  simp only [Option.isSome,Option.elim,Bool.false_eq_true,ite_true,ite_false,List.length_append,Nat.cast_add,List.append_assoc]
  apply ((firstRead.seq secondRead).seq thirdRead).consequence (fun _ ready => ready) (fun _ finished => finished)
  simp only [Spec.SignedRingProduct.length_gamma firstPositive,
    Spec.SignedRingProduct.length_gamma secondPositive,Spec.SignedRingProduct.length_gamma thirdPositive]
  have firstWidth := Nat.size_pos.mpr firstPositive
  have secondWidth := Nat.size_pos.mpr secondPositive
  have thirdWidth := Nat.size_pos.mpr thirdPositive
  omega

theorem runs_header (first second third : ℕ) (firstPositive : 1 ≤ first)
    (secondPositive : 1 ≤ second) (thirdPositive : 1 ≤ third) :
    HoareTime (program (alphabet := alphabet)) (· = input first second third) (· = output first second third)
      (4 * (header first second third).length + 86) := by
  simpa only [List.nil_append,List.append_nil,List.length_nil,Nat.cast_zero,zero_add,input,output] using
    runs_at (alphabet := alphabet) [] [] first second third firstPositive secondPositive thirdPositive

/-- Each controller receives the actual scalar encoded in its header field. -/
theorem decoded_value (value : ℕ) : Counter.value (bits value) = value := GammaDescriptorRead.decoded_value value

theorem bits_canonical (value : ℕ) : GrowingCounterData.Canonical (bits value) := by
  by_cases valueZero : value=0
  · subst value
    exact Or.inl rfl
  · apply Or.inr
    rw [bits,Spec.SignedRingProduct.msbBits_size (by omega : 1≤value)]
    simp

theorem bits_eq_native (value : ℕ) : bits value=RecursiveChildQuotientsConstant.bits value :=
  BinaryCanonicalData.value_injective _ _ (bits_canonical value)
    (RecursiveChildQuotientsConstant.bits_canonical value)
    ((decoded_value value).trans (RecursiveChildQuotientsConstant.bits_value value).symm)

end
end IntegerMultBounds.Machine.GammaHeaderRead
