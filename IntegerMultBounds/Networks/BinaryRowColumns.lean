module

public import IntegerMultBounds.Networks.BinaryRowProgram

/-! Literal Boolean row additions on any number of columns implement the
same fixed binary basis word in each column. The XOR action is connected to
the F2 coordinate semantics; no field-operation oracle is used here. -/

@[expose] public section

namespace IntegerMultBounds.Networks.BinaryRowColumns
open Module BinaryRowProgram
variable {ι κ : Type*} [DecidableEq ι]

def scalar (b : Bool) : ZMod 2 := if b then 1 else 0

def bit (z : ZMod 2) : Bool := decide (z=1)

@[simp] theorem scalar_xor (b c : Bool) : scalar (xor b c)=scalar b+scalar c := by
  cases b <;> cases c <;> decide

@[simp] theorem bit_scalar (b : Bool) : bit (scalar b)=b := by cases b <;> decide

@[simp] theorem scalar_bit (z : ZMod 2) : scalar (bit z)=z := by
  have h : z=0 ∨ z=1 := by
    fin_cases z
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases h with rfl | rfl <;> decide

theorem scalar_injective : Function.Injective scalar := by
  intro b c h
  simpa only [bit_scalar] using congrArg bit h

def execute (op : Op ι) (x : κ → ι → Bool) : κ → ι → Bool :=
  fun column => Function.update (x column) op.target (xor (x column op.target) (x column op.source))

def run (word : List (Op ι)) (x : κ → ι → Bool) : κ → ι → Bool :=
  word.foldl (fun x op => execute op x) x

def coordinates (x : κ → ι → Bool) (column : κ) : ι → ZMod 2 :=
  fun i => scalar (x column i)

theorem run_append (u v : List (Op ι)) (x : κ → ι → Bool) :
    run (u++v) x=run v (run u x) := List.foldl_append

section Basis
variable [Fintype ι] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

/-- Store each vector's coordinates as literal Boolean address bits. -/
noncomputable def encode (b : Basis ι (ZMod 2) E) (x : κ → E) : κ → ι → Bool :=
  fun column i => bit (b.equivFun (x column) i)

omit [DecidableEq ι] in
@[simp] theorem encode_coordinates (b : Basis ι (ZMod 2) E) (x : κ → E) (column : κ) :
    coordinates (encode b x) column=b.equivFun (x column) := by
  funext i
  exact scalar_bit _

end Basis
end IntegerMultBounds.Networks.BinaryRowColumns
