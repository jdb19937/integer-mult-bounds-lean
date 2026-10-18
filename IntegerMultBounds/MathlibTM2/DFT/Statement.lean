module

public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Size

/-!
# The discrete Fourier transform over a prime field below `n log n`: the statement

Everything in this file except a few short definitions is Mathlib vocabulary. The machine
model is Mathlib's `Turing.FinTM2`, as for integer multiplication
(`IntegerMultBounds.MathlibTM2.Statement`).

An instance is a prime `p`, a primitive `n`-th root of unity `ω` in `ZMod p` and a vector
`a : Fin n → ZMod p`. The transform is `(dft ω a) k = ∑ j, a j * ω ^ (j * k)`. Numbers are
written over Mathlib's alphabet `Γ'` in binary, least significant bit first, each followed by a
comma. The input is `p`, then `ω`, then the entries of `a`, each in exactly `Nat.size p` digits
(`encodeFixed`), so an instance of length `N` has `N = (n + 2) (Nat.size p + 1)`. The output is
the entries of `dft ω a`, each in its shortest binary form (`encodeNat`). The time function
bounds the number of steps on every instance of input length `N`.

The fixed width matters: with shortest forms on input, the vector `(0, 1, 0, …, 0)` at a
generator `ω` of `(ZMod p)ˣ` has input length about `p` and output length about `p log p`, and a
machine needs at least one step per output symbol.
-/

@[expose] public section

open Turing Computability Asymptotics Filter

namespace IntegerMultBounds.MathlibTM2.DFT

/-- `x` in exactly `w` binary digits over `Γ'`, least significant first. -/
def encodeFixed (w x : ℕ) : List Γ' := List.ofFn fun i : Fin w => Γ'.bit (x.testBit i)

/-- A list of naturals over `Γ'`, each in exactly `w` binary digits and followed by a comma. -/
def encodeFixedList (w : ℕ) (l : List ℕ) : List Γ' :=
  l.flatMap fun x => encodeFixed w x ++ [Γ'.comma]

/-- A list of naturals over Mathlib's alphabet `Γ'`: each number in binary, least significant
bit first (`encodeNat`), followed by a comma. -/
def encodeNatList (l : List ℕ) : List Γ' :=
  l.flatMap fun x => (encodeNat x).map inclusionBoolΓ' ++ [Γ'.comma]

/-- The discrete Fourier transform over `ZMod p` at `ω`. -/
def dft {p n : ℕ} (ω : ZMod p) (a : Fin n → ZMod p) (k : Fin n) : ZMod p :=
  ∑ j, a j * ω ^ ((j : ℕ) * k)

/-- A prime field, a primitive `n`-th root of unity in it, and a vector of length `n`. -/
structure DFTInstance where
  p : ℕ
  [prime : Fact p.Prime]
  n : ℕ
  ω : ZMod p
  primitive : IsPrimitiveRoot ω n
  a : Fin n → ZMod p

/-- The input: `p`, then `ω`, then the entries of `a`, as canonical representatives in
`Nat.size p` digits each. -/
def DFTInstance.encode (x : DFTInstance) : List Γ' :=
  encodeFixedList (Nat.size x.p) (x.p :: x.ω.val :: List.ofFn fun j => (x.a j).val)

/-- The output: the entries of the transform, as canonical representatives. -/
def DFTInstance.transform (x : DFTInstance) : List ℕ :=
  List.ofFn fun k => (dft x.ω x.a k).val

/-- A fixed finite multi-stack machine computes the discrete Fourier transform of every
instance in worst-case time `O(N (log N) ^ (1 - κ))`, where `N` is the input length. -/
def DFTInTime (κ : ℝ) : Prop :=
  ∃ M : TM2ComputableInTime DFTInstance.encode encodeNatList DFTInstance.transform,
    (fun N : ℕ => (M.time N : ℝ)) =O[atTop] fun N : ℕ => (N : ℝ) * Real.log N ^ (1 - κ)

/-- The discrete Fourier transform over prime fields below `n log n` on multitape Turing
machines. -/
def DFTStatement : Prop := ∃ κ : ℝ, 0 < κ ∧ DFTInTime κ

example : encodeFixedList 3 [6, 1] =
    [.bit false, .bit true, .bit true, .comma, .bit true, .bit false, .bit false, .comma] := by
  decide

example : encodeNatList [6, 1] =
    [.bit false, .bit true, .bit true, .comma, .bit true, .comma] := by decide

example : (List.ofFn fun k => (dft (2 : ZMod 5) ![1, 1, 0, 0] k).val) = [2, 3, 0, 4] := by
  decide

end IntegerMultBounds.MathlibTM2.DFT
