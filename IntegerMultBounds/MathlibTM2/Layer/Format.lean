module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log
public import IntegerMultBounds.BinaryWords

/-!
# Stream format of layer arrays

A coefficient is a Gaussian integer modulo `2^W`, a pair `GR W` of residues. It is stored as `W`
bit pairs, least significant first, each pair the real bit followed by the imaginary bit. A
record is `r` consecutive coefficients and an array is its records in address order. All
symbols are `bitSymbol`s, so arrays are bit arrays of record width `2 r W`.

`red` reduces a Gaussian integer modulo `2^W`. It is additive and commutes with multiplication
by `i`, conjugation and multiplication by integers, so ring computations on residues track
exact Gaussian-integer computations.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Layer

/-- Gaussian residues modulo `2^W`: real and imaginary parts. -/
abbrev GR (W : ℕ) := ZMod (2 ^ W) × ZMod (2 ^ W)

namespace GR

variable {W : ℕ}

/-- Multiplication by `i`. -/
def mulI (z : GR W) : GR W := (-z.2, z.1)

/-- Complex conjugation. -/
def conj (z : GR W) : GR W := (z.1, -z.2)

/-- Multiplication by the Gaussian integer `a + b i`. -/
def mulG (a b : ℤ) (z : GR W) : GR W := (a * z.1 - b * z.2, a * z.2 + b * z.1)

/-- The doubled forward kernel on a pair: `((1 + i) u + (1 - i) v, (1 - i) u + (1 + i) v)`. -/
def kernel2 (u v : GR W) : GR W × GR W :=
  (mulG 1 1 u + mulG 1 (-1) v, mulG 1 (-1) u + mulG 1 1 v)

end GR

/-- Reduction of a Gaussian integer modulo `2^W`. -/
def red (W : ℕ) (z : GaussianInt) : GR W := ((z.re : ZMod (2 ^ W)), (z.im : ZMod (2 ^ W)))

lemma red_add (W : ℕ) (z w : GaussianInt) : red W (z + w) = red W z + red W w := by
  simp [red]

lemma red_neg (W : ℕ) (z : GaussianInt) : red W (-z) = -red W z := by
  simp [red]

lemma red_mulG (W : ℕ) (a b : ℤ) (z : GaussianInt) :
    red W (⟨a, b⟩ * z) = GR.mulG a b (red W z) := by
  simp [red, GR.mulG, Prod.ext_iff]
  ring

lemma red_star (W : ℕ) (z : GaussianInt) : red W (star z) = GR.conj (red W z) := by
  simp [red, GR.conj]

/-! ### Bits -/

/-! ### Pair symbols -/

/-- The stack symbol of a bit pair (real bit, imaginary bit). -/
def pairSym (A : ℕ) (re im : Bool) : Fin (A + 4) := ⟨(4 + 2 * re.toNat + im.toNat) % (A + 4),
  Nat.mod_lt _ (by omega)⟩

/-- The real bit of a pair symbol. -/
def pairRe {A : ℕ} (x : Fin (A + 4)) : Bool := (x.val - 4) / 2 % 2 = 1

/-- The imaginary bit of a pair symbol. -/
def pairIm {A : ℕ} (x : Fin (A + 4)) : Bool := (x.val - 4) % 2 = 1

lemma pairSym_val {A : ℕ} (hA : 4 ≤ A) (re im : Bool) :
    (pairSym A re im).val = 4 + 2 * re.toNat + im.toNat := by
  simp only [pairSym]
  apply Nat.mod_eq_of_lt
  cases re <;> cases im <;> simp <;> omega

@[simp] lemma pairRe_pairSym {A : ℕ} (hA : 4 ≤ A) (re im : Bool) : pairRe (pairSym A re im) = re := by
  simp only [pairRe, pairSym_val hA]
  cases re <;> cases im <;> simp

@[simp] lemma pairIm_pairSym {A : ℕ} (hA : 4 ≤ A) (re im : Bool) : pairIm (pairSym A re im) = im := by
  simp only [pairIm, pairSym_val hA]
  cases re <;> cases im <;> simp

/-- A coefficient as `W` pair symbols, least significant first. -/
def coeffSyms (A W : ℕ) (z : GR W) : List (Fin (A + 4)) :=
  List.ofFn fun t : Fin W => pairSym A (z.1.val.testBit t) (z.2.val.testBit t)

/-- A record as pair symbols. -/
def recSyms (A W : ℕ) (rec : List (GR W)) : List (Fin (A + 4)) := rec.flatMap (coeffSyms A W)

/-- An array as pair symbols. -/
def arrSyms (A W : ℕ) (arr : List (List (GR W))) : List (Fin (A + 4)) := arr.flatMap (recSyms A W)

@[simp] lemma length_coeffSyms (A W : ℕ) (z : GR W) : (coeffSyms A W z).length = W := by
  simp [coeffSyms]

end IntegerMultBounds.MathlibTM2.Layer
