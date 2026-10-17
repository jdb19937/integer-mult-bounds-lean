module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Complex.Basic

/-! The eight-stream data composition of one T16 port in one replica, abstracted over the
operators. A phase event multiplies one stream by `M c` for a coefficient vector
`c : Fin 73 → ZMod 4`, where `M` is any homomorphism from the additive group of coefficient
vectors; for T16 it sends `c` to the commuting product of the coordinate kernels `C_b^{c_b}`.
Shears add an integer multiple of one stream to another, and an exchange sends a pair `(X, Y)` to
`(Y, -X)`. A kernel-evaluable check tracks each stream's frame as a packed coefficient vector and
an integer scalar chain; when it succeeds the whole program is `M target` on every stream. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Streams

/-! ### Packed coefficient vectors -/

/-- A vector in `(ZMod 4)^73`, packed as its low and high bit planes. -/
abbrev Vec := ℕ × ℕ

def Vec.coeff (v : Vec) (k : ℕ) : ZMod 4 :=
  (if v.1.testBit k then 1 else 0) + (if v.2.testBit k then 2 else 0)

def Vec.add (a b : Vec) : Vec := (a.1 ^^^ b.1, a.2 ^^^ b.2 ^^^ (a.1 &&& b.1))

def Vec.neg (a : Vec) : Vec := (a.1, a.2 ^^^ a.1)

def Vec.zero : Vec := (0, 0)

private theorem bits_add (p q r t : Bool) :
    ((if (p ^^ r) = true then 1 else 0) + (if (q ^^ t ^^ (p && r)) = true then 2 else 0) : ZMod 4) =
      ((if p = true then 1 else 0) + (if q = true then 2 else 0)) +
        ((if r = true then 1 else 0) + (if t = true then 2 else 0)) := by
  revert p q r t; decide

private theorem bits_neg (p q : Bool) :
    ((if p = true then 1 else 0) + (if (q ^^ p) = true then 2 else 0) : ZMod 4) =
      -((if p = true then 1 else 0) + (if q = true then 2 else 0)) := by
  revert p q; decide

theorem Vec.coeff_add (a b : Vec) (k : ℕ) : (a.add b).coeff k = a.coeff k + b.coeff k := by
  simp only [Vec.add, Vec.coeff, Nat.testBit_xor, Nat.testBit_land]
  exact bits_add _ _ _ _

theorem Vec.coeff_neg (a : Vec) (k : ℕ) : a.neg.coeff k = -a.coeff k := by
  simp only [Vec.neg, Vec.coeff, Nat.testBit_xor]
  exact bits_neg _ _

theorem Vec.coeff_zero (k : ℕ) : Vec.zero.coeff k = 0 := by simp [Vec.zero, Vec.coeff]

/-- The coefficient function on the 73 coordinates. -/
def Vec.toFun (v : Vec) : Fin 73 → ZMod 4 := fun k => v.coeff k

theorem Vec.toFun_add (a b : Vec) : (a.add b).toFun = a.toFun + b.toFun := by
  funext k; exact Vec.coeff_add a b k

theorem Vec.toFun_neg (a : Vec) : a.neg.toFun = -a.toFun := by
  funext k; exact Vec.coeff_neg a k

theorem Vec.toFun_zero : Vec.zero.toFun = 0 := by
  funext k; exact Vec.coeff_zero k

/-! ### Stream programs -/

def pairX (p : Fin 4) : Fin 8 := ⟨2 * p.val, by omega⟩
def pairY (p : Fin 4) : Fin 8 := ⟨2 * p.val + 1, by omega⟩

theorem pairX_ne_pairY (p : Fin 4) : pairX p ≠ pairY p := by
  intro h; have := congrArg Fin.val h; simp [pairX, pairY] at this

inductive Event where
  | phase (stream : Fin 8) (v : Vec)
  | shear (dst src : Fin 8) (c : ℤ)
  | exchange (pair : Fin 4)

variable {S : Type*} [AddCommGroup S] [Module ℂ S]

/-- The operator of a coefficient vector. -/
abbrev Op (S : Type*) [AddCommGroup S] [Module ℂ S] :=
  Multiplicative (Fin 73 → ZMod 4) →* Module.End ℂ S

def Event.run (M : Op S) : Event → (Fin 8 → S) → (Fin 8 → S)
  | .phase s v, x => Function.update x s (M (Multiplicative.ofAdd v.toFun) (x s))
  | .shear d s c, x => Function.update x d (x d + c • x s)
  | .exchange p, x => Function.update (Function.update x (pairX p) (x (pairY p))) (pairY p)
      (-x (pairX p))

def run (M : Op S) : List Event → (Fin 8 → S) → (Fin 8 → S)
  | [], x => x
  | e :: es, x => run M es (e.run M x)

/-! ### The kernel check -/

/-- Checker state: each stream's current frame and the integer scalar chain. -/
structure CState where
  frame : Fin 8 → Vec
  chain : Fin 8 → Fin 8 → ℤ

def Event.check : Event → CState → Option CState
  | .phase s v, σ => some ⟨Function.update σ.frame s ((σ.frame s).add v), σ.chain⟩
  | .shear d s c, σ =>
    if σ.frame d = σ.frame s then
      some ⟨σ.frame, Function.update σ.chain d (fun j => σ.chain d j + c * σ.chain s j)⟩
    else none
  | .exchange p, σ =>
    some ⟨Function.update (Function.update σ.frame (pairX p) (σ.frame (pairY p))) (pairY p)
        (σ.frame (pairX p)),
      Function.update (Function.update σ.chain (pairX p) (σ.chain (pairY p))) (pairY p)
        (fun j => -σ.chain (pairX p) j)⟩

def checkRun : List Event → CState → Option CState
  | [], σ => some σ
  | e :: es, σ => (e.check σ).bind (checkRun es)

def identityChain : Fin 8 → Fin 8 → ℤ := fun i j => if i = j then 1 else 0

/-- The program is `M target` on every stream, starting from the given frames. -/
def accepts (es : List Event) (start : Fin 8 → Vec) (target : Vec) : Bool :=
  match checkRun es ⟨start, identityChain⟩ with
  | some σ => (List.finRange 8).all fun i =>
      decide (σ.frame i = (start i).add target) &&
        (List.finRange 8).all fun j => decide (σ.chain i j = identityChain i j)
  | none => false

end IntegerMultBounds.Networks.Certificates.T16.Streams
