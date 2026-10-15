module

public import IntegerMultBounds.Networks.Circuit
public import Mathlib.Data.BitVec
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.CharP.Two

/-! Binary symbolic masks interpreted against arbitrary stored register values.
XOR replay therefore preserves dirty inputs, without enumerating their values. -/
@[expose] public section
namespace IntegerMultBounds.Networks.BinaryScalarReplay

/-- Interpret the selected input coordinates as a sum in the binary field. -/
def eval {n : ℕ} (mask : BitVec n) (stored : Fin n → ZMod 2) : ZMod 2 :=
  ∑ i, if mask.getLsbD i.val then stored i else 0

@[simp] theorem eval_zero {n : ℕ} (stored : Fin n → ZMod 2) : eval (0 : BitVec n) stored = 0 := by
  simp [eval]

/-- Bitwise XOR represents addition for every assignment of the original inputs. -/
theorem eval_xor {n : ℕ} (a b : BitVec n) (stored : Fin n → ZMod 2) :
    eval (a ^^^ b) stored = eval a stored + eval b stored := by
  rw [eval, eval, eval, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [BitVec.getLsbD_xor]
  cases a.getLsbD i.val <;> cases b.getLsbD i.val <;>
    simp [CharTwo.add_self_eq_zero]

/-- A singleton mask denotes its original register, including arbitrary dirty data. -/
@[simp] theorem eval_singleton {n : ℕ} (i : Fin n) (stored : Fin n → ZMod 2) :
    eval (BitVec.ofNat n (2^i.val)) stored = stored i := by
  simp only [eval, BitVec.getLsbD_ofNat, Nat.testBit_two_pow]
  simp [← Fin.ext_iff]

/-- Folding source masks reads every source from the same pre-update state. -/
theorem eval_fold_xor {n : ℕ} {ι : Type*} (sources : List ι) (state : ι → BitVec n)
    (start : BitVec n) (stored : Fin n → ZMod 2) :
    eval (sources.foldl (fun mask i => mask ^^^ state i) start) stored =
      eval start stored + (sources.map fun i => eval (state i) stored).sum := by
  induction sources generalizing start with
  | nil => simp
  | cons i sources ih => simp [ih, eval_xor, add_assoc]

/-- A symbolic row update agrees with an ordinary scalar circuit gate. -/
theorem eval_row_update {n : ℕ} {ι : Type*} [DecidableEq ι]
    (target : ι) (sources : List ι)
    (state : ι → BitVec n) (stored : Fin n → ZMod 2) :
    (fun i => eval (Function.update state target
      (sources.foldl (fun mask j => mask ^^^ state j) (state target)) i) stored) =
    (Circuit.Gate.mk target (sources.map fun i => (i, (1 : ZMod 2)))).run
      (fun i => eval (state i) stored) := by
  funext i
  by_cases hi : i = target
  · subst i
    simp [Circuit.Gate.run, eval_fold_xor, List.map_map, Function.comp_def]
  · simp [Circuit.Gate.run, Function.update_of_ne hi]

end IntegerMultBounds.Networks.BinaryScalarReplay
