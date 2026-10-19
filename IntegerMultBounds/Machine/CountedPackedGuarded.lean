module

public import IntegerMultBounds.Machine.CountedPackedReusable
public import IntegerMultBounds.Compact.ToggleValue

/-! Exact word semantics of the fixed runtime-driven early packed gadget on
its guarded set. The temporary word is restored literally, and the target
word changes only at the selected low bits. The unguarded arithmetic machine
is unchanged; this theorem supplies the guarded contract used by repair. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CountedPackedGuarded
noncomputable section
open Compact Compact.Radix Compact.PowerTwo
open PackedArith

/-- Padding is allowed: equal width and equal value determine a bit word. -/
theorem word_eq_of_length_value (xs ys : List Bool) (hl : xs.length = ys.length)
    (hv : Counter.value xs = Counter.value ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    exact (List.eq_nil_of_length_eq_zero (by simpa using hl.symm)).symm
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have ht : xs.length = ys.length := by simpa using hl
      cases x <;> cases y <;> simp only [Counter.value, Bool.false_eq_true,
        ite_false, ite_true, zero_add] at hv
      · exact congrArg (List.cons false) (ih ys ht (by omega))
      · omega
      · omega
      · exact congrArg (List.cons true) (ih ys ht (by omega))

/-- The literal block words and control bits read by the packed program. -/
def states (q b : ℕ) (V W Z : List Bool) : List DigitState :=
  (List.range Z.length).map fun i =>
    ⟨Counter.value (Gather.field V (i*q) q),
      Counter.value (Gather.field W (i*b) b), ctrl (Z.getD i false)⟩



end
end IntegerMultBounds.Machine.CountedPackedGuarded
