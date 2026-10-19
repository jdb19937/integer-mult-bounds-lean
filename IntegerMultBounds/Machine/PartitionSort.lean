module

public import IntegerMultBounds.Machine.Partition
public import IntegerMultBounds.Machine.RadixSort

/-! The concrete partition's two output words represent the stable list pass.
This connects the interfaces without assuming that concatenation or selection
of subsequent key bits is free on tapes. -/

@[expose] public section

namespace IntegerMultBounds.Machine.Partition

theorem encode_append (xs ys : List Record) :
    encode (xs ++ ys) = encode xs ++ encode ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encode, ih, List.append_assoc]

theorem buckets_eq_pass (xs : List Record) :
    bucket false xs ++ bucket true xs = encode (RadixSort.pass Record.key xs) := by
  simp only [RadixSort.pass, encode_append, bucket]
  congr 1 <;> congr 1 <;> apply List.filter_congr <;> intro x _ <;> cases x.key <;> rfl

end IntegerMultBounds.Machine.Partition
