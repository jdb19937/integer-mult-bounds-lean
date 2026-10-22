module

public import IntegerMultBounds.MathlibTM2.M8.Rev.FramedRing

/-! Complementary entrance/exit gauges cancel over the recursive node's coordinate rings. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Rev.Interp
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Global

/-- The side-role gauge identity is uniform in the interpreted coordinate ring. -/
theorem swap_complement {d : Nat} {R : Type} [CommRing R] (I : Interp d R)
    {C : Mat d} (hC : IsFrame C) (a : Addr d R) :
    I.swap C (I.swap (1 - C) a) = I.swap 1 a := by
  simp only [swap]
  rw [exchange_exchange, I.sub hC isFrame_one, I.one, Matrix.mul_sub, Matrix.mul_one,
    I.idem hC, sub_self, smul_zero, sub_zero, add_sub_cancel]

end
end IntegerMultBounds.MathlibTM2.M8.Rev.Interp
