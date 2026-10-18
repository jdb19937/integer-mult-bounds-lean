module

public import IntegerMultBounds.Networks.Certificates.PR589.Nine.Stage
public import IntegerMultBounds.Networks.FramedCircuit
public import Mathlib.Data.ZMod.Basic

/-!
# Exchange frames on bit streams

A bit stream of the parent is a Boolean function on address pairs, the head address on `inl` and
the tail address on `inr` of `Axis ⊕ Axis`. `along M` composes a stream with the address map of a
matrix `M`; it reverses products (`along_mul`).

`exchangeFrame U` is the frame of a projector `U`: a stream stored in it is the logical stream
composed with `D_U`, the exchange of the `U`-components of the two halves. It is an involution
(`exchangeFrame_symm`). A change from frame `U` to frame `V` composes with `D_U D_V`
(`exchangeFrame_change`); for a nested change this is the partial exchange on `V - U`
(`exchange_change`). A coordinate change on both halves conjugates the frame (`along_conj`).
-/

@[expose] public section

namespace IntegerMultBounds.Networks.Certificates.PR589.Nine

open Matrix

/-- A bit stream on address pairs. -/
abbrev Stream := (Axis ⊕ Axis → ℚ) → ZMod 2

/-- Composition with the address map of `M`. -/
def along (M : Matrix (Axis ⊕ Axis) (Axis ⊕ Axis) ℚ) : Stream →ₗ[ZMod 2] Stream where
  toFun f := fun z => f (M *ᵥ z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem along_apply (M : Matrix (Axis ⊕ Axis) (Axis ⊕ Axis) ℚ) (f : Stream) (z : Axis ⊕ Axis → ℚ) :
    along M f z = f (M *ᵥ z) := rfl

theorem along_one (f : Stream) : along 1 f = f := by
  funext z
  simp [along_apply]

theorem along_mul (M N : Matrix (Axis ⊕ Axis) (Axis ⊕ Axis) ℚ) (f : Stream) :
    along (M * N) f = along N (along M f) := by
  funext z
  simp [along_apply, mulVec_mulVec]

/-- The frame of a projector. -/
def exchangeFrame (U : Matrix Axis Axis ℚ) (hU : U * U = U) : FramedCircuit.Frame (ZMod 2) Stream :=
  LinearEquiv.ofInvolutive (along (exchange U)) fun f => by
    rw [← along_mul, exchange_mul_self hU, along_one]

theorem exchangeFrame_apply (U : Matrix Axis Axis ℚ) (hU : U * U = U) (f : Stream) :
    exchangeFrame U hU f = along (exchange U) f := rfl

theorem exchangeFrame_symm (U : Matrix Axis Axis ℚ) (hU : U * U = U) (f : Stream) :
    (exchangeFrame U hU).symm f = along (exchange U) f := by
  rw [LinearEquiv.symm_apply_eq, exchangeFrame_apply, ← along_mul, exchange_mul_self hU, along_one]

/-- A change from frame `U` to frame `V`. -/
theorem exchangeFrame_change (U V : Matrix Axis Axis ℚ) (hU : U * U = U) (hV : V * V = V)
    (f : Stream) :
    exchangeFrame V hV ((exchangeFrame U hU).symm f) = along (exchange U * exchange V) f := by
  rw [exchangeFrame_symm, exchangeFrame_apply, ← along_mul]

/-- A coordinate change `R` on both halves, with inverse `S`, conjugates an exchange. -/
theorem along_conj (R S U : Matrix Axis Axis ℚ) (h : R * S = 1) (f : Stream) :
    along (fromBlocks S 0 0 S) (along (exchange U) (along (fromBlocks R 0 0 R) f)) =
      along (exchange (R * U * S)) f := by
  rw [← along_mul, ← along_mul, ← Matrix.mul_assoc, exchange_conj R S U h]

end IntegerMultBounds.Networks.Certificates.PR589.Nine
