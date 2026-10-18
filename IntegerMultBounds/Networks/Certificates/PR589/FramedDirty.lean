module

public import IntegerMultBounds.Networks.Certificates.PR589.Framed
public import IntegerMultBounds.Networks.Certificates.PR589.DirtyEndpoint

/-! The framed dirty endpoint of the selected PR589 word. Sources and helpers are returned and
each target receives its source, all in their final frames. `selected_dirty` uses the selected
rational E8 shear frames `Geometry.frame` on `Geometry.Stream`. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Certificates.PR589.Framed

open Frames (initialRefs finalRefs)

variable {Ω : Type*}

/-- Framed dirty endpoint: sources and helpers are returned and each target receives its
source, all in their final frames. -/
theorem execute_dirty (frameOf : ℕ → FramedCircuit.Frame (ZMod 2) (Ω → ZMod 2))
    (stored : Fin 661 → Ω → ZMod 2) (i : Fin 661) :
    execute frameOf (FramedCircuit.encode (fun j => frameOf (Frames.snapshot initialRefs j))
        (Copy.extendStored stored)) i.val =
      frameOf (finalRefs i.val)
        (if hi : 111 ≤ i.val ∧ i.val < 222 then stored i + stored ⟨i.val - 111, by omega⟩
          else stored i) := by
  rw [execute_endpoint]
  simp only [FramedCircuit.encode, Frames.snapshot, i.isLt, if_true]
  refine congrArg (frameOf (finalRefs i.val)) ?_
  funext ω
  rw [FramedCircuit.moduleRun_pointwise]
  have h : (fun j => Copy.extendStored stored j ω) = extendInput (fun j => stored j ω) := by
    funext j
    by_cases hj : j < 661 <;> simp [Copy.extendStored, extendInput, hj]
  rw [h, dirty_endpoint]
  split <;> simp

/-- The selected word with the selected rational E8 shear frames, on arbitrary dirty streams. -/
theorem selected_dirty (stored : Fin 661 → Geometry.Stream) (i : Fin 661) :
    execute Geometry.frame (FramedCircuit.encode (fun j => Geometry.frame (Frames.snapshot initialRefs j))
        (Copy.extendStored stored)) i.val =
      Geometry.frame (finalRefs i.val)
        (if hi : 111 ≤ i.val ∧ i.val < 222 then stored i + stored ⟨i.val - 111, by omega⟩
          else stored i) :=
  execute_dirty Geometry.frame stored i

end IntegerMultBounds.Networks.Certificates.PR589.Framed
