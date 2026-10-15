module

public import IntegerMultBounds.Networks.Certificates.PR589.FullReplay
public import IntegerMultBounds.Networks.Certificates.PR589.Bounds
public import IntegerMultBounds.Networks.Certificates.PR589.EndpointSemantics

/-! Complete literal PR589 scalar word on arbitrary dirty register contents.
This proves scalar semantics only. Frames, rank moments, hosting and tape costs
are separate obligations and no primitive exponent is changed here. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589
open BinaryScalarReplay

/-- Every literal gate reads and writes only the physical 661-register bank. -/
theorem register_bounds (g : RawGate) (hg : g ∈ program) :
    g.target < 661 ∧ ∀ i ∈ g.sources, i < 661 := by
  have h := List.all_eq_true.mp program_bounded g hg
  simpa [RawGate.bounded, List.all_eq_true] using h

/-- Sources and helpers are restored, and each target receives its source. -/
theorem dirty_endpoint (stored : Fin 661 → ZMod 2) (i : Fin 661) :
    Circuit.run (program.map RawGate.toCircuit) (extendInput stored) i.val =
      if hi : 111 ≤ i.val ∧ i.val < 222 then
        stored i + stored ⟨i.val - 111, by omega⟩ else stored i := by
  rw [← eval_start stored, ← eval_replay]
  change eval (replay program (snapshot maskBank refsBefore000) i.val) stored = _
  rw [full_scalar_replay]
  exact eval_finish stored i

/-- Every source is returned unchanged, without zero-input assumptions. -/
theorem sources_restored (stored : Fin 661 → ZMod 2) (i : Fin 111) :
    Circuit.run (program.map RawGate.toCircuit) (extendInput stored) i.val =
      stored ⟨i.val, by omega⟩ := by
  have h := dirty_endpoint stored ⟨i.val, by omega⟩
  simpa only [show ¬(111 ≤ i.val ∧ i.val < 222) by omega, ↓reduceDIte] using h

/-- Every helper is returned with exactly its original arbitrary dirty value. -/
theorem helpers_restored (stored : Fin 661 → ZMod 2) (i : Fin 439) :
    Circuit.run (program.map RawGate.toCircuit) (extendInput stored) (222+i.val) =
      stored ⟨222+i.val, by omega⟩ := by
  have h := dirty_endpoint stored ⟨222+i.val, by omega⟩
  simpa only [show ¬(111 ≤ 222+i.val ∧ 222+i.val < 222) by omega, ↓reduceDIte] using h

/-- Each target gets its original value plus the corresponding original source. -/
theorem targets_added (stored : Fin 661 → ZMod 2) (i : Fin 111) :
    Circuit.run (program.map RawGate.toCircuit) (extendInput stored) (111+i.val) =
      stored ⟨111+i.val, by omega⟩ + stored ⟨i.val, by omega⟩ := by
  have h := dirty_endpoint stored ⟨111+i.val, by omega⟩
  simpa only [show 111 ≤ 111+i.val ∧ 111+i.val < 222 by omega, ↓reduceDIte,
    Nat.add_sub_cancel_left, and_self] using h

end IntegerMultBounds.Networks.Certificates.PR589
