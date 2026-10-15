module

public import IntegerMultBounds.Networks.Certificates.PR589.EndpointMasks
public import IntegerMultBounds.Networks.Certificates.PR589.Semantics

/-! Interpretation of the checked initial and final masks against arbitrary
661-register dirty inputs. Full execution is connected separately. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589
open BinaryScalarReplay

def extendInput (stored : Fin 661 → ZMod 2) (i : ℕ) : ZMod 2 :=
  if hi : i < 661 then stored ⟨i, hi⟩ else 0

theorem eval_start (stored : Fin 661 → ZMod 2) :
    (fun i => eval (snapshot maskBank refsBefore000 i) stored) = extendInput stored := by
  funext i
  by_cases hi : i < 661
  · rw [initial_mask_rows ⟨i, hi⟩]
    simpa [extendInput, hi] using eval_initial stored ⟨i, hi⟩
  · simp only [snapshot, ite_eq_right hi, extendInput, dite_eq_right hi]
    exact eval_zero stored

theorem eval_finish (stored : Fin 661 → ZMod 2) (i : Fin 661) :
    eval (snapshot maskBank refsAfter234 i.val) stored =
      if hi : 111 ≤ i.val ∧ i.val < 222 then
        stored i + stored ⟨i.val - 111, by omega⟩ else stored i := by
  rw [final_mask_rows]
  split_ifs with hi
  · rw [eval_xor, eval_initial]
    exact congrArg (fun z => stored i + z)
      (eval_singleton ⟨i.val - 111, by omega⟩ stored)
  · exact eval_initial stored i

end IntegerMultBounds.Networks.Certificates.PR589
