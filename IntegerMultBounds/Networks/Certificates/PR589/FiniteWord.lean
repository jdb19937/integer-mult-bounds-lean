module

public import IntegerMultBounds.Networks.Certificates.PR589.DirtyEndpoint
public import IntegerMultBounds.Networks.Certificates.PR589.Counts
public import IntegerMultBounds.Networks.BoundedCircuit

/-! The literal PR589 word restricted to its certified 661 physical registers.
The complete instruction list survives; no out-of-range index is defaulted. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589

theorem circuit_bounded : BoundedCircuit.Bounded 661 (program.map RawGate.toCircuit) := by
  intro gate hg
  obtain ⟨g, hmem, rfl⟩ := List.mem_map.mp hg
  obtain ⟨ht, hs⟩ := register_bounds g hmem
  refine ⟨ht, ?_⟩
  intro term hm
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
  exact hs i hi

def finiteWord : Circuit.Program (Fin 661) (ZMod 2) :=
  BoundedCircuit.finiteProgram 661 (program.map RawGate.toCircuit) circuit_bounded

theorem finiteWord_length : finiteWord.length = 5583 := by
  rw [finiteWord, BoundedCircuit.finiteProgram_length, List.length_map, program_length]

/-- The actual finite scalar program works on arbitrary dirty inputs. -/
theorem finite_dirty_endpoint (stored : Fin 661 → ZMod 2) (i : Fin 661) :
    Circuit.run finiteWord stored i =
      if hi : 111 ≤ i.val ∧ i.val < 222 then
        stored i + stored ⟨i.val - 111, by omega⟩ else stored i := by
  have hext : (fun j : Fin 661 => extendInput stored j.val) = stored := by
    funext j
    simp [extendInput, j.isLt]
  have h := congrFun (BoundedCircuit.finiteProgram_run 661
    (program.map RawGate.toCircuit) circuit_bounded (extendInput stored)) i
  rw [hext] at h
  exact h.trans (dirty_endpoint stored i)

end IntegerMultBounds.Networks.Certificates.PR589
