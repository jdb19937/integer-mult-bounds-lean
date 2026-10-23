module

public import IntegerMultBounds.MathlibTM2.Routing.DescriptorBatch

/-! Descriptor outputs lie in an arbitrary core bank. Each table has a binary
width and selector input; all tables share twelve archive/compiler tapes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

def descriptorCore {N J : ℕ} (i : Fin N) : Fin (N + (2 * J + 12)) := ⟨i.val, by omega⟩

def descriptorAux {N J : ℕ} (i : Fin (2 * J + 12)) : Fin (N + (2 * J + 12)) :=
  ⟨N + i.val, by omega⟩

theorem descriptorCore_injective {N J : ℕ} : Function.Injective (descriptorCore (N := N) (J := J)) := by
  intro i j he
  exact Fin.ext (congrArg (fun x : Fin (N + (2 * J + 12)) => x.val) he)

theorem descriptorCore_aux {N J : ℕ} (i : Fin N) (j : Fin (2 * J + 12)) :
    descriptorCore i ≠ descriptorAux j := by
  intro he
  have hv := congrArg Fin.val he
  have hi := i.isLt
  simp only [descriptorCore, descriptorAux] at hv
  omega

def descriptorBankReg {N J : ℕ} (j : Fin J) : BinaryMaskReg → Fin (N + (2 * J + 12))
  | .width => descriptorAux ⟨j.val, by omega⟩
  | .source => descriptorAux ⟨2 * J + 1, by omega⟩
  | .low => descriptorAux ⟨2 * J + 2, by omega⟩
  | .high => descriptorAux ⟨2 * J + 3, by omega⟩
  | .dst => descriptorAux ⟨2 * J + 4, by omega⟩
  | .scratch i => descriptorAux ⟨2 * J + 5 + i.val, by omega⟩

def descriptorBankSelectors {N J : ℕ} (j : Fin J) : Fin (N + (2 * J + 12)) :=
  descriptorAux ⟨J + j.val, by omega⟩

def descriptorBankSaved {N J : ℕ} : Fin (N + (2 * J + 12)) := descriptorAux ⟨2 * J, by omega⟩

theorem descriptorBankReg_injective {N J : ℕ} (j : Fin J) :
    Function.Injective (descriptorBankReg (N := N) j) := by
  intro r s he
  have hv := congrArg Fin.val he
  have hj := j.isLt
  cases r <;> cases s <;> simp only [descriptorBankReg, descriptorAux] at hv
  all_goals first | rfl | (exfalso; omega) | (congr 1; apply Fin.ext; omega)

theorem descriptorBankSelectors_reg {N J : ℕ} (j : Fin J) (r : BinaryMaskReg) :
    descriptorBankSelectors (N := N) j ≠ descriptorBankReg j r := by
  intro he
  have hv := congrArg Fin.val he
  have hj := j.isLt
  cases r <;> simp only [descriptorBankSelectors, descriptorBankReg, descriptorAux] at hv <;> omega

theorem descriptorBankSaved_reg {N J : ℕ} (j : Fin J) (r : BinaryMaskReg) :
    descriptorBankSaved (N := N) (J := J) ≠ descriptorBankReg j r := by
  intro he
  have hv := congrArg Fin.val he
  have hj := j.isLt
  cases r <;> simp only [descriptorBankSaved, descriptorBankReg, descriptorAux] at hv <;> omega

theorem descriptorBankSelectors_saved {N J : ℕ} (j : Fin J) :
    descriptorBankSelectors (N := N) j ≠ descriptorBankSaved := by
  intro he
  have hv := congrArg Fin.val he
  have hj := j.isLt
  simp only [descriptorBankSelectors, descriptorBankSaved, descriptorAux] at hv
  omega

theorem descriptorCore_reg {N J : ℕ} (i : Fin N) (j : Fin J) (r : BinaryMaskReg) :
    descriptorCore i ≠ descriptorBankReg (N := N) j r := by
  cases r <;> exact descriptorCore_aux i _

end IntegerMultBounds.MathlibTM2.Routing
