module

public import IntegerMultBounds.MathlibTM2.Routing.ClassifierPair

/-! Sixteen auxiliary tapes hold binary dimensions and a shared classifier
workspace. The two generated masks occupy their existing core destinations. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

def classifierCore {N : ℕ} (i : Fin N) : Fin (N + 16) := ⟨i.val, by omega⟩
def classifierAux {N : ℕ} (i : Fin 16) : Fin (N + 16) := ⟨N + i.val, by omega⟩

theorem classifierCore_injective {N : ℕ} : Function.Injective (classifierCore (N := N)) := by
  intro i j he
  apply Fin.ext
  exact congrArg (fun x : Fin (N + 16) => x.val) he

theorem classifierAux_injective {N : ℕ} : Function.Injective (classifierAux (N := N)) := by
  intro i j he
  apply Fin.ext
  have hv := congrArg Fin.val he
  simp only [classifierAux] at hv
  omega

theorem classifierCore_aux {N : ℕ} (i : Fin N) (j : Fin 16) : classifierCore i ≠ classifierAux j := by
  intro he
  have hv := congrArg Fin.val he
  have hi := i.isLt
  simp only [classifierCore, classifierAux] at hv
  omega

def classifierBlockIndex : PhaseBlockReg → Fin 16
  | .width => 0
  | .run => 1
  | .bin => 2
  | .low => 3
  | .high => 4
  | .dst => 5
  | .work => 6
  | .scratch i => ⟨7 + i.val, by omega⟩

theorem classifierBlockIndex_lt (r : PhaseBlockReg) : (classifierBlockIndex r).val < 10 := by
  cases r <;> simp [classifierBlockIndex]; omega

theorem classifierBlockIndex_injective : Function.Injective classifierBlockIndex := by
  intro r s he
  have hv := congrArg Fin.val he
  cases r <;> cases s <;> simp only [classifierBlockIndex] at hv
  all_goals first | rfl | (exfalso; omega) | (congr 1; apply Fin.ext; omega)

def classifierBankReg {N : ℕ} (r : PhaseBlockReg) : Fin (N + 16) := classifierAux (classifierBlockIndex r)

theorem classifierBankReg_injective {N : ℕ} : Function.Injective (classifierBankReg (N := N)) :=
  classifierAux_injective.comp classifierBlockIndex_injective

def classifierBankRepeat {N : ℕ} (temporary phase : Fin N) (i : Fin 5) : Fin (N + 16) :=
  if i = 3 then classifierCore temporary else
    if i = 4 then classifierCore phase else classifierAux ⟨10 + i.val, by omega⟩

def classifierBankPad {N : ℕ} (i : Fin 3) : Fin (N + 16) := classifierAux ⟨13 + i.val, by omega⟩

theorem classifierBankRepeat_injective {N : ℕ} (temporary phase : Fin N) (hne : temporary ≠ phase) :
    Function.Injective (classifierBankRepeat temporary phase) := by
  intro i j he
  fin_cases i <;> fin_cases j <;>
    simp_all [classifierBankRepeat, classifierCore_injective.eq_iff,
      classifierAux_injective.eq_iff, classifierCore_aux, Ne.symm]

theorem classifierBankRepeat_separate {N : ℕ} (temporary phase : Fin N) (i : Fin 5) (r : PhaseBlockReg) :
    classifierBankRepeat temporary phase i ≠ classifierBankReg r := by
  have hr := classifierBlockIndex_lt r
  fin_cases i <;> dsimp [classifierBankRepeat, classifierBankReg]
  all_goals first | exact classifierCore_aux _ _ | (intro he; have hv := congrArg Fin.val he; simp only [classifierAux] at hv; omega)

theorem classifierBankPad_separate {N : ℕ} (i : Fin 3) (r : PhaseBlockReg) :
    classifierBankPad (N := N) i ≠ classifierBankReg r := by
  have hr := classifierBlockIndex_lt r
  intro he
  have hv := congrArg Fin.val he
  simp only [classifierBankPad, classifierBankReg, classifierAux] at hv
  omega

theorem classifierBankPad_repeat {N : ℕ} (temporary phase : Fin N) (i : Fin 3) (j : Fin 5) :
    classifierBankPad i ≠ classifierBankRepeat temporary phase j := by
  have hi := i.isLt
  fin_cases j <;> dsimp [classifierBankRepeat]
  all_goals first | exact (classifierCore_aux _ _).symm | (intro he; have hv := congrArg Fin.val he; simp only [classifierBankPad, classifierAux] at hv; omega)

end IntegerMultBounds.MathlibTM2.Routing
