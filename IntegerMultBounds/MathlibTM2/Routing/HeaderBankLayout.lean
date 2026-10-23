module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalHeaderBatch

/-! A canonical-header bank uses one binary source per output and two shared
scratch tapes. Outputs occupy distinct destinations in an arbitrary core bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

def headerCore {N J : ℕ} (i : Fin N) : Fin (N + (J + 2)) := ⟨i.val, by omega⟩
def headerAux {N J : ℕ} (i : Fin (J + 2)) : Fin (N + (J + 2)) := ⟨N + i.val, by omega⟩

theorem headerCore_injective {N J : ℕ} : Function.Injective (headerCore (N := N) (J := J)) := by
  intro i j he
  exact Fin.ext (congrArg (fun x : Fin (N + (J + 2)) => x.val) he)

theorem headerCore_aux {N J : ℕ} (i : Fin N) (j : Fin (J + 2)) : headerCore i ≠ headerAux j := by
  intro he
  have hv := congrArg Fin.val he
  have hi := i.isLt
  simp only [headerCore, headerAux] at hv
  omega

def headerBankReg {N J : ℕ} (dst : Fin J → Fin N) (j : Fin J) (i : Fin 4) : Fin (N + (J + 2)) :=
  if i = 0 then headerAux ⟨j.val, by omega⟩ else
    if i = 1 then headerCore (dst j) else
      if i = 2 then headerAux ⟨J, by omega⟩ else headerAux ⟨J + 1, by omega⟩

theorem headerBankReg_injective {N J : ℕ} (dst : Fin J → Fin N) (j : Fin J) :
    Function.Injective (headerBankReg dst j) := by
  intro i k he
  have hj := j.isLt
  have hd := (dst j).isLt
  fin_cases i <;> fin_cases k <;> dsimp [headerBankReg, headerCore, headerAux] at he
  all_goals first | rfl | (exfalso; simp only [Fin.mk.injEq] at he; omega)

theorem headerBankReg_separate {N J : ℕ} (dst : Fin J → Fin N) (hdst : Function.Injective dst)
    (j k : Fin J) (hjk : j ≠ k) (i : Fin 4) : headerCore (J := J) (dst j) ≠ headerBankReg dst k i := by
  fin_cases i <;> dsimp [headerBankReg]
  all_goals first | exact headerCore_aux _ _ | exact headerCore_injective.ne (hdst.ne hjk)

def headerBankJob {N J : ℕ} (dst : Fin J → Fin N) (L value : Fin J → ℕ) (j : Fin J) :
    CanonicalHeaderJob (N + (J + 2)) := ⟨headerBankReg dst j, L j, value j⟩

theorem headerBankJob_dst {N J : ℕ} (dst : Fin J → Fin N) (L value : Fin J → ℕ) (j : Fin J) :
    (headerBankJob dst L value j).dst = headerCore (dst j) := rfl

theorem headerBankJob_injective {N J : ℕ} (dst : Fin J → Fin N) (hdst : Function.Injective dst)
    (L value : Fin J → ℕ) : Function.Injective (headerBankJob dst L value) := by
  intro j k he
  have h := congrArg CanonicalHeaderJob.dst he
  exact hdst (headerCore_injective h)

end IntegerMultBounds.MathlibTM2.Routing
