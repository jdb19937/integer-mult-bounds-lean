module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryFieldBatch

/-! Two generated fields share one unary temporary and three scratch tapes.
Only two binary width inputs are added: six tapes beyond an arbitrary core bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

def fieldCore {N : ℕ} (i : Fin N) : Fin (N + 6) := ⟨i.val, by omega⟩

def fieldAux {N : ℕ} (i : Fin 6) : Fin (N + 6) := ⟨N + i.val, by omega⟩

theorem fieldCore_injective {N : ℕ} : Function.Injective (fieldCore (N := N)) := by
  intro i j he
  exact Fin.ext (congrArg (fun x : Fin (N + 6) => x.val) he)

theorem fieldCore_aux {N : ℕ} (i : Fin N) (j : Fin 6) : fieldCore i ≠ fieldAux j := by
  intro he
  have hv := congrArg Fin.val he
  have hi := i.isLt
  simp only [fieldCore, fieldAux] at hv
  omega

def fieldPairReg {N : ℕ} (dst : Fin N) (k : Fin 2) : BinaryZeroReg → Fin (N + 6)
  | .width => fieldAux ⟨k.val, by omega⟩
  | .dst => fieldCore dst
  | .unary => fieldAux 2
  | .scratch i => fieldAux ⟨3 + i.val, by omega⟩

theorem fieldPairReg_injective {N : ℕ} (dst : Fin N) (k : Fin 2) :
    Function.Injective (fieldPairReg dst k) := by
  intro r s he
  have hv := congrArg Fin.val he
  have hd := dst.isLt
  have hk := k.isLt
  cases r <;> cases s <;> simp only [fieldPairReg, fieldCore, fieldAux] at hv
  all_goals first | rfl | (exfalso; omega) | (congr 1; apply Fin.ext; omega)

theorem fieldPairReg_core {N : ℕ} (dst i : Fin N) (k : Fin 2)
    (r : BinaryZeroReg) (hr : r ≠ .dst) : fieldCore i ≠ fieldPairReg dst k r := by
  cases r with
  | dst => exact (hr rfl).elim
  | width => exact fieldCore_aux i _
  | unary => exact fieldCore_aux i _
  | scratch j => exact fieldCore_aux i _

def fieldPairJob {N : ℕ} (dst : Fin N) (k : Fin 2) (ones : Bool) (L n : ℕ) : BinaryFieldJob (N + 6) :=
  ⟨fieldPairReg dst k, ones, L, n⟩

end IntegerMultBounds.MathlibTM2.Routing
