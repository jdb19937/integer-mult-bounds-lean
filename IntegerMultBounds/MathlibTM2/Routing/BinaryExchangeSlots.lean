module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryExchangeLayout

/-! Explicit tape numbering: the host bank plus 28 reusable exchange tapes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

noncomputable def binaryExchangeSlot {t₀ : ℕ} : BinaryExchangeReg t₀ → Fin (swapT t₀ + 28)
  | .bank i => ⟨i.val, by have := i.isLt; omega⟩
  | .width => ⟨swapT t₀, by omega⟩
  | .lower => ⟨swapT t₀ + 1, by omega⟩
  | .upper => ⟨swapT t₀ + 2, by omega⟩
  | .span => ⟨swapT t₀ + 3, by omega⟩
  | .rowExp => ⟨swapT t₀ + 4, by omega⟩
  | .gapExp => ⟨swapT t₀ + 5, by omega⟩
  | .lowerExp => ⟨swapT t₀ + 6, by omega⟩
  | .rows => ⟨swapT t₀ + 7, by omega⟩
  | .block => ⟨swapT t₀ + 8, by omega⟩
  | .canonical => ⟨swapT t₀ + 9, by omega⟩
  | .header i => ⟨swapT t₀ + 10 + i.val, by have := i.isLt; omega⟩
  | .scratch i => ⟨swapT t₀ + 15 + i.val, by have := i.isLt; omega⟩
  | .triple => ⟨swapT t₀ + 22, by omega⟩
  | .work => ⟨swapT t₀ + 23, by omega⟩
  | .aux => ⟨swapT t₀ + 24, by omega⟩
  | .ctmp => ⟨swapT t₀ + 25, by omega⟩
  | .str => ⟨swapT t₀ + 26, by omega⟩
  | .tmp => ⟨swapT t₀ + 27, by omega⟩

theorem binaryExchangeSlot_injective {t₀ : ℕ} : Function.Injective (binaryExchangeSlot (t₀ := t₀)) := by
  intro i j h
  have hv := congrArg Fin.val h
  cases i <;> cases j <;> simp only [binaryExchangeSlot] at hv
  all_goals first | rfl | (exfalso; omega) | (congr 1; apply Fin.ext; omega)

end IntegerMultBounds.MathlibTM2.Routing
