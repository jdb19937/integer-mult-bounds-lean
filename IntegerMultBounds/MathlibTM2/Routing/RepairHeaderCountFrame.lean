module

public import IntegerMultBounds.MathlibTM2.Routing.RepairHeaderLayout

/-! Count construction and canonical-header writes commute because their
outputs are disjoint and every live dimension tape is preserved. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

theorem repairHeaderBank_dimension {T A : ℕ} (bank : RepairHeaderReg → Fin T)
    (hbank : Function.Injective bank) (R : Fin T → List (Fin (A + 4)))
    (words : Fin 5 → List Bool) (i : Fin 5) :
    elementaryHeaderBank R (fun r => repairHeaderExchangeReg bank (.base r)) words (bank (.dimension i)) =
      R (bank (.dimension i)) := by
  simp [elementaryHeaderBank, repairHeaderExchangeReg, hbank.eq_iff]

theorem repairHeaderBank_count_keep {T A : ℕ} (bank : RepairHeaderReg → Fin T)
    (hbank : Function.Injective bank) (R : Fin T → List (Fin (A + 4)))
    (words : Fin 5 → List Bool) (r : HeaderCountReg) :
    elementaryHeaderBank R (fun r => repairHeaderExchangeReg bank (.base r)) words (repairHeaderCountReg bank r) =
      R (repairHeaderCountReg bank r) := by
  have hs := repairHeaderCounts_header_separate bank hbank r
  simp [elementaryHeaderBank, hs]

theorem repairHeaderCountBank_commute {T A : ℕ} (bank : RepairHeaderReg → Fin T)
    (hbank : Function.Injective bank) (c : Fin 2) (R : Fin T → List (Fin (A + 4)))
    (words : Fin 5 → List Bool) :
    repairHeaderCountBank (repairHeaderCountReg bank) c
      (elementaryHeaderBank R (fun r => repairHeaderExchangeReg bank (.base r)) words) =
    elementaryHeaderBank (repairHeaderCountBank (repairHeaderCountReg bank) c R)
      (fun r => repairHeaderExchangeReg bank (.base r)) words := by
  have hf : ∀ f : Fin 5,
      elementaryHeaderBank R (fun r => repairHeaderExchangeReg bank (.base r)) words
        (repairHeaderCountReg bank (.field f)) = R (repairHeaderCountReg bank (.field f)) := by
    intro f
    exact repairHeaderBank_count_keep bank hbank R words (.field f)
  simp only [repairHeaderCountBank, hf]
  funext i
  by_cases hr : i = repairHeaderCountReg bank .row
  · subst i
    simp [elementaryHeaderBank,
      repairHeaderCountReg, repairHeaderExchangeReg, repairHeaderCountRole, hbank.eq_iff]
  · by_cases hg : i = repairHeaderCountReg bank .gap
    · subst i
      simp [elementaryHeaderBank,
        repairHeaderCountReg, repairHeaderExchangeReg, repairHeaderCountRole, hbank.eq_iff]
    · simp only [Function.update_of_ne hr, Function.update_of_ne hg, elementaryHeaderBank, Function.update_apply]

end IntegerMultBounds.MathlibTM2.Routing
