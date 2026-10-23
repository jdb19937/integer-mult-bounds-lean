module

public import IntegerMultBounds.MathlibTM2.Routing.RepairHeaderCountsClean

/-! Dimension tapes and the arithmetic header generator share one bank.
Count construction reuses the generator's row/gap and two scratch roles. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

inductive RepairHeaderReg where
  | dimension (i : Fin 5) | exchange (r : ExchangeHeaderReg)
  deriving DecidableEq

def repairHeaderCountRole : HeaderCountReg → RepairHeaderReg
  | .field i => .dimension i
  | .row => .exchange (.base .rowExp)
  | .gap => .exchange (.base .gapExp)
  | .tmp => .exchange (.base (.scratch 1))
  | .work => .exchange (.base (.scratch 2))

theorem repairHeaderCountRole_injective : Function.Injective repairHeaderCountRole := by
  intro r s he
  cases r <;> cases s <;> simp_all [repairHeaderCountRole]

def repairHeaderCountReg {T : ℕ} (bank : RepairHeaderReg → Fin T) : HeaderCountReg → Fin T :=
  bank ∘ repairHeaderCountRole

def repairHeaderExchangeReg {T : ℕ} (bank : RepairHeaderReg → Fin T) : ExchangeHeaderReg → Fin T :=
  bank ∘ RepairHeaderReg.exchange

theorem repairHeaderCountReg_injective {T : ℕ} (bank : RepairHeaderReg → Fin T)
    (hbank : Function.Injective bank) : Function.Injective (repairHeaderCountReg bank) :=
  hbank.comp repairHeaderCountRole_injective

theorem repairHeaderExchangeReg_injective {T : ℕ} (bank : RepairHeaderReg → Fin T)
    (hbank : Function.Injective bank) : Function.Injective (repairHeaderExchangeReg bank) :=
  hbank.comp (by intro r s he; exact RepairHeaderReg.exchange.inj he)

theorem repairHeaderCounts_header_separate {T : ℕ} (bank : RepairHeaderReg → Fin T)
    (hbank : Function.Injective bank) (r : HeaderCountReg) (i : Fin 5) :
    repairHeaderCountReg bank r ≠ repairHeaderExchangeReg bank (.base (.header i)) := by
  cases r <;> simp [repairHeaderCountReg, repairHeaderExchangeReg, repairHeaderCountRole, hbank.eq_iff]

theorem repairHeaderCounts_exchange_keep {T A : ℕ} (bank : RepairHeaderReg → Fin T)
    (hbank : Function.Injective bank) (c : Fin 2) (R : Fin T → List (Fin (A + 4)))
    (r : ExchangeHeaderReg) (hrow : r ≠ .base .rowExp) (hgap : r ≠ .base .gapExp) :
    repairHeaderCountBank (repairHeaderCountReg bank) c R (repairHeaderExchangeReg bank r) =
      R (repairHeaderExchangeReg bank r) := by
  simp [repairHeaderCountBank, repairHeaderCountReg, repairHeaderExchangeReg, repairHeaderCountRole,
    hbank.eq_iff, hrow, hgap]

end IntegerMultBounds.MathlibTM2.Routing
