module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryExchangeCall

/-! One shared physical bank for binary exchange setup, header generation and
installation. Scratch is reused between phases, rather than allocated per call. -/

@[expose] public section
noncomputable section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

inductive BinaryExchangeReg (t₀ : ℕ) where
  | bank (i : Fin (swapT t₀))
  | width | lower | upper | span | rowExp | gapExp | lowerExp | rows | block | canonical
  | header (i : Fin 5) | scratch (i : Fin 7)
  | triple | work | aux | ctmp | str | tmp
  deriving DecidableEq

def binaryExchangeHeaderBase {t₀ : ℕ} : ElementaryHeaderReg → BinaryExchangeReg t₀
  | .rowExp => .rowExp
  | .gapExp => .gapExp
  | .target => .canonical
  | .rows => .rows
  | .block => .block
  | .header i => .header i
  | .scratch i => .scratch i

def binaryExchangeHeaderReg {t₀ : ℕ} : ExchangeHeaderReg → BinaryExchangeReg t₀
  | .base r => binaryExchangeHeaderBase r
  | .lowerExp => .lowerExp
  | .triple => .triple

def binaryExchangeExponentReg {t₀ : ℕ} : ExchangeExponentReg → BinaryExchangeReg t₀
  | .width => .width
  | .lower => .lower
  | .upper => .upper
  | .span => .span
  | .rowExp => .rowExp
  | .gapExp => .gapExp
  | .lowerExp => .lowerExp
  | .scratch i => .scratch i

theorem binaryExchangeHeaderBase_injective {t₀ : ℕ} :
    Function.Injective (binaryExchangeHeaderBase (t₀ := t₀)) := by
  intro i j h
  cases i <;> cases j <;> simp_all [binaryExchangeHeaderBase]

theorem binaryExchangeHeaderReg_injective {t₀ : ℕ} :
    Function.Injective (binaryExchangeHeaderReg (t₀ := t₀)) := by
  intro i j h
  cases i with
  | base i =>
    cases j with
    | base j => exact congrArg ExchangeHeaderReg.base (binaryExchangeHeaderBase_injective h)
    | lowerExp => cases i <;> simp_all [binaryExchangeHeaderReg, binaryExchangeHeaderBase]
    | triple => cases i <;> simp_all [binaryExchangeHeaderReg, binaryExchangeHeaderBase]
  | lowerExp => cases j with
    | base j => cases j <;> simp_all [binaryExchangeHeaderReg, binaryExchangeHeaderBase]
    | lowerExp => rfl
    | triple => simp_all [binaryExchangeHeaderReg]
  | triple => cases j with
    | base j => cases j <;> simp_all [binaryExchangeHeaderReg, binaryExchangeHeaderBase]
    | lowerExp => simp_all [binaryExchangeHeaderReg]
    | triple => rfl

theorem binaryExchangeExponentReg_injective {t₀ : ℕ} :
    Function.Injective (binaryExchangeExponentReg (t₀ := t₀)) := by
  intro i j h
  cases i <;> cases j <;> simp_all [binaryExchangeExponentReg]

end IntegerMultBounds.MathlibTM2.Routing
