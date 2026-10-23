module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalHeaderValue
public import IntegerMultBounds.MathlibTM2.Routing.ExchangeHeaderExec

/-! The arithmetic exchange-header generator emits the exact canonical lists
specified by the swap dimensions, without separate large numeric operands. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

def exchangeCanonicalHeaders (n a b w rows B : ℕ) (k : Fin 5) : List Bool :=
  GrowingCounterData.advance (swapValues (blockExchangeDimensions n a b w rows B).1
    (blockExchangeDimensions n a b w rows B).2.1 (blockExchangeDimensions n a b w rows B).2.2 w w k) []

theorem exchangeHeaderWords_eq_canonical (n a b w rows B : ℕ) (hab : a + w ≤ b)
    (rowBits payload widthBits : List Bool)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrows : Counter.value rowBits = rows)
    (hpayload : GrowingCounterData.Canonical payload) (hpayloadValue : Counter.value payload = 2 ^ a * (3 * B))
    (hwidth : GrowingCounterData.Canonical widthBits) (hwidthValue : Counter.value widthBits = w) :
    exchangeHeaderWords rowBits payload widthBits (n - (b + w)) (b - a - w) =
      exchangeCanonicalHeaders n a b w rows B := by
  obtain ⟨hc, hv⟩ := exchangeHeaderWords_valid n a b w rows B hab rowBits payload widthBits
    hrow hrowNe hrows hpayload hpayloadValue hwidth hwidthValue
  funext k
  simpa only [hv k, exchangeCanonicalHeaders] using canonical_eq_advance _ (hc k)

theorem exchangeCanonicalHeaders_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (bank : ExchangeHeaderReg → Fin T) (hbank : Function.Injective bank)
    (n a b w rows B L : ℕ) (hab : a + w ≤ b) (hB : B < 2 ^ L) (hB0 : 0 < B)
    (rowBits widthBits : List Bool)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ []) (hrows : Counter.value rowBits = rows)
    (hwidth : GrowingCounterData.Canonical widthBits) (hwidthValue : Counter.value widthBits = w)
    (v : HS T Q A U) (S : Stacks T A)
    (hrowInput : S.R (bank (.base .rows)) = rowBits.map bitSymbol)
    (hblock : S.R (bank (.base .block)) = binSyms L B)
    (hwidthInput : S.R (bank (.base .target)) = widthBits.map bitSymbol)
    (hrowExp : (S.R (bank (.base .rowExp))).length = n - (b + w))
    (hgapExp : (S.R (bank (.base .gapExp))).length = b - a - w)
    (hlowerExp : (S.R (bank .lowerExp)).length = a)
    (hheaders : ∀ i, S.R (bank (.base (.header i))) = [])
    (hscratch : ∀ i, S.R (bank (.base (.scratch i))) = []) (htriple : S.R (bank .triple) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 6 * (rowBits.length + (n - (b + w))) + 6 * (b - a - w) + 52 * L +
        6 * a + 12 * widthBits.length + 226 ∧
      Exec body (exchangeHeaderProgram bank) (mk v S) m
        (mk v' { S with R := elementaryHeaderBank S.R (fun r => bank (.base r)) (exchangeCanonicalHeaders n a b w rows B) }) := by
  obtain ⟨payload, v', m, hc, hv, _, hu, hm, he⟩ := exchangeHeader_exec body bank hbank rowBits widthBits L B hB hB0
    v S hrowInput hblock hwidthInput hheaders hscratch htriple
  rw [hlowerExp] at hv
  rw [hrowExp, hgapExp, hlowerExp] at hm
  rw [hrowExp, hgapExp, exchangeHeaderWords_eq_canonical n a b w rows B hab rowBits payload widthBits
    hrow hrowNe hrows hc hv hwidth hwidthValue] at he
  exact ⟨v', m, hu, hm, he⟩

end IntegerMultBounds.MathlibTM2.Routing
