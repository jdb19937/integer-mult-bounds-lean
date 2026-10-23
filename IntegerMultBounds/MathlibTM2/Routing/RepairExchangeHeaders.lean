module

public import IntegerMultBounds.MathlibTM2.Routing.ExchangeCanonicalHeaders
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelective

/-! The R2 field swaps are interval exchanges beginning at the low b field.
Their arithmetic header generator therefore emits the exact R2 header bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

def repairHeaderUpper (p : Par) (X : ℕ) (c : Fin 2) : ℕ :=
  fieldOff (selectiveLen p X) (selectiveSwapFld c)

theorem repairHeaderUpper_ge (p : Par) (X : ℕ) (c : Fin 2) : p.wc ≤ repairHeaderUpper p X c := by
  fin_cases c <;> simp [repairHeaderUpper, selectiveSwapFld, selectiveFieldOff]

theorem repairHeaderRowExp_eq (p : Par) (X : ℕ) (c : Fin 2) :
    fieldsLen (selectiveLen p X) - (repairHeaderUpper p X c + p.wc) =
      if c = 0 then p.wc + X else X := by
  simp only [repairHeaderUpper, selectiveFieldOff]
  fin_cases c <;> simp [fieldsLen, Fin.sum_univ_succ, selectiveLen, selectiveSwapFld] <;> omega

theorem repairHeaderGapExp_eq (p : Par) (X : ℕ) (c : Fin 2) :
    repairHeaderUpper p X c - p.wc = if c = 0 then p.wy else p.wy + p.wc := by
  fin_cases c <;> simp [repairHeaderUpper, selectiveSwapFld, selectiveFieldOff]; omega

theorem repairExchangeHeaders_eq (p : Par) (X rb R B : ℕ) (c : Fin 2) :
    exchangeCanonicalHeaders (fieldsLen (selectiveLen p X)) 0 (repairHeaderUpper p X c) p.wc R
      (fieldsLen (selectiveKeyLen p X rb) + B) = repairCanonicalHeaders p X rb R B c := by
  have hab : 0 + p.wc ≤ repairHeaderUpper p X c := by simpa using repairHeaderUpper_ge p X c
  funext k
  unfold exchangeCanonicalHeaders repairCanonicalHeaders routingHeaders selectiveSwapValues
  rw [blockExchangeDimensions_eq _ _ _ _ _ _ hab]
  simp [swapDimsIdx, repairHeaderUpper, selectiveFieldOff]

theorem repairExchangeHeaders_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (bank : ExchangeHeaderReg → Fin T) (hbank : Function.Injective bank)
    (p : Par) (X rb R B L : ℕ) (c : Fin 2)
    (hB : fieldsLen (selectiveKeyLen p X rb) + B < 2 ^ L)
    (hB0 : 0 < fieldsLen (selectiveKeyLen p X rb) + B)
    (rowBits widthBits : List Bool)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ []) (hrows : Counter.value rowBits = R)
    (hwidth : GrowingCounterData.Canonical widthBits) (hwidthValue : Counter.value widthBits = p.wc)
    (v : HS T Q A U) (S : Stacks T A)
    (hrowInput : S.R (bank (.base .rows)) = rowBits.map bitSymbol)
    (hblock : S.R (bank (.base .block)) = binSyms L (fieldsLen (selectiveKeyLen p X rb) + B))
    (hwidthInput : S.R (bank (.base .target)) = widthBits.map bitSymbol)
    (hrowExp : (S.R (bank (.base .rowExp))).length = fieldsLen (selectiveLen p X) - (repairHeaderUpper p X c + p.wc))
    (hgapExp : (S.R (bank (.base .gapExp))).length = repairHeaderUpper p X c - p.wc)
    (hlowerExp : (S.R (bank .lowerExp)).length = 0)
    (hheaders : ∀ i, S.R (bank (.base (.header i))) = [])
    (hscratch : ∀ i, S.R (bank (.base (.scratch i))) = []) (htriple : S.R (bank .triple) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 6 * (rowBits.length + (fieldsLen (selectiveLen p X) - (repairHeaderUpper p X c + p.wc))) +
        6 * (repairHeaderUpper p X c - p.wc) + 52 * L + 12 * widthBits.length + 226 ∧
      Exec body (exchangeHeaderProgram bank) (mk v S) m
        (mk v' { S with R := elementaryHeaderBank S.R (fun r => bank (.base r)) (repairCanonicalHeaders p X rb R B c) }) := by
  have he := exchangeCanonicalHeaders_exec body bank hbank (fieldsLen (selectiveLen p X)) 0
    (repairHeaderUpper p X c) p.wc R (fieldsLen (selectiveKeyLen p X rb) + B) L
    (by simpa using repairHeaderUpper_ge p X c) hB hB0 rowBits widthBits hrow hrowNe hrows hwidth hwidthValue
    v S hrowInput hblock hwidthInput hrowExp (by simpa using hgapExp) hlowerExp hheaders hscratch htriple
  simpa only [repairExchangeHeaders_eq, Nat.mul_zero, Nat.add_zero, Nat.sub_zero] using he

end IntegerMultBounds.MathlibTM2.Routing
