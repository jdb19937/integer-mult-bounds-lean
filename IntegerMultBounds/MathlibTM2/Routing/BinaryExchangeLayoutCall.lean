module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryExchangeLayout

/-! All separation premises of an actual binary exchange are discharged by one
injective common-bank layout. No phase receives a fresh bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

noncomputable def binaryExchangeLayoutCall {t₀ T Q n R B : ℕ}
    (slot : BinaryExchangeReg t₀ → Fin T) (hslot : Function.Injective slot)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd) (hpay : ∀ k, hd k ≠ pay)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T)
    (spec : BlockExchangeSpec n) (hR : 0 < R) (hB : 0 < B)
    (rowBits : List Bool) (Lc L : ℕ) (hn : n < 2 ^ Lc) (hBin : B < 2 ^ L)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ []) (hrowValue : Counter.value rowBits = R) :
    BinaryExchangeCall t₀ T Q n R B (slot .str) (slot .tmp) where
  hd := hd
  pay := pay
  hhd := hhd
  hpay := hpay
  hQ := hQ
  bank := fun j => slot (.bank j)
  hbank := hslot.comp (by intro i j h; exact BinaryExchangeReg.bank.inj h)
  hT := hT
  hst := by simp [hslot.eq_iff]
  hstr := by intro j; simp [hslot.eq_iff]
  htmp := by intro j; simp [hslot.eq_iff]
  a := spec.a
  b := spec.b
  w := spec.w
  hab := spec.separate
  hb := spec.fits
  hR := hR
  hB := hB
  rg := slot ∘ binaryExchangeHeaderReg
  hrg := hslot.comp binaryExchangeHeaderReg_injective
  cfg := fun k => slot (.header k)
  hcfg := rfl
  hbankRaw := by intro j; simp [exchangeHeaderPrivate, binaryExchangeHeaderReg, binaryExchangeHeaderBase, hslot.eq_iff]
  hstrRaw := by simp [exchangeHeaderPrivate, binaryExchangeHeaderReg, binaryExchangeHeaderBase, hslot.eq_iff]
  htmpRaw := by simp [exchangeHeaderPrivate, binaryExchangeHeaderReg, binaryExchangeHeaderBase, hslot.eq_iff]
  work := slot .work
  aux := slot .aux
  ctmp := slot .ctmp
  hworkRaw := by simp [exchangeHeaderPrivate, binaryExchangeHeaderReg, binaryExchangeHeaderBase, hslot.eq_iff]
  hauxRaw := by simp [exchangeHeaderPrivate, binaryExchangeHeaderReg, binaryExchangeHeaderBase, hslot.eq_iff]
  hctmpRaw := by simp [exchangeHeaderPrivate, binaryExchangeHeaderReg, binaryExchangeHeaderBase, hslot.eq_iff]
  hregs := by intro k; simp [List.nodup_cons, hslot.eq_iff]
  hsources := by intro k j; simp [hslot.eq_iff]
  ex := slot ∘ binaryExchangeExponentReg
  hex := hslot.comp binaryExchangeExponentReg_injective
  hcanonical := by intro r; cases r <;> simp [binaryExchangeHeaderReg, binaryExchangeHeaderBase, binaryExchangeExponentReg, hslot.eq_iff]
  hrowSlot := rfl
  hgapSlot := rfl
  hlowerSlot := rfl
  hheaderOther := by
    intro r h₁ h₂ h₃ h₄
    cases r with
    | base r => cases r <;> simp_all [exchangeBinarySetupPrivate, exchangeExponentPrivate,
        binaryExchangeHeaderReg, binaryExchangeHeaderBase, binaryExchangeExponentReg, hslot.eq_iff]
    | lowerExp => exact (h₃ rfl).elim
    | triple => simp [exchangeBinarySetupPrivate, exchangeExponentPrivate,
        binaryExchangeHeaderReg, binaryExchangeHeaderBase, binaryExchangeExponentReg, hslot.eq_iff]
  hbankSetup := by intro j; simp [exchangeBinarySetupPrivate, exchangeExponentPrivate,
    binaryExchangeHeaderReg, binaryExchangeHeaderBase, binaryExchangeExponentReg, hslot.eq_iff]
  hstrSetup := by simp [exchangeBinarySetupPrivate, exchangeExponentPrivate,
    binaryExchangeHeaderReg, binaryExchangeHeaderBase, binaryExchangeExponentReg, hslot.eq_iff]
  htmpSetup := by simp [exchangeBinarySetupPrivate, exchangeExponentPrivate,
    binaryExchangeHeaderReg, binaryExchangeHeaderBase, binaryExchangeExponentReg, hslot.eq_iff]
  hworkSetup := by simp [exchangeBinarySetupPrivate, exchangeExponentPrivate,
    binaryExchangeHeaderReg, binaryExchangeHeaderBase, binaryExchangeExponentReg, hslot.eq_iff]
  hauxSetup := by simp [exchangeBinarySetupPrivate, exchangeExponentPrivate,
    binaryExchangeHeaderReg, binaryExchangeHeaderBase, binaryExchangeExponentReg, hslot.eq_iff]
  hctmpSetup := by simp [exchangeBinarySetupPrivate, exchangeExponentPrivate,
    binaryExchangeHeaderReg, binaryExchangeHeaderBase, binaryExchangeExponentReg, hslot.eq_iff]
  rowBits := rowBits
  Lc := Lc
  L := L
  hn := hn
  hBin := hBin
  hrow := hrow
  hrowNe := hrowNe
  hrowValue := hrowValue
  ex_str := by intro r; cases r <;> simp [binaryExchangeExponentReg, hslot.eq_iff]
  rg_str := by
    intro r
    cases r with
    | base r => cases r <;> simp [binaryExchangeHeaderReg, binaryExchangeHeaderBase, hslot.eq_iff]
    | lowerExp => simp [binaryExchangeHeaderReg, hslot.eq_iff]
    | triple => simp [binaryExchangeHeaderReg, hslot.eq_iff]
  work_str := by simp [hslot.eq_iff]
  aux_str := by simp [hslot.eq_iff]
  ctmp_str := by simp [hslot.eq_iff]

end IntegerMultBounds.MathlibTM2.Routing
