module

public import IntegerMultBounds.MathlibTM2.Routing.RepairHeaderCountFrame

/-! Generate exact R2 interchange headers from live dimension tapes, construct
and erase both shift counts, and restore every non-output tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

def repairHeaderGenerateProgram {T Q A : ℕ} {P U : Type} (bank : RepairHeaderReg → Fin T) (c : Fin 2) : Pr P T Q A U :=
  .seq (repairHeaderCountProgram (repairHeaderCountReg bank) c)
    (.seq (exchangeHeaderProgram (repairHeaderExchangeReg bank))
      (metadataClean [repairHeaderCountReg bank .row, repairHeaderCountReg bank .gap]))

theorem repairHeaderGenerate_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (bank : RepairHeaderReg → Fin T) (hbank : Function.Injective bank)
    (p : Par) (X rb R B L : ℕ) (c : Fin 2)
    (hB : fieldsLen (selectiveKeyLen p X rb) + B < 2 ^ L)
    (hB0 : 0 < fieldsLen (selectiveKeyLen p X rb) + B)
    (rowBits widthBits : List Bool)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ []) (hrows : Counter.value rowBits = R)
    (hwidth : GrowingCounterData.Canonical widthBits) (hwidthValue : Counter.value widthBits = p.wc)
    (v : HS T Q A U) (S : Stacks T A)
    (hdim : ∀ f, (S.R (bank (.dimension f))).length = selectiveLen p X f)
    (hrowInput : S.R (bank (.exchange (.base .rows))) = rowBits.map bitSymbol)
    (hblock : S.R (bank (.exchange (.base .block))) = binSyms L (fieldsLen (selectiveKeyLen p X rb) + B))
    (hwidthInput : S.R (bank (.exchange (.base .target))) = widthBits.map bitSymbol)
    (hblank : ∀ r : ExchangeHeaderReg, r ≠ .base .rows → r ≠ .base .block → r ≠ .base .target →
      S.R (bank (.exchange r)) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 14 * (p.wc + p.wy + X) + 6 * rowBits.length + 52 * L + 12 * widthBits.length + 251 ∧
      Exec body (repairHeaderGenerateProgram bank c) (mk v S) m
        (mk v' { S with R := elementaryHeaderBank S.R (fun r => bank (.exchange (.base r))) (repairCanonicalHeaders p X rb R B c) }) := by
  let rg := repairHeaderCountReg bank
  let ex := repairHeaderExchangeReg bank
  have hrg := repairHeaderCountReg_injective bank hbank
  have hex := repairHeaderExchangeReg_injective bank hbank
  have hb (r : ExchangeHeaderReg) (hr : r ≠ .base .rows) (hbl : r ≠ .base .block) (hw : r ≠ .base .target) :
      S.R (ex r) = [] := hblank r hr hbl hw
  have hd (f : Fin 5) : (S.R (rg (.field f))).length = selectiveLen p X f := hdim f
  obtain ⟨v₁, hu₁, he₁⟩ := repairHeaderCounts_exec body rg hrg c v S
    (hb _ (by simp) (by simp) (by simp)) (hb _ (by simp) (by simp) (by simp))
    (hb _ (by simp) (by simp) (by simp)) (hb _ (by simp) (by simp) (by simp))
  rw [repairHeaderCounts_cost p X rg S.R c hd] at he₁
  let S₁ : Stacks T A := { S with R := repairHeaderCountBank rg c S.R }
  have hk (r : ExchangeHeaderReg) (hr : r ≠ .base .rowExp) (hg : r ≠ .base .gapExp) :
      S₁.R (ex r) = S.R (ex r) := repairHeaderCounts_exchange_keep bank hbank c S.R r hr hg
  obtain ⟨hlrow, hlgap⟩ := repairHeaderCounts_lengths p X rg S.R c hd
  have hrlen : (S₁.R (ex (.base .rowExp))).length =
      fieldsLen (selectiveLen p X) - (repairHeaderUpper p X c + p.wc) := by
    simpa [S₁, rg, ex, repairHeaderCountBank, repairHeaderCountReg, repairHeaderExchangeReg,
      repairHeaderCountRole, hbank.eq_iff] using hlrow
  have hglen : (S₁.R (ex (.base .gapExp))).length = repairHeaderUpper p X c - p.wc := by
    simpa [S₁, rg, ex, repairHeaderCountBank, repairHeaderCountReg, repairHeaderExchangeReg,
      repairHeaderCountRole, hbank.eq_iff] using hlgap
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := repairExchangeHeaders_exec body ex hex p X rb R B L c hB hB0
    rowBits widthBits hrow hrowNe hrows hwidth hwidthValue v₁ S₁
    (by rw [hk _ (by simp) (by simp)]; exact hrowInput)
    (by rw [hk _ (by simp) (by simp)]; exact hblock)
    (by rw [hk _ (by simp) (by simp)]; exact hwidthInput) hrlen hglen
    (by rw [hk _ (by simp) (by simp), hb _ (by simp) (by simp) (by simp)]; rfl)
    (by intro i; rw [hk _ (by simp) (by simp)]; exact hb _ (by simp) (by simp) (by simp))
    (by intro i; rw [hk _ (by simp) (by simp)]; exact hb _ (by simp) (by simp) (by simp))
    (by rw [hk _ (by simp) (by simp)]; exact hb _ (by simp) (by simp) (by simp))
  let S₂ : Stacks T A := { S with R := elementaryHeaderBank S.R (fun r => ex (.base r)) (repairCanonicalHeaders p X rb R B c) }
  obtain ⟨v₃, hu₃, he₃⟩ := repairHeaderCountsClean_exec body p X rg hrg c v₂ S₂
    (by intro f; rw [show S₂.R (rg (.field f)) = S.R (rg (.field f)) from
      repairHeaderBank_count_keep bank hbank S.R _ (.field f)]; exact hd f)
    (by rw [show S₂.R (rg .row) = S.R (rg .row) from repairHeaderBank_count_keep bank hbank S.R _ .row]; exact hb _ (by simp) (by simp) (by simp))
    (by rw [show S₂.R (rg .gap) = S.R (rg .gap) from repairHeaderBank_count_keep bank hbank S.R _ .gap]; exact hb _ (by simp) (by simp) (by simp))
  dsimp only [S₂] at he₃
  rw [repairHeaderCountBank_commute bank hbank c S.R] at he₃
  have hsum : (fieldsLen (selectiveLen p X) - (repairHeaderUpper p X c + p.wc)) +
      (repairHeaderUpper p X c - p.wc) = p.wc + p.wy + X := by
    rw [repairHeaderRowExp_eq, repairHeaderGapExp_eq]
    fin_cases c <;> simp <;> omega
  refine ⟨v₃, (6 * (p.wc + p.wy + X) + 20) + (m₂ + (2 * (p.wc + p.wy + X) + 5)),
    hu₃.trans (hu₂.trans hu₁), ?_, Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  omega

end IntegerMultBounds.MathlibTM2.Routing
