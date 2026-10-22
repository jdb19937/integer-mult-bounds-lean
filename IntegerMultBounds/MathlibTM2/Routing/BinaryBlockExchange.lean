module

public import IntegerMultBounds.MathlibTM2.Routing.GeneratedBlockExchangeCost
public import IntegerMultBounds.MathlibTM2.Routing.ExchangeBinarySetup

/-! Actual interval exchanges from padded binary coordinates, with all setup
and both header banks generated and cleared by execution. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem binaryBlockExchange_exec {t₀ T Q K : ℕ} {U F : Type}
    (body : F → Pr F T Q (prime + K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd) (hpay : ∀ k, hd k ≠ pay)
    (hQ : swapStates hd pay hhd ≤ Q)
    (bank : Fin (swapT t₀) → Fin T) (hbank : Function.Injective bank) (hT : swapT t₀ ≤ T)
    (str tmp : Fin T) (hst : str ≠ tmp)
    (hstr : ∀ j, bank j ≠ str) (htmp : ∀ j, bank j ≠ tmp)
    (n a b w : ℕ) (hab : a + w ≤ b) (hb : b + w ≤ n)
    {R B : ℕ} (hR : 0 < R) (hB : 0 < B)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlB : ∀ r ∈ l, r.length = B) (h8 : ∀ r ∈ l, ∀ s ∈ r, s.val < 8)
    (rg : ExchangeHeaderReg → Fin T) (hrg : Function.Injective rg)
    (cfg : Fin 5 → Fin T) (hcfg : cfg = fun k => rg (.base (.header k)))
    (hbankRaw : ∀ j, bank j ∉ exchangeHeaderPrivate rg)
    (hstrRaw : str ∉ exchangeHeaderPrivate rg) (htmpRaw : tmp ∉ exchangeHeaderPrivate rg)
    (work aux ctmp : Fin T)
    (hworkRaw : work ∉ exchangeHeaderPrivate rg) (hauxRaw : aux ∉ exchangeHeaderPrivate rg)
    (hctmpRaw : ctmp ∉ exchangeHeaderPrivate rg)
    (hregs : ∀ k, [cfg k, bank (reg (hd k)), work, aux, ctmp].Nodup)
    (hsources : ∀ k j, cfg k ≠ bank (reg (hd j)))
    (ex : ExchangeExponentReg → Fin T) (hex : Function.Injective ex)
    (hcanonical : ∀ r, rg (.base .target) ≠ ex r)
    (hrowSlot : rg (.base .rowExp) = ex .rowExp) (hgapSlot : rg (.base .gapExp) = ex .gapExp)
    (hlowerSlot : rg .lowerExp = ex .lowerExp)
    (hheaderOther : ∀ r, r ≠ .base .rowExp → r ≠ .base .gapExp → r ≠ .lowerExp → r ≠ .base .target →
      rg r ∉ exchangeBinarySetupPrivate ex (rg (.base .target)))
    (hbankSetup : ∀ j, bank j ∉ exchangeBinarySetupPrivate ex (rg (.base .target)))
    (hstrSetup : str ∉ exchangeBinarySetupPrivate ex (rg (.base .target)))
    (htmpSetup : tmp ∉ exchangeBinarySetupPrivate ex (rg (.base .target)))
    (hworkSetup : work ∉ exchangeBinarySetupPrivate ex (rg (.base .target)))
    (hauxSetup : aux ∉ exchangeBinarySetupPrivate ex (rg (.base .target)))
    (hctmpSetup : ctmp ∉ exchangeBinarySetupPrivate ex (rg (.base .target)))
    (rowBits : List Bool) (Lc L : ℕ) (hn : n < 2 ^ Lc) (hBin : B < 2 ^ L)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ []) (hrowValue : Counter.value rowBits = R)
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hL : ∀ j, S.L j = []) (hsrc : S.R str = l.flatten) (htmp0 : S.R tmp = [])
    (hpay0 : S.R (bank (reg pay)) = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (bank j) = [])
    (hhdr0 : ∀ k, S.R (bank (reg (hd k))) = [])
    (hrows : S.R (rg (.base .rows)) = rowBits.map bitSymbol)
    (hblock : S.R (rg (.base .block)) = binSyms L B)
    (hwidth : S.R (ex .width) = binSyms Lc n) (hlower : S.R (ex .lower) = binSyms Lc a)
    (hupper : S.R (ex .upper) = binSyms Lc b) (hspan : S.R (ex .span) = binSyms Lc w)
    (hlower0 : S.R (ex .lowerExp) = []) (hrow0 : S.R (ex .rowExp) = []) (hgap0 : S.R (ex .gapExp) = [])
    (hexScratch : ∀ i, S.R (ex (.scratch i)) = []) (hcanonical0 : S.R (rg (.base .target)) = [])
    (hraw0 : ∀ k, S.R (rg (.base (.header k))) = [])
    (hscratch : ∀ i, S.R (rg (.base (.scratch i))) = []) (htriple : S.R (rg .triple) = [])
    (hw : S.R work = []) (ha : S.R aux = []) (hc0 : S.R ctmp = [])
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (bank (reg i)), s ≠ blank ∧ s.val < prime + 4) :
    ∃ (v' : HS T Q (prime + K) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ (3 * (Lc * (4 * n + 31) + 2 * n + 26) + 10 * Lc + 12 : ℕ) +
        generatedExchangeBound bank R B n a b w L rowBits.length Lc S + (2 * n + 2 * Lc + 9 : ℕ) ∧
      Exec body (.seq (exchangeBinarySetupProgram ex (rg (.base .target)))
        (.seq (.seq (exchangeHeaderProgram rg)
        (.seq (installedBlockExchangeProgram cfg bank hd work aux ctmp
          (swapPass hd pay hhd hQ bank hbank hT str tmp)) (metadataClean (exchangeHeaderPrivate rg))))
          (metadataClean (exchangeBinarySetupPrivate ex (rg (.base .target)))))) (mk v S) m
        (mk v' { S with R := Function.update S.R str (moveRecs (blockExchangeRank n a b w R hab hb) l).flatten }) := by
  let canonical := rg (.base .target)
  have hcanonical' (r : ExchangeExponentReg) : canonical ≠ ex r := hcanonical r
  obtain ⟨bits, v₁, m₁, hbits, hbitsValue, hbitsLength, hu₁, hm₁, he₁⟩ := exchangeBinarySetup_exec body ex hex
    canonical hcanonical Lc n a b w hn hab hb v S hwidth hlower hupper hspan hlower0 hrow0 hgap0 hexScratch hcanonical0
  let S₁ : Stacks T (prime + K) := { S with R := Function.update (exchangeExponentBank S.R ex n a b w) canonical (bits.map bitSymbol) }
  have hkeep (j : Fin T) (hj : j ∉ exchangeBinarySetupPrivate ex canonical) : S₁.R j = S.R j :=
    exchangeBinarySetup_keep S.R ex canonical bits n a b w j hj
  have hbankKeep (j : Fin (swapT t₀)) : S₁.R (bank j) = S.R (bank j) := hkeep _ (hbankSetup j)
  have hheaderKeep (r : ExchangeHeaderReg) (h₁ : r ≠ .base .rowExp) (h₂ : r ≠ .base .gapExp)
      (h₃ : r ≠ .lowerExp) (h₄ : r ≠ .base .target) : S₁.R (rg r) = S.R (rg r) :=
    hkeep _ (hheaderOther r h₁ h₂ h₃ h₄)
  have hrowExp : (S₁.R (rg (.base .rowExp))).length = n - (b + w) := by
    simp [S₁, hrowSlot, Function.update_of_ne (hcanonical' .rowExp).symm, exchangeExponentBank, hex.eq_iff, Nat.sub_sub]
  have hgapExp : (S₁.R (rg (.base .gapExp))).length = b - a - w := by
    simp [S₁, hgapSlot, Function.update_of_ne (hcanonical' .gapExp).symm, exchangeExponentBank]
  have hlowerExp : (S₁.R (rg .lowerExp)).length = a := by
    simp [S₁, hlowerSlot, Function.update_of_ne (hcanonical' .lowerExp).symm, exchangeExponentBank, hex.eq_iff]
  obtain ⟨payload, v₂, m₂, _, _, _, hu₂, hm₂, he₂⟩ := generatedBlockExchange_exec_cost body
    hd pay hhd hpay hQ bank hbank hT str tmp hst hstr htmp n a b w hab hb hR hB l hl hlB h8
    rg hrg cfg hcfg hbankRaw hstrRaw htmpRaw work aux ctmp hworkRaw hauxRaw hctmpRaw hregs hsources
    rowBits bits L hBin hrow hrowNe hrowValue hbits hbitsValue v₁ S₁ hL
    ((hkeep str hstrSetup).trans hsrc) ((hkeep tmp htmpSetup).trans htmp0)
    (by simpa only [hbankKeep] using hpay0) (by simpa only [hbankKeep] using hpriv)
    (by simpa only [hbankKeep] using hhdr0)
    ((hheaderKeep (.base .rows) (by simp) (by simp) (by simp) (by simp)).trans hrows)
    ((hheaderKeep (.base .block) (by simp) (by simp) (by simp) (by simp)).trans hblock)
    (by simp [S₁, canonical]) hrowExp hgapExp hlowerExp
    (by intro k; rw [hheaderKeep _ (by simp) (by simp) (by simp) (by simp)]; exact hraw0 k)
    (by intro k; rw [hheaderKeep _ (by simp) (by simp) (by simp) (by simp)]; exact hscratch k)
    ((hheaderKeep .triple (by simp) (by simp) (by simp) (by simp)).trans htriple)
    ((hkeep work hworkSetup).trans hw) ((hkeep aux hauxSetup).trans ha) ((hkeep ctmp hctmpSetup).trans hc0)
    (by simpa only [hbankKeep] using hother)
  let out := (moveRecs (blockExchangeRank n a b w R hab hb) l).flatten
  let S₂ : Stacks T (prime + K) := { S₁ with R := Function.update S₁.R str out }
  let keys := exchangeBinarySetupPrivate ex canonical
  have hkeys : keys.Nodup := by
    simp [keys, exchangeBinarySetupPrivate, exchangeExponentPrivate, List.nodup_cons, hex.eq_iff, hcanonical']
  obtain ⟨v₃, hu₃, he₃⟩ := metadataClean_exec body keys hkeys v₂ S₂
  have hcost : metadataCleanCost S₂.R keys = metadataCleanCost S₁.R keys := by
    apply metadataCleanCost_congr
    intro j hj
    have hne : j ≠ str := by intro he; subst j; exact hstrSetup hj
    exact Function.update_of_ne hne _ _
  have hfinal : metadataCleared S₂.R keys = Function.update S.R str out := by
    rw [metadataCleared_update _ _ _ _ hstrSetup]
    congr 1
    exact exchangeBinarySetup_restore S.R ex canonical bits n a b w hcanonical0 hlower0 hrow0 hgap0
  rw [hcost, hfinal] at he₃
  have hclean := exchangeBinarySetup_cleanCost S.R ex hex canonical hcanonical bits Lc n a b w hbitsLength hab hb
  have hprice : generatedExchangeBound bank R B n a b w L rowBits.length bits.length S₁ ≤
      generatedExchangeBound bank R B n a b w L rowBits.length Lc S := by
    unfold generatedExchangeBound
    simp only [hbankKeep]
    gcongr
  have hm₁' : (m₁ : ℝ) ≤ (3 * (Lc * (4 * n + 31) + 2 * n + 26) + 10 * Lc + 12 : ℕ) := by exact_mod_cast hm₁
  have hclean' : (metadataCleanCost S₁.R keys : ℝ) ≤ (2 * n + 2 * Lc + 9 : ℕ) := by exact_mod_cast hclean
  refine ⟨v₃, m₁ + (m₂ + metadataCleanCost S₁.R keys), hu₃.trans (hu₂.trans hu₁), ?_,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  simp only [Nat.cast_add] at hm₁' hclean' ⊢
  linarith only [hm₁', hm₂, hprice, hclean']

end IntegerMultBounds.MathlibTM2.Routing
