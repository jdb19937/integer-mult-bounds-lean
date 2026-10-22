module

public import IntegerMultBounds.MathlibTM2.Routing.ExchangeHeaderExec
public import IntegerMultBounds.MathlibTM2.Routing.InstalledBlockExchange

/-! Generation, installation, actual exchange, and cleanup of both header banks. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable def installedExchangePrice {t₀ T K : ℕ}
    (bank : Fin (swapT t₀) → Fin T) (cfg : Fin 5 → Fin T) (hd : Fin 5 → Fin t₀)
    (R B n w : ℕ) (S : Stacks T (prime + K)) : ℝ :=
  (metadataInstallCost S.R (exchangeInstallJobs cfg bank hd) : ℕ) +
    (3 * swapConst * (T + 12 * swapT t₀ + 5 : ℕ) * (R * 2 ^ n * B : ℕ) *
      ((max 1 w : ℕ) : ℝ) ^ Parameters.tau +
      (6 * ∑ j, (metadataInstalled S.R (exchangeInstallJobs cfg bank hd) (bank j)).length +
        34 * (R * 2 ^ n * B) + 2 * T + 6 * swapT t₀ + 23 : ℕ)) +
    (metadataCleanCost (metadataInstalled S.R (exchangeInstallJobs cfg bank hd))
      ((exchangeInstallJobs cfg bank hd).map MetadataJob.dst) : ℕ)

theorem generatedBlockExchange_exec {t₀ T Q K : ℕ} {U F : Type}
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
    (rowBits widthBits : List Bool) (L : ℕ) (hBin : B < 2 ^ L)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ []) (hrowValue : Counter.value rowBits = R)
    (hwidth : GrowingCounterData.Canonical widthBits) (hwidthValue : Counter.value widthBits = w)
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hL : ∀ j, S.L j = []) (hsrc : S.R str = l.flatten) (htmp0 : S.R tmp = [])
    (hpay0 : S.R (bank (reg pay)) = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (bank j) = [])
    (hhdr0 : ∀ k, S.R (bank (reg (hd k))) = [])
    (hrows : S.R (rg (.base .rows)) = rowBits.map bitSymbol)
    (hblock : S.R (rg (.base .block)) = binSyms L B)
    (hwidthInput : S.R (rg (.base .target)) = widthBits.map bitSymbol)
    (hrowExp : (S.R (rg (.base .rowExp))).length = n - (b + w))
    (hgapExp : (S.R (rg (.base .gapExp))).length = b - a - w)
    (hlowerExp : (S.R (rg .lowerExp)).length = a)
    (hraw0 : ∀ k, S.R (rg (.base (.header k))) = [])
    (hscratch : ∀ i, S.R (rg (.base (.scratch i))) = []) (htriple : S.R (rg .triple) = [])
    (hw : S.R work = []) (ha : S.R aux = []) (hc0 : S.R ctmp = [])
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (bank (reg i)), s ≠ blank ∧ s.val < prime + 4) :
    ∃ (payload : List Bool) (v' : HS T Q (prime + K) U) (m : ℕ),
      GrowingCounterData.Canonical payload ∧ Counter.value payload = 2 ^ a * (3 * B) ∧
      payload.length ≤ a + L + 2 ∧ v'.user = v.user ∧
      (m : ℝ) ≤ (6 * (rowBits.length + (n - (b + w))) + 6 * (b - a - w) + 52 * L +
        6 * a + 12 * widthBits.length + 226 : ℕ) +
        installedExchangePrice bank cfg hd R B n w
          { S with R := elementaryHeaderBank S.R (fun r => rg (.base r)) (exchangeHeaderWords rowBits payload widthBits (n - (b + w)) (b - a - w)) } +
        (2 * ((n - (b + w)) + rowBits.length + (b - a - w) + 1 + payload.length + 2 * widthBits.length) + 11 : ℕ) ∧
      Exec body (.seq (exchangeHeaderProgram rg)
        (.seq (installedBlockExchangeProgram cfg bank hd work aux ctmp
          (swapPass hd pay hhd hQ bank hbank hT str tmp)) (metadataClean (exchangeHeaderPrivate rg)))) (mk v S) m
        (mk v' { S with R := Function.update S.R str (moveRecs (blockExchangeRank n a b w R hab hb) l).flatten }) := by
  obtain ⟨payload, v₁, m₁, hcanonical, hvalue, hlength, hu₁, hm₁, he₁⟩ :=
    exchangeHeader_exec body rg hrg rowBits widthBits L B hBin hB v S hrows hblock hwidthInput hraw0 hscratch htriple
  rw [hrowExp, hgapExp, hlowerExp] at hm₁
  rw [hlowerExp] at hvalue hlength
  rw [hrowExp, hgapExp] at he₁
  let words := exchangeHeaderWords rowBits payload widthBits (n - (b + w)) (b - a - w)
  let S₁ : Stacks T (prime + K) := { S with R := elementaryHeaderBank S.R (fun r => rg (.base r)) words }
  have hkeep (j : Fin T) (hj : j ∉ exchangeHeaderPrivate rg) : S₁.R j = S.R j :=
    exchangeHeaderBank_keep S.R rg words j hj
  have hbankKeep (j : Fin (swapT t₀)) : S₁.R (bank j) = S.R (bank j) := hkeep _ (hbankRaw j)
  obtain ⟨hc, hv⟩ := exchangeHeaderWords_valid n a b w R B hab rowBits payload widthBits
    hrow hrowNe hrowValue hcanonical hvalue hwidth hwidthValue
  have hraw : ∀ k, S₁.R (cfg k) = (words k).map bitSymbol := by
    intro k
    rw [hcfg]
    fin_cases k <;> simp [S₁, elementaryHeaderBank, hrg.eq_iff]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := installedBlockExchange_exec body hd pay hhd hpay hQ bank hbank hT
    str tmp hst hstr htmp n a b w hab hb hR hB l hl hlB h8 cfg work aux ctmp hregs hsources words hv hc v₁ S₁ hL
    ((hkeep str hstrRaw).trans hsrc) ((hkeep tmp htmpRaw).trans htmp0)
    (by simpa only [hbankKeep] using hpay0) (by simpa only [hbankKeep] using hpriv)
    (by simpa only [hbankKeep] using hhdr0) hraw
    ((hkeep work hworkRaw).trans hw) ((hkeep aux hauxRaw).trans ha) ((hkeep ctmp hctmpRaw).trans hc0)
    (by simpa only [hbankKeep] using hother)
  let out := (moveRecs (blockExchangeRank n a b w R hab hb) l).flatten
  let S₂ : Stacks T (prime + K) := { S₁ with R := Function.update S₁.R str out }
  obtain ⟨v₃, hu₃, he₃⟩ := metadataClean_exec body (exchangeHeaderPrivate rg)
    (by simp [exchangeHeaderPrivate, List.nodup_cons, hrg.eq_iff]) v₂ S₂
  have hcost : metadataCleanCost S₂.R (exchangeHeaderPrivate rg) =
      2 * ((n - (b + w)) + rowBits.length + (b - a - w) + 1 + payload.length + 2 * widthBits.length) + 11 := by
    trans metadataCleanCost S₁.R (exchangeHeaderPrivate rg)
    · apply metadataCleanCost_congr
      intro j hj
      have hne : j ≠ str := by intro he; subst j; exact hstrRaw hj
      exact Function.update_of_ne hne _ _
    · exact exchangeHeader_cleanCost S.R rg hrg rowBits payload widthBits _ _
  have hfinal : metadataCleared S₂.R (exchangeHeaderPrivate rg) = Function.update S.R str out := by
    rw [metadataCleared_update _ _ _ _ hstrRaw]
    congr 1
    exact exchangeHeaderBank_restore S.R rg words hraw0
  rw [hcost, hfinal] at he₃
  refine ⟨payload, v₃, m₁ + (m₂ + _), hcanonical, hvalue, hlength,
    hu₃.trans (hu₂.trans hu₁), ?_, Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  have hm₁' : (m₁ : ℝ) ≤ (6 * (rowBits.length + (n - (b + w))) + 6 * (b - a - w) +
      52 * L + 6 * a + 12 * widthBits.length + 226 : ℕ) := by exact_mod_cast hm₁
  change (m₂ : ℝ) ≤ installedExchangePrice bank cfg hd R B n w S₁ at hm₂
  simp only [Nat.cast_add] at hm₁' ⊢
  linarith only [hm₁', hm₂]

end IntegerMultBounds.MathlibTM2.Routing
