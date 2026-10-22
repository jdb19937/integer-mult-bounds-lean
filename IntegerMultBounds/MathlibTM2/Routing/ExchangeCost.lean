module

public import IntegerMultBounds.MathlibTM2.Routing.GeneratedBlockExchange
public import IntegerMultBounds.MathlibTM2.Routing.MetadataBankCost

/-! Exchange prices in original bank size and raw header lengths. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem installedExchangePrice_le {t₀ T K : ℕ}
    (bank : Fin (swapT t₀) → Fin T) (hbank : Function.Injective bank)
    (cfg : Fin 5 → Fin T) (hd : Fin 5 → Fin t₀) (hhd : Function.Injective hd)
    (R B n w : ℕ) (S : Stacks T (prime + K)) (hs : Fin 5 → List Bool)
    (hraw : ∀ k, S.R (cfg k) = (hs k).map bitSymbol) :
    installedExchangePrice bank cfg hd R B n w S ≤
      3 * swapConst * (T + 12 * swapT t₀ + 5 : ℕ) * (R * 2 ^ n * B : ℕ) *
        ((max 1 w : ℕ) : ℝ) ^ Parameters.tau +
      (6 * ∑ j, (S.R (bank j)).length + 14 * ∑ k, (hs k).length +
        34 * (R * 2 ^ n * B) + 2 * T + 6 * swapT t₀ + 110 : ℕ) := by
  let jobs := exchangeInstallJobs cfg bank hd
  have hsum := metadataInstalled_bankLength_le S.R bank hbank jobs
    (by
      intro job hj
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hj
      exact ⟨reg (hd k), rfl⟩)
  have hwords : (jobs.map (fun job => (job.contents S.R).length)).sum = (∑ k, (hs k).length) + 5 := by
    simp [jobs, exchangeInstallJobs, List.finRange_succ, MetadataJob.contents, hraw, Fin.sum_univ_succ]
    omega
  rw [hwords] at hsum
  have hnat : 6 * (∑ k, (hs k).length) + 36 +
      (6 * ∑ j, (metadataInstalled S.R jobs (bank j)).length +
        34 * (R * 2 ^ n * B) + 2 * T + 6 * swapT t₀ + 23) +
      (2 * (∑ k, (hs k).length) + 21) ≤
      6 * (∑ j, (S.R (bank j)).length) + 14 * (∑ k, (hs k).length) +
        34 * (R * 2 ^ n * B) + 2 * T + 6 * swapT t₀ + 110 := by omega
  have hreal := (Nat.cast_le (α := ℝ)).mpr hnat
  unfold installedExchangePrice
  rw [exchangeInstall_cost S.R cfg bank hd hs hraw,
    exchangeInstall_cleanCost S.R cfg bank hbank hd hhd hs hraw]
  dsimp only [jobs] at hreal
  simp only [Nat.cast_add] at hreal ⊢
  linarith only [hreal]

theorem generatedExchangePrice_le {t₀ T K : ℕ}
    (bank : Fin (swapT t₀) → Fin T) (hbank : Function.Injective bank)
    (rg : ExchangeHeaderReg → Fin T) (hrg : Function.Injective rg)
    (hbankRaw : ∀ j, bank j ∉ exchangeHeaderPrivate rg)
    (hd : Fin 5 → Fin t₀) (hhd : Function.Injective hd)
    (R B n w rowExp gapExp a L : ℕ) (S : Stacks T (prime + K))
    (rowBits payload widthBits : List Bool) (hlength : payload.length ≤ a + L + 2) :
    installedExchangePrice bank (fun k => rg (.base (.header k))) hd R B n w
      { S with R := elementaryHeaderBank S.R (fun r => rg (.base r)) (exchangeHeaderWords rowBits payload widthBits rowExp gapExp) } ≤
      3 * swapConst * (T + 12 * swapT t₀ + 5 : ℕ) * (R * 2 ^ n * B : ℕ) *
        ((max 1 w : ℕ) : ℝ) ^ Parameters.tau +
      (6 * ∑ j, (S.R (bank j)).length +
        14 * (rowExp + rowBits.length + gapExp + 1 + (a + L + 2) + 2 * widthBits.length) +
        34 * (R * 2 ^ n * B) + 2 * T + 6 * swapT t₀ + 110 : ℕ) := by
  let words := exchangeHeaderWords rowBits payload widthBits rowExp gapExp
  let S₁ : Stacks T (prime + K) := { S with R := elementaryHeaderBank S.R (fun r => rg (.base r)) words }
  have hraw : ∀ k, S₁.R (rg (.base (.header k))) = (words k).map bitSymbol := by
    intro k
    fin_cases k <;> simp [S₁, elementaryHeaderBank, hrg.eq_iff]
  have hkeep (j : Fin (swapT t₀)) : S₁.R (bank j) = S.R (bank j) :=
    exchangeHeaderBank_keep S.R rg words (bank j) (hbankRaw j)
  have hwords : (∑ k, (words k).length) =
      rowExp + rowBits.length + gapExp + 1 + payload.length + 2 * widthBits.length := by
    simp [words, exchangeHeaderWords, binaryPowerBits, Fin.sum_univ_succ]
    omega
  have h := installedExchangePrice_le bank hbank (fun k => rg (.base (.header k))) hd hhd
    R B n w S₁ words hraw
  simp only [hkeep, hwords] at h
  refine h.trans ?_
  gcongr

end IntegerMultBounds.MathlibTM2.Routing
