module

public import IntegerMultBounds.MathlibTM2.Routing.BlockExchangeExec
public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-! Executed header installation, interval exchange and complete header cleanup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable def exchangeInstallJobs {t₀ T : ℕ} (cfg : Fin 5 → Fin T)
    (bank : Fin (swapT t₀) → Fin T) (hd : Fin 5 → Fin t₀) : List (MetadataJob T) :=
  (List.finRange 5).map (fun k => .copy (cfg k) (bank (reg (hd k))) true)

noncomputable def installedBlockExchangeProgram {t₀ T Q A : ℕ} {P U : Type}
    (cfg : Fin 5 → Fin T) (bank : Fin (swapT t₀) → Fin T) (hd : Fin 5 → Fin t₀)
    (work aux ctmp : Fin T) (core : Pr P T Q A U) : Pr P T Q A U :=
  .seq (metadataInstall work aux ctmp (exchangeInstallJobs cfg bank hd))
    (.seq core (metadataClean ((exchangeInstallJobs cfg bank hd).map MetadataJob.dst)))

/-- All five raw headers are copied once, with separators added by execution. -/
theorem exchangeInstall_cost {t₀ T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (cfg : Fin 5 → Fin T) (bank : Fin (swapT t₀) → Fin T) (hd : Fin 5 → Fin t₀)
    (hs : Fin 5 → List Bool) (hraw : ∀ k, R (cfg k) = (hs k).map bitSymbol) :
    metadataInstallCost R (exchangeInstallJobs cfg bank hd) = 6 * (∑ k, (hs k).length) + 36 := by
  simp [exchangeInstallJobs, List.finRange_succ, metadataInstallCost, MetadataJob.cost,
    hraw, Fin.sum_univ_succ]
  omega

/-- Installed separators are included in the exact final cleanup price. -/
theorem exchangeInstall_cleanCost {t₀ T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (cfg : Fin 5 → Fin T) (bank : Fin (swapT t₀) → Fin T) (hbank : Function.Injective bank)
    (hd : Fin 5 → Fin t₀) (hhd : Function.Injective hd)
    (hs : Fin 5 → List Bool) (hraw : ∀ k, R (cfg k) = (hs k).map bitSymbol) :
    metadataCleanCost (metadataInstalled R (exchangeInstallJobs cfg bank hd))
      ((exchangeInstallJobs cfg bank hd).map MetadataJob.dst) = 2 * (∑ k, (hs k).length) + 21 := by
  simp [exchangeInstallJobs, List.finRange_succ, metadataCleanCost, metadataInstalled,
    MetadataJob.dst, MetadataJob.contents, hraw, hbank.eq_iff,
    BinaryInterchangeRun.slot_injective.eq_iff, hhd.eq_iff, Fin.sum_univ_succ]
  omega

theorem installedBlockExchange_exec {t₀ T Q K : ℕ} {U F : Type}
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
    (cfg : Fin 5 → Fin T) (work aux ctmp : Fin T)
    (hregs : ∀ k, [cfg k, bank (reg (hd k)), work, aux, ctmp].Nodup)
    (hsources : ∀ k j, cfg k ≠ bank (reg (hd j)))
    (hs : Fin 5 → List Bool)
    (hv : ∀ k, Counter.value (hs k) = swapValues
      (blockExchangeDimensions n a b w R B).1
      (blockExchangeDimensions n a b w R B).2.1
      (blockExchangeDimensions n a b w R B).2.2 w w k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k))
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hL : ∀ j, S.L j = []) (hsrc : S.R str = l.flatten) (htmp0 : S.R tmp = [])
    (hpay0 : S.R (bank (reg pay)) = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (bank j) = [])
    (hhdr0 : ∀ k, S.R (bank (reg (hd k))) = [])
    (hraw : ∀ k, S.R (cfg k) = (hs k).map bitSymbol)
    (hw : S.R work = []) (ha : S.R aux = []) (hc0 : S.R ctmp = [])
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (bank (reg i)), s ≠ blank ∧ s.val < prime + 4) :
    ∃ (v' : HS T Q (prime + K) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ (metadataInstallCost S.R (exchangeInstallJobs cfg bank hd) : ℕ) +
        (3 * swapConst * (T + 12 * swapT t₀ + 5 : ℕ) *
          (R * 2 ^ n * B : ℕ) * ((max 1 w : ℕ) : ℝ) ^ Parameters.tau +
          (6 * ∑ j, ((metadataInstalled S.R (exchangeInstallJobs cfg bank hd)) (bank j)).length +
            34 * (R * 2 ^ n * B) + 2 * T + 6 * swapT t₀ + 23 : ℕ)) +
        (metadataCleanCost (metadataInstalled S.R (exchangeInstallJobs cfg bank hd))
          ((exchangeInstallJobs cfg bank hd).map MetadataJob.dst) : ℕ) ∧
      Exec body (installedBlockExchangeProgram cfg bank hd work aux ctmp
        (swapPass hd pay hhd hQ bank hbank hT str tmp)) (mk v S) m
        (mk v' { S with R := Function.update S.R str (moveRecs (blockExchangeRank n a b w R hab hb) l).flatten }) := by
  let jobs := exchangeInstallJobs cfg bank hd
  let keys := jobs.map MetadataJob.dst
  let S₁ : Stacks T (prime + K) := { S with R := metadataInstalled S.R jobs }
  have hkeys : keys.Nodup := by
    simpa only [keys, jobs, exchangeInstallJobs, List.map_map, Function.comp_def, MetadataJob.dst] using
      (List.nodup_finRange 5).map (hbank.comp (BinaryInterchangeRun.slot_injective.comp hhd))
  have hkeep (j : Fin T) (hj : ∀ k, j ≠ bank (reg (hd k))) : S₁.R j = S.R j := by
    apply metadataInstalled_keep
    simp only [jobs, exchangeInstallJobs, List.map_map, Function.comp_def, MetadataJob.dst, List.mem_map]
    rintro ⟨k, _, he⟩
    exact hj k he.symm
  have hbankKeep (j : Fin (swapT t₀)) (hj : ∀ k, j ≠ reg (hd k)) : S₁.R (bank j) = S.R (bank j) :=
    hkeep _ (fun k he => hj k (hbank he))
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := metadataInstall_exec body jobs work aux ctmp hkeys
    (by intro job hj; obtain ⟨k, _, rfl⟩ := List.mem_map.mp hj; exact hregs k)
    (by
      intro job hj other ho
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hj
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp ho
      exact hsources k j)
    v S (by intro job hj; obtain ⟨k, _, rfl⟩ := List.mem_map.mp hj; trivial)
    (by intro job hj; obtain ⟨k, _, rfl⟩ := List.mem_map.mp hj; exact hhdr0 k) hw ha hc0
  have hhdr : ∀ k, S₁.R (bank (reg (hd k))) = separator :: (hs k).map bitSymbol := by
    intro k
    have h := metadataInstalled_at S.R jobs hkeys (.copy (cfg k) (bank (reg (hd k))) true)
      (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩)
    simpa only [MetadataJob.dst, MetadataJob.contents, Bool.true_eq, ite_true, hraw, List.singleton_append] using h
  have hpay₁ : S₁.R (bank (reg pay)) = [] := by
    rw [hbankKeep]
    · exact hpay0
    · intro k he
      exact hpay k (BinaryInterchangeRun.slot_injective he).symm
  have hpriv₁ : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S₁.R (bank j) = [] := by
    intro j hj
    rw [hbankKeep]
    · exact hpriv j hj
    · intro k he
      have heval := congrArg Fin.val he
      change j.val = (hd k).val at heval
      have := (hd k).isLt
      omega
  have hother₁ : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S₁.R (bank (reg i)), s ≠ blank ∧ s.val < prime + 4 := by
    intro i hi hk
    rw [hbankKeep _ (fun k he => hk k (BinaryInterchangeRun.slot_injective he).symm)]
    exact hother i hi hk
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := blockExchange_exec body hd pay hhd hQ bank hbank hT
    str tmp hst hstr htmp n a b w hab hb hR hB l hl hlB h8 hs hv hc v₁ S₁ hL
    ((hkeep str (fun k => (hstr _).symm)).trans hsrc)
    ((hkeep tmp (fun k => (htmp _).symm)).trans htmp0) hpay₁ hpriv₁ hhdr hother₁
  let out := (moveRecs (blockExchangeRank n a b w R hab hb) l).flatten
  let S₂ : Stacks T (prime + K) := { S₁ with R := Function.update S₁.R str out }
  have hstrKeys : str ∉ keys := by
    simp only [keys, jobs, exchangeInstallJobs, List.map_map, Function.comp_def, MetadataJob.dst, List.mem_map]
    rintro ⟨k, _, he⟩
    exact hstr _ he
  obtain ⟨v₃, hu₃, he₃⟩ := metadataClean_exec body keys hkeys v₂ S₂
  have hcost : metadataCleanCost S₂.R keys = metadataCleanCost S₁.R keys := by
    apply metadataCleanCost_congr
    intro j hj
    have hne : j ≠ str := by intro he; subst j; exact hstrKeys hj
    exact Function.update_of_ne hne _ _
  have hfinal : metadataCleared S₂.R keys = Function.update S.R str out := by
    rw [metadataCleared_update _ _ _ _ hstrKeys]
    congr 1
    exact metadataClean_restore S.R jobs
      (by intro job hj; obtain ⟨k, _, rfl⟩ := List.mem_map.mp hj; exact hhdr0 k)
  rw [hcost, hfinal] at he₃
  refine ⟨v₃, m₁ + (m₂ + metadataCleanCost S₁.R keys), hu₃.trans (hu₂.trans hu₁), ?_,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  have hm₁' : (m₁ : ℝ) ≤ (metadataInstallCost S.R jobs : ℕ) := by exact_mod_cast hm₁
  dsimp only [S₁, keys, jobs] at hm₁' hm₂ ⊢
  simp only [Nat.cast_add] at hm₂ ⊢
  linarith only [hm₁', hm₂]

end IntegerMultBounds.MathlibTM2.Routing
