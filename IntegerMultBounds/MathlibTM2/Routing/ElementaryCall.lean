module

public import IntegerMultBounds.MathlibTM2.Routing.ElementarySetup
public import IntegerMultBounds.MathlibTM2.Routing.ElementaryXorExec
public import IntegerMultBounds.MathlibTM2.Routing.ConfigurationBatchClean

/-!
# A reusable elementary routing call from raw framed metadata

The actual loader, XOR program and cleanup run on one fixed bank. The only final
changes are the requested record permutation, the configuration cursor and its
rewind archive. Shared counter setup and raw-word generation are not supplied.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable def elementaryConfigKeys {t₀ T : ℕ} (rg : LayReg t₀ → Fin T) (hd : Fin 5 → Fin t₀) :=
  List.ofFn (elementaryConfigTarget rg hd)

noncomputable def elementaryCallProgram {t₀ T Q K : ℕ} {U P : Type}
    (rg : LayReg t₀ → Fin T) (hrg : Function.Injective rg)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T) (config saved : Fin T) :
    Pr P T Q (prime + K) U :=
  .seq (elementarySetup rg hd config saved)
    (.seq (elementaryXorProgram rg hrg hd pay hhd hQ hT) (metadataClean (elementaryConfigKeys rg hd)))

/-- One whole call executes from raw configuration, restoring its reusable bank. -/
theorem elementaryCall_exec {t₀ T Q K n R B : ℕ} {U P : Type}
    (body : P → Pr P T Q (prime + K) U) (rg : LayReg t₀ → Fin T)
    (hrg : Function.Injective rg) (hd : Fin 5 → Fin t₀) (pay : Fin t₀)
    (hhd : Function.Injective hd) (hpay : ∀ j, hd j ≠ pay)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T)
    (config saved : Fin T) (hcs : config ≠ saved)
    (hconfig : ∀ r, config ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
    (t s : Fin n) (hne : s ≠ t) (hR : 0 < R) (hB : 1 ≤ B)
    (headers : Fin 5 → List Bool)
    (hv : ∀ k, Counter.value (headers k) = swapValues
      (blockExchangeDimensions n (elementarySwapSpec t).a (elementarySwapSpec t).b (elementarySwapSpec t).w R B).1
      (blockExchangeDimensions n (elementarySwapSpec t).a (elementarySwapSpec t).b (elementarySwapSpec t).w R B).2.1
      (blockExchangeDimensions n (elementarySwapSpec t).a (elementarySwapSpec t).b (elementarySwapSpec t).w R B).2.2
      (elementarySwapSpec t).w (elementarySwapSpec t).w k)
    (hc : ∀ k, GrowingCounterData.Canonical (headers k))
    (rest : List (Fin (prime + K + 4))) (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hL : ∀ j, S.L j = []) (hcfg : ElementarySharedCfg rg S.R n (R * 2 ^ n) B 0)
    (hempty : ∀ key, S.R (elementaryConfigTarget rg hd key) = [])
    (hpay0 : S.R (rg (.sw (reg pay))) = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (rg (.sw j)) = [])
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ x ∈ S.R (rg (.sw (reg i))), x ≠ blank ∧ x.val < prime + 4)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlB : ∀ r ∈ l, r.length = B) (h8 : ∀ r ∈ l, ∀ x ∈ r, x.val < 8)
    (hstream : S.R (rg .str) = l.flatten)
    (hinput : S.R config = configurationWords
      (List.ofFn (elementaryConfigWord n ((elementarySwapSpec t).coordinate s).val headers)) ++ rest) :
    let words := List.ofFn (elementaryConfigWord n ((elementarySwapSpec t).coordinate s).val headers :
      Fin 6 → List (Fin (prime + K + 4)))
    let installed := elementaryLoaded S.R rg hd config saved n ((elementarySwapSpec t).coordinate s).val headers rest
    ∃ (v' : HS T Q (prime + K) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ configurationBatchCost words + elementaryXorCost rg t R B { S with R := installed } +
        metadataCleanCost installed (elementaryConfigKeys rg hd) ∧
      Exec body (elementaryCallProgram rg hrg hd pay hhd hQ hT config saved) (mk v S) m
        (mk v' { S with R := Function.update (Function.update (Function.update S.R config rest) saved ((configurationWords words).reverse ++ S.R saved)) (rg .str) (moveRecs (elementaryXorRank t s hne R) l).flatten }) := by
  dsimp only
  let source := ((elementarySwapSpec t).coordinate s).val
  let words := List.ofFn (elementaryConfigWord n source headers : Fin 6 → List (Fin (prime + K + 4)))
  let installed := elementaryLoaded S.R rg hd config saved n source headers rest
  let keys := elementaryConfigKeys rg hd
  have hkeys : (List.ofFn (elementaryConfigSlot rg hd)).map ConfigurationSlot.dst = keys := by
    simp [keys, elementaryConfigKeys, elementaryConfigSlot]
  have hn : keys.Nodup := hkeys ▸ elementaryConfigSlots_nodup rg hrg hd hhd
  have hstr : rg .str ∉ keys := by
    intro hm
    obtain ⟨key, he⟩ := List.mem_ofFn.mp hm
    rcases elementaryConfigTarget_role rg hd key with ⟨j, hj⟩ | hj <;>
      rw [hj] at he <;> simp [hrg.eq_iff] at he
  obtain ⟨v₁, hu₁, he₁, hcfg₁, hhdr₁⟩ := elementarySetup_exec body rg hrg hd hhd config saved hcs
    hconfig hsaved n (R * 2 ^ n) B 0 source headers rest v S hcfg hempty hinput
  have hstream₁ : installed (rg .str) = l.flatten := by
    exact (elementaryLoaded_keep S.R rg hrg hd config saved hconfig hsaved n source headers rest
      .str (by simp) (by simp) (by intro j; simp)).trans hstream
  have hkeep (j : Fin (swapT t₀)) (hj : ∀ k, j ≠ reg (hd k)) : installed (rg (.sw j)) = S.R (rg (.sw j)) :=
    elementaryLoaded_sw S.R rg hrg hd config saved hconfig hsaved n source headers rest j hj
  have hpay₁ : installed (rg (.sw (reg pay))) = [] := by
    rw [hkeep _ (fun k he => hpay k (swapReg_injective he).symm)]
    exact hpay0
  have hpriv₁ : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → installed (rg (.sw j)) = [] := by
    intro j hj
    rw [hkeep j (by
      intro k he
      have he' := congrArg Fin.val he
      rw [reg_val] at he'
      have hk := (hd k).isLt
      omega)]
    exact hpriv j hj
  have hother₁ : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ x ∈ installed (rg (.sw (reg i))), x ≠ blank ∧ x.val < prime + 4 := by
    intro i hi hk
    rw [hkeep _ (fun k he => hk k (swapReg_injective he).symm)]
    exact hother i hi hk
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := elementaryXor_exec body rg hrg hd pay hhd hQ hT t s hne
    hR hB headers hv hc v₁ { S with R := installed } hL hcfg₁ hpay₁ hpriv₁ hhdr₁ hother₁ l hl hlB h8 hstream₁
  let routed := (moveRecs (elementaryXorRank t s hne R) l).flatten
  obtain ⟨v₃, hu₃, he₃⟩ := metadataClean_exec body keys hn v₂
    { S with R := Function.update installed (rg .str) routed }
  have hrestore : metadataCleared installed keys =
      Function.update (Function.update S.R config rest) saved ((configurationWords words).reverse ++ S.R saved) := by
    rw [← hkeys]
    exact configurationBatchClean_restore S.R config (rg .tmp) saved (hconfig .tmp) hcs
      (hsaved .tmp).symm _ words (by simp [words])
      (elementaryConfigSlots_separate rg hrg hd config saved hconfig hsaved) rest hinput hcfg.tmp
      (by intro slot hs; obtain ⟨key, rfl⟩ := List.mem_ofFn.mp hs; exact hempty key)
  have hfinal := metadataCleared_update installed keys (rg .str) routed hstr
  rw [hrestore] at hfinal
  have hcost : metadataCleanCost (Function.update installed (rg .str) routed) keys = metadataCleanCost installed keys := by
    apply metadataCleanCost_congr
    intro j hj
    have hne : j ≠ rg .str := by
      intro he
      apply hstr
      simpa only [he] using hj
    exact Function.update_of_ne hne _ _
  rw [hfinal, hcost] at he₃
  refine ⟨v₃, configurationBatchCost words + (m₂ + metadataCleanCost installed keys),
    hu₃.trans (hu₂.trans hu₁), ?_, Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  rw [Nat.cast_add, Nat.cast_add]
  linarith only [hm₂]

end IntegerMultBounds.MathlibTM2.Routing
