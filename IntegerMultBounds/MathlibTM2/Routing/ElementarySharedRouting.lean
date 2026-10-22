module

public import IntegerMultBounds.MathlibTM2.Routing.ElementarySharedProgram
public import IntegerMultBounds.MathlibTM2.Routing.ElementaryLoopCost

/-!
# Elementary routing with executed shared-counter setup and cleanup

The program starts with binary counter inputs and a raw instruction stream.
Every setup, routing and cleanup phase executes and is charged. Generating the
binary inputs and canonical instruction words is still a separate obligation.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable {t₀ T Q K : ℕ} {U P : Type}

/-- Complete elementary execution from raw shared metadata and instructions. -/
theorem elementarySharedRouting_exec {n rows B : ℕ}
    (body : P → Pr P T Q (prime + K) U) (rg : LayReg t₀ → Fin T) (hrg : Function.Injective rg)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd) (hpay : ∀ j, hd j ≠ pay)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T)
    (config saved : Fin T) (hcs : config ≠ saved)
    (hconfig : ∀ r, config ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
    (cfg : Fin 4 → Fin T) (work tmp ctmp : Fin T) (wb wm : ℕ)
    (hregs : ∀ key, [(elementarySharedJob rg cfg wb wm B (rows * 2 ^ n) key).src,
      elementarySharedTarget rg key, work, tmp, ctmp].Nodup)
    (hsources : ∀ key other, (elementarySharedJob rg cfg wb wm B (rows * 2 ^ n) key).src ≠
      elementarySharedTarget rg other)
    (hrows : 0 < rows) (hB : 1 ≤ B) (hn : n ≤ B) (ds : List (ElementaryInstruction n))
    (hvalid : ∀ d ∈ ds, d.Valid rows B)
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (data : ElementarySharedData cfg wb wm n B (rows * 2 ^ n) S.R)
    (hL : ∀ j, S.L j = [])
    (hempty : ∀ key, S.R (elementarySharedTarget rg key) = [])
    (hw : S.R work = []) (ht : S.R tmp = []) (hc : S.R ctmp = [])
    (hblank : ∀ r : LayReg t₀, r ≠ .ctrB → r ≠ .cnt → r ≠ .fld → r ≠ .mA →
      r ≠ .str → r ≠ .mB → (∀ j, r ≠ .sw j) → S.R (rg r) = [])
    (hmeta : ∀ key, S.R (elementaryConfigTarget rg hd key) = [])
    (hpay0 : S.R (rg (.sw (reg pay))) = [])
    (hprivate : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (rg (.sw j)) = [])
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ x ∈ S.R (rg (.sw (reg i))), x ≠ blank ∧ x.val < prime + 4)
    (harchive : S.R saved = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = rows * 2 ^ n)
    (hlB : ∀ r ∈ l, r.length = B) (h8 : ∀ r ∈ l, ∀ x ∈ r, x.val < 8)
    (hstream : S.R (rg .str) = l.flatten) (hinput : S.R config = elementaryFrames ds) :
    let jobs := elementarySharedJobs rg cfg wb wm B (rows * 2 ^ n)
    let S₁ : Stacks T (prime + K) := { S with R := metadataInstalled S.R jobs }
    ∃ (v' : HS T Q (prime + K) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ (metadataInstallCost S.R jobs : ℕ) +
        ((ds.length : ℝ) * (elementaryBaseCost rg n rows B S₁ + 2) +
          (12 * swapT t₀ + 20 : ℕ) * (elementaryFrames (A := prime + K) ds).length + 4) +
        (metadataCleanCost S₁.R (jobs.map MetadataJob.dst) : ℕ) ∧
      Exec body (elementarySharedProgram rg cfg work tmp ctmp wb wm B (rows * 2 ^ n)
        (elementaryRoutingProgram rg hrg hd pay hhd hQ hT config saved)) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg .str) (moveRecs (elementaryInstructionsRank rows ds) l).flatten }) := by
  dsimp only
  apply elementarySharedProgram_exec body rg hrg cfg work tmp ctmp wb wm n B (rows * 2 ^ n)
    hregs hsources v S data hempty hw ht hc
  intro v₁
  let S₁ : Stacks T (prime + K) :=
    { S with R := metadataInstalled S.R (elementarySharedJobs rg cfg wb wm B (rows * 2 ^ n)) }
  have hkeep (k : Fin T) (hk : ∀ key, k ≠ elementarySharedTarget rg key) : S₁.R k = S.R k :=
    elementarySharedSetup_keep rg cfg wb wm B (rows * 2 ^ n) S.R k hk
  have hready : ElementaryLoopReady rg hd pay S₁.R n rows B :=
    elementarySharedSetup_ready rg hrg hd pay cfg wb wm n rows B S.R data hblank hmeta hpay0 hprivate hother
  have hsaved₁ : S₁.R saved = [] := by
    rw [hkeep]
    · exact harchive
    · intro key
      fin_cases key <;> exact hsaved _
  have hconfig₁ : S₁.R config = elementaryFrames ds := by
    rw [hkeep]
    · exact hinput
    · intro key
      fin_cases key <;> exact hconfig _
  have hstream₁ : S₁.R (rg .str) = l.flatten := by
    rw [hkeep]
    · exact hstream
    · intro key
      fin_cases key <;> simp [elementarySharedTarget, hrg.eq_iff]
  exact elementaryRouting_exec_le body rg hrg hd pay hhd hpay hQ hT config saved hcs hconfig hsaved
    hrows hB hn ds hvalid v₁ S₁ hL hready hsaved₁ l hl hlB h8 hstream₁ hconfig₁

end IntegerMultBounds.MathlibTM2.Routing
