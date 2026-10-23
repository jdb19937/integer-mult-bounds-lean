module

public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactScratch
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveEmbedded
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Compile eleven descriptors, execute exact R2 and erase the generated
tables. Only the record stream changes; every phase is charged. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable section

variable {Q K : ℕ} {P U : Type}
variable (ρ n m X rb scale : ℕ) (active : Fin n → Bool)
  (s : Fin n → SlotSource (routingParameters ρ n m (Nat.clog 2 scale)) X)

local notation "p₀" => routingParameters ρ n m (Nat.clog 2 scale)
local notation "hG₀" => And.left (routingParameters_guards ρ n m (Nat.clog 2 scale))
local notation "hK₀" => And.left (And.right (routingParameters_guards ρ n m (Nat.clog 2 scale)))

theorem exactSelectiveCompact_exec (body : P → Pr P repairT Q (prime + K) U)
    (body' : P → Pr P repairCompactT Q (prime + K) U)
    (hbody : ∀ f, body' f = embProg compactDescriptorCore id (body f))
    (Lw Lg L : Fin 11 → ℕ)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS repairCompactT Q (prime + K) U) (S : Stacks repairCompactT (prime + K))
    (data : RepairPendingDescriptorData p₀ X rb wb wm wp wk R B
      (repairCanonicalHeaders p₀ X rb R B) (embStk compactDescriptorCore S).R)
    (hempty : ∀ key, S.R (compactDescriptorCore (repairSetupTarget key)) = [])
    (hL : ∀ j, S.L (compactDescriptorCore j) = []) (hblank : ∀ j, RepairBlank j → S.R (compactDescriptorCore j) = [])
    (hwidthFit : ∀ j, L j < 2 ^ Lw j) (hW : ∀ j, repairCompactSourceWidth p₀ X (repairDescriptorKey j) + 1 < 2 ^ L j)
    (hsize : ∀ j, repairCompactRows p₀ (repairDescriptorKey j) < 2 ^ Lg j)
    (hwidth : ∀ j, S.R (compactDescriptorAux (.width j)) = binSyms (Lw j) (L j))
    (hsourceWidth : ∀ j, S.R (compactDescriptorAux (.sourceWidth j)) = binSyms (L j) (repairCompactSourceWidth p₀ X (repairDescriptorKey j) + 1))
    (hinput : ∀ j, S.R (compactDescriptorAux (.input j)) = selectorRunFrames (Lg j) (L j) (SparseSelectorRun.compress (repairCompactIndices p₀ X hG₀ hK₀ active s j).reverse).reverse)
    (hscratch : ∀ r : CompactDescriptorRole 11,
      (∀ k, r ≠ .input k) → (∀ k, r ≠ .width k) → (∀ k, r ≠ .sourceWidth k) → S.R (compactDescriptorAux r) = [])
    (hdesc : ∀ d, S.R (compactDescriptorCore (repairDescriptorSource d)) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (hsrc : S.R (compactDescriptorCore repairHost.src) = l.flatten) :
    let S₁ : Stacks repairCompactT (prime + K) := { S with R := compactDescriptorBankGenerated S.R (repairCompactJobs p₀ X hG₀ hK₀ active s Lw Lg L) }
    let jobs := repairJobs p₀ X rb wb wm wp wk R B
    let installed := metadataInstalled (embStk compactDescriptorCore S₁).R jobs
    ∃ (v' : HS repairCompactT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ compactDescriptorBatchCost (repairCompactJobs p₀ X hG₀ hK₀ active s Lw Lg L) +
        metadataInstallCost (embStk compactDescriptorCore S₁).R jobs +
        repairDensityCoreCost p₀ X rb R B scale { embStk compactDescriptorCore S₁ with R := installed } +
        metadataCleanCost installed repairTargets + compactDescriptorEraseCost (repairCompactJobs p₀ X hG₀ hK₀ active s Lw Lg L) ∧
      Exec body' (.seq (compactDescriptorBatch (repairCompactJobs p₀ X hG₀ hK₀ active s Lw Lg L))
        (.seq (embProg compactDescriptorCore id (repairProgram hQ hA)) (metadataClean ((repairCompactJobs p₀ X hG₀ hK₀ active s Lw Lg L).map CompactDescriptorJob.dst))))
        (mk v S) steps
        (mk v' { S with R := Function.update S.R (compactDescriptorCore repairHost.src) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  dsimp only
  let cfg := repairCompactJobs p₀ X hG₀ hK₀ active s Lw Lg L
  let S₁ : Stacks repairCompactT (prime + K) := { S with R := compactDescriptorBankGenerated S.R cfg }
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := repairCompactBank_exec p₀ X hG₀ hK₀ active s body' Lw Lg L v S
    hwidthFit hW hsize hwidth hsourceWidth hinput hscratch
  have hd : RepairSetupData p₀ X rb hG₀ hK₀ active s wb wm wp wk R B
      (repairCanonicalHeaders p₀ X rb R B) (embStk compactDescriptorCore S₁).R :=
    data.compactGenerated p₀ X rb hG₀ hK₀ active s Lw Lg L hdesc
  have hs₁ : S₁.R (compactDescriptorCore repairHost.src) = l.flatten := by
    change compactDescriptorBankGenerated S.R cfg (compactDescriptorCore repairHost.src) = l.flatten
    rw [repairCompactBank_core_keep p₀ X hG₀ hK₀ active s Lw Lg L S.R repairHost.src (fun d => ?_)]
    · exact hsrc
    · rw [repairDescriptorSource_eq]
      exact (repairSetup_source_src _).symm
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := exactSelectiveEmbedded_exec ρ n m X rb scale active s body
    compactDescriptorCore compactDescriptorCore_injective id body' hbody hQ hA hscale hn hR hB hrb hs v₁ S₁ hd
    (repairCompactBank_targets p₀ X hG₀ hK₀ active s Lw Lg L S.R hempty) hL
    (repairCompactBank_blank p₀ X hG₀ hK₀ active s Lw Lg L S.R hblank) l hl hlen hs₁
  obtain ⟨v₃, hu₃, he₃⟩ := repairCompactClean_exec p₀ X hG₀ hK₀ active s body' Lw Lg L v₂ S
    (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten hdesc
  change v₂.user = v₁.user at hu₂
  have hu : v₃.user = v.user := hu₃.trans (hu₂.trans hu₁)
  refine ⟨v₃, m₁ + (m₂ + compactDescriptorEraseCost cfg), hu, ?_,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  have hc₁ : (m₁ : ℝ) ≤ compactDescriptorBatchCost cfg := by exact_mod_cast hm₁
  push_cast
  linarith

end
end IntegerMultBounds.MathlibTM2.Routing
