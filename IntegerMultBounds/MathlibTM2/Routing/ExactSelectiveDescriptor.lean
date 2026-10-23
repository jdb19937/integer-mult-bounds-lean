module

public import IntegerMultBounds.MathlibTM2.Routing.RepairDescriptorScratch
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

theorem exactSelectiveDescriptor_exec (body : P → Pr P repairT Q (prime + K) U)
    (body' : P → Pr P (repairT + (2 * 11 + 12)) Q (prime + K) U)
    (hbody : ∀ f, body' f = embProg descriptorCore id (body f))
    (L : Fin 11 → ℕ)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS (repairT + (2 * 11 + 12)) Q (prime + K) U) (S : Stacks (repairT + (2 * 11 + 12)) (prime + K))
    (data : RepairPendingDescriptorData p₀ X rb wb wm wp wk R B
      (repairCanonicalHeaders p₀ X rb R B) (embStk descriptorCore S).R)
    (hempty : ∀ key, S.R (descriptorCore (repairSetupTarget key)) = [])
    (hL : ∀ j, S.L (descriptorCore j) = []) (hblank : ∀ j, RepairBlank j → S.R (descriptorCore j) = [])
    (hfit : ∀ j, repairDescriptorWidth p₀ X (repairDescriptorKey j) < 2 ^ L j)
    (hwidth : ∀ j, S.R (descriptorBankReg j .width) = binSyms (L j) (repairDescriptorWidth p₀ X (repairDescriptorKey j)))
    (hinput : ∀ j, S.R (descriptorBankSelectors j) = descriptorSelectorFrames (L j)
      (repairDescriptorIndices p₀ X hG₀ hK₀ active s (repairDescriptorKey j)).reverse)
    (hscratch : ∀ i : Fin (2 * 11 + 12), 2 * 11 ≤ i.val → S.R (descriptorAux i) = [])
    (hdesc : ∀ d, S.R (descriptorCore (repairDescriptorSource d)) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (hsrc : S.R (descriptorCore repairHost.src) = l.flatten) :
    let S₁ : Stacks (repairT + (2 * 11 + 12)) (prime + K) := { S with R := descriptorBankGenerated S.R (repairDescriptorJobs p₀ X hG₀ hK₀ active s L) }
    let jobs := repairJobs p₀ X rb wb wm wp wk R B
    let installed := metadataInstalled (embStk descriptorCore S₁).R jobs
    ∃ (v' : HS (repairT + (2 * 11 + 12)) Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ descriptorBatchCost (repairDescriptorJobs p₀ X hG₀ hK₀ active s L) +
        metadataInstallCost (embStk descriptorCore S₁).R jobs +
        repairDensityCoreCost p₀ X rb R B scale { embStk descriptorCore S₁ with R := installed } +
        metadataCleanCost installed repairTargets + descriptorEraseCost (repairDescriptorJobs p₀ X hG₀ hK₀ active s L) ∧
      Exec body' (.seq (descriptorBatch (repairDescriptorJobs p₀ X hG₀ hK₀ active s L))
        (.seq (embProg descriptorCore id (repairProgram hQ hA)) (metadataClean ((repairDescriptorJobs p₀ X hG₀ hK₀ active s L).map DescriptorJob.dst))))
        (mk v S) steps
        (mk v' { S with R := Function.update S.R (descriptorCore repairHost.src) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  dsimp only
  let cfg := repairDescriptorJobs p₀ X hG₀ hK₀ active s L
  let S₁ : Stacks (repairT + (2 * 11 + 12)) (prime + K) := { S with R := descriptorBankGenerated S.R cfg }
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := repairDescriptorBank_exec p₀ X hG₀ hK₀ active s body' L v S
    hfit hwidth hinput hscratch
  have hd : RepairSetupData p₀ X rb hG₀ hK₀ active s wb wm wp wk R B
      (repairCanonicalHeaders p₀ X rb R B) (embStk descriptorCore S₁).R :=
    data.generated p₀ X rb hG₀ hK₀ active s L hdesc
  have hs₁ : S₁.R (descriptorCore repairHost.src) = l.flatten := by
    change descriptorBankGenerated S.R cfg (descriptorCore repairHost.src) = l.flatten
    rw [repairDescriptorBank_core_keep p₀ X hG₀ hK₀ active s L S.R repairHost.src (fun d => ?_)]
    · exact hsrc
    · rw [repairDescriptorSource_eq]
      exact (repairSetup_source_src _).symm
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := exactSelectiveEmbedded_exec ρ n m X rb scale active s body
    descriptorCore descriptorCore_injective id body' hbody hQ hA hscale hn hR hB hrb hs v₁ S₁ hd
    (repairDescriptorBank_targets p₀ X hG₀ hK₀ active s L S.R hempty) hL
    (repairDescriptorBank_blank p₀ X hG₀ hK₀ active s L S.R hblank) l hl hlen hs₁
  obtain ⟨v₃, hu₃, he₃⟩ := repairDescriptorClean_exec p₀ X hG₀ hK₀ active s body' L v₂ S
    (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten hdesc
  refine ⟨v₃, m₁ + (m₂ + descriptorEraseCost cfg), hu₃.trans (hu₂.trans hu₁), ?_,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  have hc₁ : (m₁ : ℝ) ≤ descriptorBatchCost cfg := by exact_mod_cast hm₁
  push_cast
  linarith

end
end IntegerMultBounds.MathlibTM2.Routing
