module

public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveConfiguration
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveDescriptor
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveEmbedded
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Lift complete generated-configuration exact repair into any larger bank,
with identical step count and complete nonstream restoration. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable section

variable {T Q K : ℕ} {P P' U : Type}
variable (ρ n m X rb scale : ℕ) (active : Fin n → Bool)
  (s : Fin n → SlotSource (routingParameters ρ n m (Nat.clog 2 scale)) X)

local notation "p₀" => routingParameters ρ n m (Nat.clog 2 scale)
local notation "hG₀" => And.left (routingParameters_guards ρ n m (Nat.clog 2 scale))
local notation "hK₀" => And.left (And.right (routingParameters_guards ρ n m (Nat.clog 2 scale)))

theorem exactSelectiveConfigurationEmbedded_exec (body : P → Pr P repairT Q (prime + K) U)
    (descriptorBody : P → Pr P repairDescriptorT Q (prime + K) U)
    (hdescriptor : ∀ f, descriptorBody f = embProg (descriptorCore (J := 11)) id (body f))
    (configurationBody : P → Pr P repairConfigurationT Q (prime + K) U)
    (hconfiguration : ∀ f, configurationBody f = embProg (fieldCore (N := repairDescriptorT)) id (descriptorBody f))
    (e : Fin repairConfigurationT → Fin T) (he : Function.Injective e) (ι : P → P')
    (body' : P' → Pr P' T Q (prime + K) U)
    (hbody : ∀ f, body' (ι f) = embProg e ι (configurationBody f))
    (Lr Lm : ℕ) (hr : rb < 2 ^ Lr) (hm : (p₀).wy < 2 ^ Lm)
    (L : Fin 11 → ℕ)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (data : RepairPendingConfigurationData p₀ X rb wb wm wp wk R B
      (repairCanonicalHeaders p₀ X rb R B) (embStk (descriptorCore (J := 11)) (embStk (fieldCore (N := repairDescriptorT)) (embStk e S))).R)
    (hempty : ∀ key, (embStk e S).R ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) (repairSetupTarget key))) = [])
    (hL : ∀ j, (embStk e S).L ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) j)) = []) (hblank : ∀ j, RepairBlank j → (embStk e S).R ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) j)) = [])
    (hfit : ∀ j, repairDescriptorWidth p₀ X (repairDescriptorKey j) < 2 ^ L j)
    (hwidth : ∀ j, (embStk e S).R ((fieldCore (N := repairDescriptorT)) ((descriptorBankReg (N := repairT) (J := 11)) j .width)) = binSyms (L j) (repairDescriptorWidth p₀ X (repairDescriptorKey j)))
    (hinput : ∀ j, (embStk e S).R ((fieldCore (N := repairDescriptorT)) ((descriptorBankSelectors (N := repairT) (J := 11)) j)) = descriptorSelectorFrames (L j)
      (repairDescriptorIndices p₀ X hG₀ hK₀ active s (repairDescriptorKey j)).reverse)
    (hscratch : ∀ i : Fin (2 * 11 + 12), 2 * 11 ≤ i.val → (embStk e S).R ((fieldCore (N := repairDescriptorT)) ((descriptorAux (N := repairT) (J := 11)) i)) = [])
    (hdesc : ∀ d, (embStk e S).R ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) (repairDescriptorSource d))) = [])
    (hrowWidth : (embStk e S).R (fieldAux 0) = binSyms Lr rb)
    (hmaskWidth : (embStk e S).R (fieldAux 1) = binSyms Lm (p₀).wy)
    (hwidthScratch : ∀ i : Fin 6, 2 ≤ i.val → (embStk e S).R (fieldAux i) = [])
    (hrow : (embStk e S).R ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) (repairSetupSource (.inr .row)))) = [])
    (hmask : (embStk e S).R ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) (repairSetupSource (.inr .keyMask)))) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (hsrc : (embStk e S).R ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) repairHost.src)) = l.flatten) :
    let W : Stacks repairConfigurationT (prime + K) := { embStk e S with R := repairConfigurationWidthBank rb (p₀).wy (embStk e S).R }
    let C := embStk (fieldCore (N := repairDescriptorT)) W
    let cfg := repairDescriptorJobs p₀ X hG₀ hK₀ active s L
    let D : Stacks repairDescriptorT (prime + K) := { C with R := descriptorBankGenerated C.R cfg }
    let jobs := repairJobs p₀ X rb wb wm wp wk R B
    let installed := metadataInstalled (embStk (descriptorCore (J := 11)) D).R jobs
    ∃ (v' : HS T Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ ((Lr * (4 * rb + 11) + 8 * rb + 12) + (Lm * (4 * (p₀).wy + 11) + 2 * (p₀).wy + 6) + 1 : ℕ) +
        descriptorBatchCost cfg + metadataInstallCost (embStk (descriptorCore (J := 11)) D).R jobs +
        repairDensityCoreCost p₀ X rb R B scale { embStk (descriptorCore (J := 11)) D with R := installed } +
        metadataCleanCost installed repairTargets + descriptorEraseCost cfg + (2 * rb + 2 * (p₀).wy + 5 : ℕ) ∧
      Exec body' (embProg e ι (.seq (binaryFieldBatch (repairConfigurationWidthJobs Lr Lm rb (p₀).wy))
        (.seq (embProg (fieldCore (N := repairDescriptorT)) id (.seq (descriptorBatch cfg)
          (.seq (embProg (descriptorCore (J := 11)) id (repairProgram hQ hA)) (metadataClean (cfg.map DescriptorJob.dst)))))
          (metadataClean [(fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) (repairSetupSource (.inr .row))), (fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) (repairSetupSource (.inr .keyMask)))]))))
        (mk v S) steps (mk v' { S with R := Function.update S.R (e ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) repairHost.src))) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  obtain ⟨v₁, steps, hu₁, hm₁, hex⟩ := exactSelectiveConfiguration_exec ρ n m X rb scale active s
    body descriptorBody hdescriptor configurationBody hconfiguration Lr Lm hr hm L hQ hA hscale hn
    hR hB hrb hs (embDn e v) (embStk e S) data hempty hL hblank hfit hwidth hinput hscratch hdesc
    hrowWidth hmaskWidth hwidthScratch hrow hmask l hl hlen hsrc
  obtain ⟨v₂, hu₂, he₂⟩ := exec_emb_stream e he ι configurationBody body' hbody _ v S v₁ steps
    ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) repairHost.src))
    (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten hex
  exact ⟨v₂, steps, hu₂.trans hu₁, hm₁, he₂⟩

end
end IntegerMultBounds.MathlibTM2.Routing
