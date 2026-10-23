module

public import IntegerMultBounds.MathlibTM2.Routing.CompactClassifierRepair
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveCompactGeneratedClassifiers
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveCompactConfiguration
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveCompact
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveEmbedded
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! The complete classifier-generated exact execution under its named program
and price, ready for composition with forward and inverse placement. -/

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

theorem compactClassifierRepair_exec (body : P → Pr P repairT Q (prime + K) U)
    (descriptorBody : P → Pr P repairCompactT Q (prime + K) U)
    (hdescriptor : ∀ f, descriptorBody f = embProg (compactDescriptorCore (J := 11)) id (body f))
    (body' : P → Pr P repairCompactConfigurationT Q (prime + K) U)
    (hbody : ∀ f, body' f = embProg (fieldCore (N := repairCompactT)) id (descriptorBody f))
    (classifierBody : P → Pr P repairCompactClassifierT Q (prime + K) U)
    (hclassifier : ∀ f, classifierBody f = embProg classifierCore id (body' f))
    (Lr Lm : ℕ) (hr : rb < 2 ^ Lr) (hm : (p₀).wy < 2 ^ Lm)
    (Lw Lg L : Fin 11 → ℕ)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS repairCompactClassifierT Q (prime + K) U) (S : Stacks repairCompactConfigurationT (prime + K))
    (data : RepairPendingMaskData p₀ X rb wb wm wp wk R B
      (repairCanonicalHeaders p₀ X rb R B) (embStk (compactDescriptorCore (J := 11)) (embStk (fieldCore (N := repairCompactT)) S)).R)
    (hempty : ∀ key, S.R ((fieldCore (N := repairCompactT)) ((compactDescriptorCore (J := 11)) (repairSetupTarget key))) = [])
    (hL : ∀ j, S.L ((fieldCore (N := repairCompactT)) ((compactDescriptorCore (J := 11)) j)) = []) (hblank : ∀ j, RepairBlank j → S.R ((fieldCore (N := repairCompactT)) ((compactDescriptorCore (J := 11)) j)) = [])
    (hwidthFit : ∀ j, L j < 2 ^ Lw j) (hW : ∀ j, repairCompactSourceWidth p₀ X (repairDescriptorKey j) + 1 < 2 ^ L j)
    (hsize : ∀ j, repairCompactRows p₀ (repairDescriptorKey j) < 2 ^ Lg j)
    (hwidth : ∀ j, (embStk (fieldCore (N := repairCompactT)) S).R (compactDescriptorAux (.width j)) = binSyms (Lw j) (L j))
    (hsourceWidth : ∀ j, (embStk (fieldCore (N := repairCompactT)) S).R (compactDescriptorAux (.sourceWidth j)) = binSyms (L j) (repairCompactSourceWidth p₀ X (repairDescriptorKey j) + 1))
    (hinput : ∀ j, (embStk (fieldCore (N := repairCompactT)) S).R (compactDescriptorAux (.input j)) = selectorRunFrames (Lg j) (L j) (SparseSelectorRun.compress (repairCompactIndices p₀ X hG₀ hK₀ active s j).reverse).reverse)
    (hscratch : ∀ r : CompactDescriptorRole 11,
      (∀ k, r ≠ .input k) → (∀ k, r ≠ .width k) → (∀ k, r ≠ .sourceWidth k) → (embStk (fieldCore (N := repairCompactT)) S).R (compactDescriptorAux r) = [])
    (hdesc : ∀ d, S.R ((fieldCore (N := repairCompactT)) ((compactDescriptorCore (J := 11)) (repairDescriptorSource d))) = [])
    (hrowWidth : S.R (fieldAux 0) = binSyms Lr rb)
    (hmaskWidth : S.R (fieldAux 1) = binSyms Lm (p₀).wy)
    (hwidthScratch : ∀ i : Fin 6, 2 ≤ i.val → S.R (fieldAux (N := repairCompactT) i) = [])
    (hrow : S.R ((fieldCore (N := repairCompactT)) ((compactDescriptorCore (J := 11)) (repairSetupSource (.inr .row)))) = [])
    (hmask : S.R ((fieldCore (N := repairCompactT)) ((compactDescriptorCore (J := 11)) (repairSetupSource (.inr .keyMask)))) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (hsrc : S.R ((fieldCore (N := repairCompactT)) ((compactDescriptorCore (J := 11)) repairHost.src)) = l.flatten)
    (S' : Stacks repairCompactClassifierT (prime + K)) (hproject : embStk classifierCore S' = S)
    (LK Ln Lo Lt : ℕ) (hsegment : (p₀).K < 2 ^ LK) (hcountFit : n < 2 ^ Ln)
    (hoffsetFit : ρ + 1 < 2 ^ Lo) (htopFit : m < 2 ^ Lt)
    (hsegmentInput : S'.R (classifierAux 0) = binSyms LK (p₀).K)
    (hrunInput : S'.R (classifierAux 1) = binSyms LK (p₀).G)
    (hcountInput : S'.R (classifierAux 10) = binSyms Ln n)
    (hoffsetInput : S'.R (classifierAux 13) = binSyms Lo (ρ + 1))
    (hphaseOffsetInput : S'.R (classifierAux 14) = binSyms Lo ρ)
    (htopInput : S'.R (classifierAux 15) = binSyms Lt m)
    (hclassifierScratch : ∀ i : Fin 16, 2 ≤ i.val → i.val ≠ 10 → i.val < 13 → S'.R (classifierAux i) = [])
    (htemporary : S'.R (classifierCore repairCompactClassifierTemporary) = [])
    (hphase : S'.R (classifierCore repairCompactClassifierPhase) = []) :
    ∃ (v' : HS repairCompactClassifierT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ compactClassifierRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B Lr Lm LK Ln Lo Lt Lw Lg L S' ∧
      Exec classifierBody (compactClassifierRepairProgram p₀ X rb hG₀ hK₀ active s Lr Lm Lw Lg L hQ hA)
        (mk v S') steps (mk v' { S' with R := Function.update S'.R (classifierCore (repairCompactConfigurationCore repairHost.src)) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  have he := exactSelectiveCompactClassifiers_exec ρ n m X rb scale active s body descriptorBody hdescriptor
    body' hbody classifierBody hclassifier Lr Lm hr hm Lw Lg L hQ hA hscale hn hR hB hrb hs v S
    data hempty hL hblank hwidthFit hW hsize hwidth hsourceWidth hinput hscratch hdesc hrowWidth hmaskWidth hwidthScratch hrow hmask
    l hl hlen hsrc S' hproject LK Ln Lo Lt hsegment hcountFit hoffsetFit htopFit
    hsegmentInput hrunInput hcountInput hoffsetInput hphaseOffsetInput htopInput hclassifierScratch htemporary hphase
  simpa only [compactClassifierRepairPrice, compactClassifierRepairProgram, compactConfigurationRepairPrice, compactConfigurationRepairProgram,
    exactRepairPrice, hproject, repairCompactConfigurationCore, add_assoc] using he

end
end IntegerMultBounds.MathlibTM2.Routing
