module

public import IntegerMultBounds.MathlibTM2.Routing.HeaderRepairMoved
public import IntegerMultBounds.MathlibTM2.Routing.PlacementAround
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveGeneratedClassifiers
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveConfiguration
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveDescriptor
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveEmbedded
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Actual forward placement, header-generating exact repair and inverse
placement in any larger bank, with all costs and nonstream restoration. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable section

variable {t₀ T Q K : ℕ} {P P' U : Type}
variable (ρ n m X rb scale : ℕ) (active : Fin n → Bool)
  (s : Fin n → SlotSource (routingParameters ρ n m (Nat.clog 2 scale)) X)

local notation "p₀" => routingParameters ρ n m (Nat.clog 2 scale)
local notation "hG₀" => And.left (routingParameters_guards ρ n m (Nat.clog 2 scale))
local notation "hK₀" => And.left (And.right (routingParameters_guards ρ n m (Nat.clog 2 scale)))

theorem placedHeaderRepair_exec (body : P → Pr P repairT Q (prime + K) U)
    (descriptorBody : P → Pr P repairDescriptorT Q (prime + K) U)
    (hdescriptor : ∀ f, descriptorBody f = embProg (descriptorCore (J := 11)) id (body f))
    (body' : P → Pr P repairConfigurationT Q (prime + K) U)
    (hbody : ∀ f, body' f = embProg (fieldCore (N := repairDescriptorT)) id (descriptorBody f))
    (classifierBody : P → Pr P repairClassifierT Q (prime + K) U)
    (hclassifier : ∀ f, classifierBody f = embProg classifierCore id (body' f))
    (Lr Lm : ℕ) (hr : rb < 2 ^ Lr) (hm : (p₀).wy < 2 ^ Lm)
    (L : Fin 11 → ℕ)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS T Q (prime + K) U) (S : Stacks repairConfigurationT (prime + K))
    (data : RepairPendingHeaderData p₀ X rb wb wm wp wk R B
      (embStk (descriptorCore (J := 11)) (embStk (fieldCore (N := repairDescriptorT)) S)).R)
    (hempty : ∀ key, S.R ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) (repairSetupTarget key))) = [])
    (hL : ∀ j, S.L ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) j)) = []) (hblank : ∀ j, RepairBlank j → S.R ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) j)) = [])
    (hfit : ∀ j, repairDescriptorWidth p₀ X (repairDescriptorKey j) < 2 ^ L j)
    (hwidth : ∀ j, S.R ((fieldCore (N := repairDescriptorT)) ((descriptorBankReg (N := repairT) (J := 11)) j .width)) = binSyms (L j) (repairDescriptorWidth p₀ X (repairDescriptorKey j)))
    (hinput : ∀ j, S.R ((fieldCore (N := repairDescriptorT)) ((descriptorBankSelectors (N := repairT) (J := 11)) j)) = descriptorSelectorFrames (L j)
      (repairDescriptorIndices p₀ X hG₀ hK₀ active s (repairDescriptorKey j)).reverse)
    (hscratch : ∀ i : Fin (2 * 11 + 12), 2 * 11 ≤ i.val → S.R ((fieldCore (N := repairDescriptorT)) ((descriptorAux (N := repairT) (J := 11)) i)) = [])
    (hdesc : ∀ d, S.R ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) (repairDescriptorSource d))) = [])
    (hrowWidth : S.R (fieldAux 0) = binSyms Lr rb)
    (hmaskWidth : S.R (fieldAux 1) = binSyms Lm (p₀).wy)
    (hwidthScratch : ∀ i : Fin 6, 2 ≤ i.val → S.R (fieldAux (N := repairDescriptorT) i) = [])
    (hrow : S.R ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) (repairSetupSource (.inr .row)))) = [])
    (hmask : S.R ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) (repairSetupSource (.inr .keyMask)))) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (hsrc : S.R ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) repairHost.src)) = l.flatten)
    (S' : Stacks repairClassifierT (prime + K)) (hproject : embStk classifierCore S' = S)
    (LK Ln Lo Lt : ℕ) (hsegment : (p₀).K < 2 ^ LK) (hcountFit : n < 2 ^ Ln)
    (hoffsetFit : ρ + 1 < 2 ^ Lo) (htopFit : m < 2 ^ Lt)
    (hsegmentInput : S'.R (classifierAux 0) = binSyms LK (p₀).K)
    (hrunInput : S'.R (classifierAux 1) = binSyms LK (p₀).G)
    (hcountInput : S'.R (classifierAux 10) = binSyms Ln n)
    (hoffsetInput : S'.R (classifierAux 13) = binSyms Lo (ρ + 1))
    (hphaseOffsetInput : S'.R (classifierAux 14) = binSyms Lo ρ)
    (htopInput : S'.R (classifierAux 15) = binSyms Lt m)
    (hclassifierScratch : ∀ i : Fin 16, 2 ≤ i.val → i.val ≠ 10 → i.val < 13 → S'.R (classifierAux i) = [])
    (htemporary : S'.R (classifierCore repairClassifierTemporary) = [])
    (hphase : S'.R (classifierCore repairClassifierPhase) = [])
    (D : Stacks repairHeaderT (prime + K)) (hHeaderProject : embStk sharedHeaderCore D = S')
    (headerBody : P → Pr P repairHeaderT Q (prime + K) U)
    (hHeaderBody : ∀ f, headerBody f = embProg sharedHeaderCore id (classifierBody f))
    (Lrow Lwidth : ℕ) (hRbin : R < 2 ^ Lrow) (hWCbin : (p₀).wc < 2 ^ Lwidth)
    (hrowInput : D.R (sharedHeaderBinary 0) = binSyms Lrow R)
    (hwidthInput : D.R (sharedHeaderBinary 1) = binSyms Lwidth (p₀).wc)
    (hheaders : ∀ c i, D.R (repairSharedHeaderBank c (.exchange (.base (.header i)))) = [])
    (hwork : ∀ r : HeaderWorkRole, (∀ i, r ≠ .binary i) → D.R (sharedHeaderWork r) = [])
    (e : Fin repairHeaderT → Fin T) (he : Function.Injective e) (ι : P → P')
    (outerBody : P' → Pr P' T Q (prime + K) U)
    (houter : ∀ f, outerBody (ι f) = embProg e ι (headerBody f))
    (S'' : Stacks T (prime + K)) (houterProject : embStk e S'' = D)
    (tmp : Fin T) (H : ℕ) (hplacementFit : 9 * H ≤ fieldsLen (selectiveLen p₀ X))
    (w : ℕ) (hw : w ≤ H) (reservoir : Fin 3)
    (calls : Fin 3 → BinaryExchangeCall t₀ T Q (fieldsLen (selectiveLen p₀ X)) R B
      (e (repairHeaderRawCore repairHost.src)) tmp)
    (hspec : ∀ j, (calls j).spec = reservoirExchangeSpecs (fieldsLen (selectiveLen p₀ X)) H hplacementFit w hw reservoir j)
    (hready : ∀ j, (calls j).Ready S'')
    (houterSrc : S''.R (e (repairHeaderRawCore repairHost.src)) = l.flatten) :
    let forward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hplacementFit w hw reservoir R false
    let backward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hplacementFit w hw reservoir R true
    let l₁ := moveRecs forward l
    let C₁ : Stacks repairHeaderT (prime + K) := { D with R := Function.update D.R (repairHeaderRawCore repairHost.src) l₁.flatten }
    ∃ (v' : HS T Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ binaryExchangeChainCost calls S'' (reservoirExchangeOrder false) +
        headerRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B Lr Lm LK Ln Lo Lt Lrow Lwidth L C₁ +
        binaryExchangeChainCost calls S'' (reservoirExchangeOrder true) ∧
      Exec outerBody (.seq (binaryExchangeChain calls (reservoirExchangeOrder false))
        (.seq (embProg e ι (headerRepairProgram p₀ X rb hG₀ hK₀ active s Lr Lm L hQ hA))
          (binaryExchangeChain calls (reservoirExchangeOrder true))))
        (mk v S'') steps (mk v' { S'' with R := Function.update S''.R (e (repairHeaderRawCore repairHost.src)) (moveRecs backward (moveRecs (selectiveIdealPerm hK₀ active s R hs) l₁)).flatten }) := by
  let forward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hplacementFit w hw reservoir R false
  let l₁ := moveRecs forward l
  let S₁ : Stacks T (prime + K) := { S'' with R := Function.update S''.R (e (repairHeaderRawCore repairHost.src)) l₁.flatten }
  let C₁ : Stacks repairHeaderT (prime + K) := { D with R := Function.update D.R (repairHeaderRawCore repairHost.src) l₁.flatten }
  apply placementAround_exec outerBody _ tmp H hplacementFit w hw reservoir calls hspec v S'' hready l hl hlen houterSrc
    (embProg e ι (headerRepairProgram p₀ X rb hG₀ hK₀ active s Lr Lm L hQ hA))
    (selectiveIdealPerm hK₀ active s R hs)
  intro u
  obtain ⟨u₁, k, hu₁, hk, hx⟩ := headerRepairMoved_exec ρ n m X rb scale active s body descriptorBody hdescriptor
    body' hbody classifierBody hclassifier Lr Lm hr hm L hQ hA hscale hn hR hB hrb hs (embDn e u) S
    data hempty hL hblank hfit hwidth hinput hscratch hdesc hrowWidth hmaskWidth hwidthScratch hrow hmask
    l hl hlen hsrc S' hproject LK Ln Lo Lt hsegment hcountFit hoffsetFit htopFit hsegmentInput hrunInput
    hcountInput hoffsetInput hphaseOffsetInput htopInput hclassifierScratch htemporary hphase D hHeaderProject headerBody hHeaderBody Lrow Lwidth hRbin hWCbin
    hrowInput hwidthInput hheaders hwork forward
  have hp : embStk e S₁ = C₁ := by
    dsimp only [S₁, C₁]
    rw [embStk_update_stream e he, houterProject]
  change Exec headerBody _ (mk (embDn e u) C₁) k
    (mk u₁ { C₁ with R := Function.update C₁.R (repairHeaderRawCore repairHost.src) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l₁).flatten }) at hx
  rw [← hp] at hx
  obtain ⟨u₂, hu₂, hx₂⟩ := exec_emb_stream e he ι headerBody outerBody houter _ u S₁ u₁ k
    (repairHeaderRawCore repairHost.src)
    (moveRecs (selectiveIdealPerm hK₀ active s R hs) l₁).flatten hx
  exact ⟨u₂, k, hu₂.trans hu₁, hk, hx₂⟩

end
end IntegerMultBounds.MathlibTM2.Routing
