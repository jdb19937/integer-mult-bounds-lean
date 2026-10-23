module

public import IntegerMultBounds.MathlibTM2.Routing.PlacedClassifierRepair
public import IntegerMultBounds.MathlibTM2.Routing.ClassifierPlacementLayout
public import IntegerMultBounds.MathlibTM2.Routing.SharedScheduleInput
public import IntegerMultBounds.MathlibTM2.Routing.BinaryScheduleCalls
public import IntegerMultBounds.MathlibTM2.Routing.PlacementAround
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveGeneratedClassifiers
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveConfiguration
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveDescriptor
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveEmbedded
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Concrete shared-bank execution of placement, generated-classifier exact
repair and inverse placement. Initial bank words derive placement readiness. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable section

variable {t₀ Q K : ℕ} {P P' U : Type}
variable (ρ n m X rb scale : ℕ) (active : Fin n → Bool)
  (s : Fin n → SlotSource (routingParameters ρ n m (Nat.clog 2 scale)) X)

local notation "p₀" => routingParameters ρ n m (Nat.clog 2 scale)
local notation "hG₀" => And.left (routingParameters_guards ρ n m (Nat.clog 2 scale))
local notation "hK₀" => And.left (And.right (routingParameters_guards ρ n m (Nat.clog 2 scale)))

local notation "T₀" => classifierPlacementT t₀
local notation "e₀" => classifierPlacementEmbed (t₀ := t₀)
local notation "slot₀" => classifierPlacementSlot (t₀ := t₀)

theorem jointBankClassifierRepair_exec (body : P → Pr P repairT Q (prime + K) U)
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
    (v : HS T₀ Q (prime + K) U) (S : Stacks repairConfigurationT (prime + K))
    (data : RepairPendingMaskData p₀ X rb wb wm wp wk R B
      (repairCanonicalHeaders p₀ X rb R B) (embStk (descriptorCore (J := 11)) (embStk (fieldCore (N := repairDescriptorT)) S)).R)
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
    (ι : P → P')
    (outerBody : P' → Pr P' T₀ Q (prime + K) U)
    (houter : ∀ f, outerBody (ι f) = embProg e₀ ι (classifierBody f))
    (S'' : Stacks T₀ (prime + K)) (houterProject : embStk e₀ S'' = S')
    (H : ℕ) (hplacementFit : 9 * H ≤ fieldsLen (selectiveLen p₀ X))
    (w : ℕ) (hw : w ≤ H) (reservoir : Fin 3)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd) (hpay : ∀ k, hd k ≠ pay)
    (hQplacement : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T₀)
    (rowBits : List Bool) (Lc Lp : ℕ) (hwidthPlacement : fieldsLen (selectiveLen p₀ X) < 2 ^ Lc) (hBin : B < 2 ^ Lp)
    (hrowCanonical : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ []) (hrowValue : Counter.value rowBits = R)
    (bankWords : Fin (swapT t₀) → List (Fin (prime + K + 4)))
    (hpay0 : bankWords (reg pay) = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → bankWords j = [])
    (hhdr0 : ∀ k, bankWords (reg (hd k)) = [])
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) → ∀ x ∈ bankWords (reg i), x ≠ blank ∧ x.val < prime + 4)
    (hleft : ∀ j, S''.L j = [])
    (hbank : S''.R = sharedScheduleInputBank (classifierCore (repairConfigurationCore repairHost.src)) S'.R
      (reservoirExchangeSpecs (fieldsLen (selectiveLen p₀ X)) H hplacementFit w hw reservoir)
      bankWords Lc Lp B rowBits l.flatten) :
    let calls := binaryScheduleCalls slot₀ classifierPlacementSlot_injective hd pay hhd hpay hQplacement hT
      (reservoirExchangeSpecs (fieldsLen (selectiveLen p₀ X)) H hplacementFit w hw reservoir) hR hB rowBits Lc Lp
      hwidthPlacement hBin hrowCanonical hrowNe hrowValue
    let forward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hplacementFit w hw reservoir R false
    let backward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hplacementFit w hw reservoir R true
    let l₁ := moveRecs forward l
    let C₁ : Stacks repairClassifierT (prime + K) := { S' with R := Function.update S'.R (classifierCore (repairConfigurationCore repairHost.src)) l₁.flatten }
    ∃ (v' : HS T₀ Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ binaryExchangeChainCost calls S'' (reservoirExchangeOrder false) +
        classifierRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B Lr Lm LK Ln Lo Lt L C₁ +
        binaryExchangeChainCost calls S'' (reservoirExchangeOrder true) ∧
      Exec outerBody (.seq (binaryExchangeChain calls (reservoirExchangeOrder false))
        (.seq (embProg e₀ ι (classifierRepairProgram p₀ X rb hG₀ hK₀ active s Lr Lm L hQ hA))
          (binaryExchangeChain calls (reservoirExchangeOrder true))))
        (mk v S'') steps (mk v' { S'' with R := Function.update S''.R (e₀ (classifierCore (repairConfigurationCore repairHost.src))) (moveRecs backward (moveRecs (selectiveIdealPerm hK₀ active s R hs) l₁)).flatten }) := by
  let spec := reservoirExchangeSpecs (fieldsLen (selectiveLen p₀ X)) H hplacementFit w hw reservoir
  let calls := binaryScheduleCalls slot₀ classifierPlacementSlot_injective hd pay hhd hpay hQplacement hT
      (reservoirExchangeSpecs (fieldsLen (selectiveLen p₀ X)) H hplacementFit w hw reservoir) hR hB rowBits Lc Lp
      hwidthPlacement hBin hrowCanonical hrowNe hrowValue
  have hstream : S'.R (classifierCore (repairConfigurationCore repairHost.src)) = l.flatten := by
    rw [← hproject] at hsrc
    exact hsrc
  have hplacement (r : BinaryScheduleReg t₀ 3) :
      S''.R (slot₀ r) = binaryScheduleInputWords spec bankWords Lc Lp B rowBits l.flatten r := by
    rw [hbank]
    exact sharedScheduleInputBank_schedule (classifierCore (repairConfigurationCore repairHost.src)) S'.R
      spec bankWords Lc Lp B rowBits l.flatten hstream r
  have hready : ∀ j, (calls j).Ready S'' := binaryScheduleCalls_ready slot₀ classifierPlacementSlot_injective
    hd pay hhd hpay hQplacement hT spec hR hB rowBits Lc Lp hwidthPlacement hBin hrowCanonical hrowNe hrowValue
    bankWords hpay0 hpriv hhdr0 hother S'' hleft l.flatten hplacement
  have houterSrc : S''.R (e₀ (classifierCore (repairConfigurationCore repairHost.src))) = l.flatten := by
    have hc := sharedScheduleInputBank_core (classifierCore (repairConfigurationCore repairHost.src)) S'.R
      spec bankWords Lc Lp B rowBits l.flatten (classifierCore (repairConfigurationCore repairHost.src))
    rw [hbank]
    exact hc.trans hstream
  exact placedClassifierRepair_exec ρ n m X rb scale active s body descriptorBody hdescriptor body' hbody
    classifierBody hclassifier Lr Lm hr hm L hQ hA hscale hn hR hB hrb hs v S data hempty hL hblank hfit
    hwidth hinput hscratch hdesc hrowWidth hmaskWidth hwidthScratch hrow hmask l hl hlen hsrc S' hproject
    LK Ln Lo Lt hsegment hcountFit hoffsetFit htopFit hsegmentInput hrunInput hcountInput hoffsetInput
    hphaseOffsetInput htopInput hclassifierScratch htemporary hphase e₀ classifierPlacementEmbed_injective ι outerBody houter
    S'' houterProject (slot₀ .tmp) H hplacementFit w hw reservoir calls
    (binaryScheduleCalls_spec slot₀ classifierPlacementSlot_injective hd pay hhd hpay hQplacement hT spec hR hB
      rowBits Lc Lp hwidthPlacement hBin hrowCanonical hrowNe hrowValue) hready houterSrc

end
end IntegerMultBounds.MathlibTM2.Routing
