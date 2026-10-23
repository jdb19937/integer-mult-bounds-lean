module

public import IntegerMultBounds.MathlibTM2.Routing.ConfigurationRepair
public import IntegerMultBounds.MathlibTM2.Routing.PlacedExactSelective
public import IntegerMultBounds.MathlibTM2.Routing.RepairStreamFrame
public import IntegerMultBounds.MathlibTM2.Routing.BinaryReservoirPlacement

/-! Actual placement, embedded exact R2 update, and inverse placement, with
complete restoration and all three execution costs charged. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable {t₀ T Q K : ℕ} {P P' U : Type}
variable (ρ n m X rb scale : ℕ) (active : Fin n → Bool)
  (s : Fin n → SlotSource (routingParameters ρ n m (Nat.clog 2 scale)) X)

local notation "p₀" => routingParameters ρ n m (Nat.clog 2 scale)
local notation "hG₀" => And.left (routingParameters_guards ρ n m (Nat.clog 2 scale))
local notation "hK₀" => And.left (And.right (routingParameters_guards ρ n m (Nat.clog 2 scale)))

theorem placedExactSelectiveConfiguration_exec (body : P → Pr P repairT Q (prime + K) U)
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
      (repairCanonicalHeaders p₀ X rb R B) (fun i => S.R (e (repairConfigurationCore i))))
    (hempty : ∀ key, S.R (e (repairConfigurationCore (repairSetupTarget key))) = [])
    (hL : ∀ j, S.L (e (repairConfigurationCore j)) = []) (hblank : ∀ j, RepairBlank j → S.R (e (repairConfigurationCore j)) = [])
    (hdescriptorFit : ∀ j, repairDescriptorWidth p₀ X (repairDescriptorKey j) < 2 ^ L j)
    (hwidth : ∀ j, S.R (e (fieldCore (N := repairDescriptorT) (descriptorBankReg (N := repairT) (J := 11) j .width))) = binSyms (L j) (repairDescriptorWidth p₀ X (repairDescriptorKey j)))
    (hinput : ∀ j, S.R (e (fieldCore (N := repairDescriptorT) (descriptorBankSelectors (N := repairT) (J := 11) j))) = descriptorSelectorFrames (L j)
      (repairDescriptorIndices p₀ X hG₀ hK₀ active s (repairDescriptorKey j)).reverse)
    (hscratch : ∀ i : Fin (2 * 11 + 12), 2 * 11 ≤ i.val → S.R (e (fieldCore (N := repairDescriptorT) (descriptorAux (N := repairT) (J := 11) i))) = [])
    (hdesc : ∀ d, S.R (e (repairConfigurationCore (repairDescriptorSource d))) = [])
    (hrowWidth : S.R (e (fieldAux 0)) = binSyms Lr rb)
    (hmaskWidth : S.R (e (fieldAux 1)) = binSyms Lm (p₀).wy)
    (hwidthScratch : ∀ i : Fin 6, 2 ≤ i.val → S.R (e (fieldAux i)) = [])
    (hrow : S.R (e (repairConfigurationCore (repairSetupSource (.inr .row)))) = [])
    (hmask : S.R (e (repairConfigurationCore (repairSetupSource (.inr .keyMask)))) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (hsrc : S.R (e (repairConfigurationCore repairHost.src)) = l.flatten)
    (tmp : Fin T) (H : ℕ) (hfit : 9 * H ≤ fieldsLen (selectiveLen p₀ X))
    (w : ℕ) (hw : w ≤ H) (reservoir : Fin 3)
    (calls : Fin 3 → BinaryExchangeCall t₀ T Q (fieldsLen (selectiveLen p₀ X)) R B (e (repairConfigurationCore repairHost.src)) tmp)
    (hspec : ∀ j, (calls j).spec = reservoirExchangeSpecs (fieldsLen (selectiveLen p₀ X)) H hfit w hw reservoir j)
    (hready : ∀ j, (calls j).Ready S) :
    let forward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hfit w hw reservoir R false
    let backward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hfit w hw reservoir R true
    let l₁ := moveRecs forward l
    let S₁ : Stacks T (prime + K) := { S with R := Function.update S.R (e (repairConfigurationCore repairHost.src)) l₁.flatten }
    ∃ (v' : HS T Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ binaryExchangeChainCost calls S (reservoirExchangeOrder false) +
        configurationRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B Lr Lm L (embStk e S₁) +
        binaryExchangeChainCost calls S (reservoirExchangeOrder true) ∧
      Exec body' (.seq (binaryExchangeChain calls (reservoirExchangeOrder false))
        (.seq (embProg e ι (configurationRepairProgram p₀ X rb hG₀ hK₀ active s Lr Lm L hQ hA)) (binaryExchangeChain calls (reservoirExchangeOrder true))))
        (mk v S) steps (mk v' { S with R := Function.update S.R (e (repairConfigurationCore repairHost.src)) (moveRecs backward (moveRecs (selectiveIdealPerm hK₀ active s R hs) l₁)).flatten }) := by
  let forward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hfit w hw reservoir R false
  let backward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hfit w hw reservoir R true
  let l₁ := moveRecs forward l
  let S₁ : Stacks T (prime + K) := { S with R := Function.update S.R (e (repairConfigurationCore repairHost.src)) l₁.flatten }
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := binaryReservoirPlacement_exec H hfit w hw reservoir false body' calls hspec
    v S hready l hl (fun r hr => (hlen r hr).1) (fun r hr => (hlen r hr).2) hsrc
  have hl₁ : l₁.length = R * 2 ^ fieldsLen (selectiveLen p₀ X) := length_moveRecs _ _
  have hmem₁ : ∀ r ∈ l₁, r ∈ l := fun r hr => mem_moveRecs _ hl hr
  have data₁ : RepairPendingConfigurationData p₀ X rb wb wm wp wk R B
      (repairCanonicalHeaders p₀ X rb R B) (fun i => S₁.R (e (repairConfigurationCore i))) := by
    apply data.congr p₀ X rb
    intro key
    exact Function.update_of_ne (he.ne (repairConfigurationCore_injective.ne (repairSetup_source_src key))) _ _
  have hempty₁ : ∀ key, S₁.R (e (repairConfigurationCore (repairSetupTarget key))) = [] := by
    intro key
    rw [show S₁.R (e (repairConfigurationCore (repairSetupTarget key))) = S.R (e (repairConfigurationCore (repairSetupTarget key))) from
      Function.update_of_ne (he.ne (repairConfigurationCore_injective.ne (repairSetup_target_src key))) _ _]
    exact hempty key
  have hblank₁ : ∀ j, RepairBlank j → S₁.R (e (repairConfigurationCore j)) = [] := by
    intro j hj
    rw [show S₁.R (e (repairConfigurationCore j)) = S.R (e (repairConfigurationCore j)) from Function.update_of_ne (he.ne (repairConfigurationCore_injective.ne (repairBlank_src j hj))) _ _]
    exact hblank j hj
  have hkeep (j : Fin repairConfigurationT) (hj : j ≠ repairConfigurationCore repairHost.src) : S₁.R (e j) = S.R (e j) :=
    Function.update_of_ne (he.ne hj) _ _
  have hkeep' (j : Fin repairConfigurationT) (hj : j ≠ repairConfigurationCore repairHost.src) :
      (embStk e S₁).R j = (embStk e S).R j := hkeep j hj
  have hdsrc (d : RepairDescriptorKey) : repairConfigurationCore (repairDescriptorSource d) ≠
      repairConfigurationCore repairHost.src := by
    rw [repairDescriptorSource_eq]
    exact repairConfigurationSource_src _
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := exactSelectiveConfigurationEmbedded_exec ρ n m X rb scale active s body
    descriptorBody hdescriptor configurationBody hconfiguration e he ι body' hbody Lr Lm hr hm L
    hQ hA hscale hn hR hB hrb hs v₁ S₁ data₁ hempty₁ hL hblank₁ hdescriptorFit
    (fun j => by rw [hkeep' _ (repairConfigurationDescriptorReg_src j .width)]; exact hwidth j)
    (fun j => by rw [hkeep' _ (repairConfigurationSelectors_src j)]; exact hinput j)
    (fun i hi => by rw [hkeep' _ (repairConfigurationDescriptorAux_src i)]; exact hscratch i hi)
    (fun d => by
      change (embStk e S₁).R (repairConfigurationCore (repairDescriptorSource d)) = []
      rw [hkeep' _ (hdsrc d)]; exact hdesc d)
    (by rw [hkeep' _ (repairConfigurationAux_src 0)]; exact hrowWidth)
    (by rw [hkeep' _ (repairConfigurationAux_src 1)]; exact hmaskWidth)
    (fun i hi => by rw [hkeep' _ (repairConfigurationAux_src i)]; exact hwidthScratch i hi)
    (by
      change (embStk e S₁).R (repairConfigurationCore (repairSetupSource (.inr .row))) = []
      rw [hkeep' _ (repairConfigurationSource_src (.inr .row))]; exact hrow)
    (by
      change (embStk e S₁).R (repairConfigurationCore (repairSetupSource (.inr .keyMask))) = []
      rw [hkeep' _ (repairConfigurationSource_src (.inr .keyMask))]; exact hmask)
    l₁ hl₁ (fun r hr => hlen r (hmem₁ r hr)) (by simp [S₁, embStk, Function.comp_apply, repairConfigurationCore])
  let l₂ := moveRecs (selectiveIdealPerm hK₀ active s R hs) l₁
  let S₂ : Stacks T (prime + K) := { S₁ with R := Function.update S₁.R (e (repairConfigurationCore repairHost.src)) l₂.flatten }
  have hl₂ : l₂.length = R * 2 ^ fieldsLen (selectiveLen p₀ X) := length_moveRecs _ _
  have hmem₂ : ∀ r ∈ l₂, r ∈ l := fun r hr => hmem₁ r (mem_moveRecs _ hl₁ hr)
  have hready₂ : ∀ j, (calls j).Ready S₂ := fun j =>
    BinaryExchangeCall.Ready.updateStream (calls j) S₁
      (BinaryExchangeCall.Ready.updateStream (calls j) S (hready j) l₁.flatten) l₂.flatten
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := binaryReservoirPlacement_exec H hfit w hw reservoir true body' calls hspec
    v₂ S₂ hready₂ l₂ hl₂ (fun r hr => (hlen r (hmem₂ r hr)).1)
    (fun r hr => (hlen r (hmem₂ r hr)).2) (by simp [S₂])
  have hcost : binaryExchangeChainCost calls S₂ (reservoirExchangeOrder true) =
      binaryExchangeChainCost calls S (reservoirExchangeOrder true) := by
    rw [binaryExchangeChainCost_updateStream calls S₁ l₂.flatten,
      binaryExchangeChainCost_updateStream calls S l₁.flatten]
  rw [hcost] at hm₃
  refine ⟨v₃, m₁ + (m₂ + m₃), hu₃.trans (hu₂.trans hu₁), ?_, ?_⟩
  · have hp : (m₂ : ℝ) ≤ configurationRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B Lr Lm L (embStk e S₁) := by
      simpa only [configurationRepairPrice, exactRepairPrice, add_assoc] using hm₂
    simp only [Nat.cast_add]
    linarith only [hm₁, hp, hm₃]
  · dsimp only [S₁, repairConfigurationCore] at he₂
    simp only [Function.update_idem] at he₂
    dsimp only [S₂, S₁, repairConfigurationCore] at he₃
    simp only [Function.update_idem] at he₃
    exact Exec.seq he₁ (Exec.seq he₂ he₃)

end IntegerMultBounds.MathlibTM2.Routing
