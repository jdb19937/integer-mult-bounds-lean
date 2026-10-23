module

public import IntegerMultBounds.MathlibTM2.Routing.ClassifierRepairExec
public import IntegerMultBounds.MathlibTM2.Routing.RepairClassifierInputFrame
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveGeneratedClassifiers
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveConfiguration
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveDescriptor
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

theorem classifierRepairMoved_exec (body : P → Pr P repairT Q (prime + K) U)
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
    (v : HS repairClassifierT Q (prime + K) U) (S : Stacks repairConfigurationT (prime + K))
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
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (_hsrc : S.R ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) repairHost.src)) = l.flatten)
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
    (π : Equiv.Perm (Fin (R * 2 ^ fieldsLen (selectiveLen p₀ X)))) :
    let l₁ := moveRecs π l
    let S₁ : Stacks repairClassifierT (prime + K) := { S' with R := Function.update S'.R (classifierCore (repairConfigurationCore repairHost.src)) l₁.flatten }
    ∃ (v' : HS repairClassifierT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ classifierRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B Lr Lm LK Ln Lo Lt L S₁ ∧
      Exec classifierBody (classifierRepairProgram p₀ X rb hG₀ hK₀ active s Lr Lm L hQ hA)
        (mk v S₁) steps (mk v' { S₁ with R := Function.update S₁.R (classifierCore (repairConfigurationCore repairHost.src)) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l₁).flatten }) := by
  let l₁ := moveRecs π l
  let C₁ : Stacks repairConfigurationT (prime + K) := { S with R := Function.update S.R (repairConfigurationCore repairHost.src) l₁.flatten }
  let S₁ : Stacks repairClassifierT (prime + K) := { S' with R := Function.update S'.R (classifierCore (repairConfigurationCore repairHost.src)) l₁.flatten }
  have hkeep (i : Fin repairConfigurationT) (hi : i ≠ repairConfigurationCore repairHost.src) : C₁.R i = S.R i :=
    Function.update_of_ne hi _ _
  have haux (i : Fin 16) : S₁.R (classifierAux i) = S'.R (classifierAux i) :=
    Function.update_of_ne (classifierCore_aux _ i).symm _ _
  have hdata : RepairPendingMaskData p₀ X rb wb wm wp wk R B (repairCanonicalHeaders p₀ X rb R B)
      (fun i => C₁.R (repairConfigurationCore i)) := by
    apply data.congr p₀ X rb
    intro key
    exact hkeep _ (repairConfigurationSource_src key)
  apply classifierRepair_exec ρ n m X rb scale active s body descriptorBody hdescriptor body' hbody
    classifierBody hclassifier Lr Lm hr hm L hQ hA hscale hn hR hB hrb hs v C₁ hdata
    (l := l₁) (S' := S₁) (LK := LK) (Ln := Ln) (Lo := Lo) (Lt := Lt)
  · intro key
    change C₁.R (repairConfigurationCore (repairSetupTarget key)) = []
    rw [hkeep _ (repairConfigurationCore_injective.ne (repairSetup_target_src key))]; exact hempty key
  · exact hL
  · intro j hj
    change C₁.R (repairConfigurationCore j) = []
    rw [hkeep _ (repairConfigurationCore_injective.ne (repairBlank_src j hj))]; exact hblank j hj
  · exact hfit
  · intro j; rw [hkeep _ (repairConfigurationDescriptorReg_src j .width)]; exact hwidth j
  · intro j; rw [hkeep _ (repairConfigurationSelectors_src j)]; exact hinput j
  · intro i hi; rw [hkeep _ (repairConfigurationDescriptorAux_src i)]; exact hscratch i hi
  · intro d
    change C₁.R (repairConfigurationCore (repairDescriptorSource d)) = []
    rw [hkeep _ (repairConfigurationCore_injective.ne (by rw [repairDescriptorSource_eq]; exact repairSetup_source_src _))]
    exact hdesc d
  · rw [hkeep _ (repairConfigurationAux_src 0)]; exact hrowWidth
  · rw [hkeep _ (repairConfigurationAux_src 1)]; exact hmaskWidth
  · intro i hi; rw [hkeep _ (repairConfigurationAux_src i)]; exact hwidthScratch i hi
  · change C₁.R (repairConfigurationCore (repairSetupSource (.inr .row))) = []
    rw [hkeep _ (repairConfigurationSource_src (.inr .row))]; exact hrow
  · change C₁.R (repairConfigurationCore (repairSetupSource (.inr .keyMask))) = []
    rw [hkeep _ (repairConfigurationSource_src (.inr .keyMask))]; exact hmask
  · exact length_moveRecs _ _
  · intro r hr; exact hlen r (mem_moveRecs _ hl hr)
  · simp [C₁, repairConfigurationCore]
  · dsimp only [S₁, C₁]
    rw [embStk_update_stream classifierCore classifierCore_injective, hproject]
  · exact hsegment
  · exact hcountFit
  · exact hoffsetFit
  · exact htopFit
  · rw [haux]; exact hsegmentInput
  · rw [haux]; exact hrunInput
  · rw [haux]; exact hcountInput
  · rw [haux]; exact hoffsetInput
  · rw [haux]; exact hphaseOffsetInput
  · rw [haux]; exact htopInput
  · intro i hi hne hi'; rw [haux]; exact hclassifierScratch i hi hne hi'
  · change Function.update S'.R (classifierCore (repairConfigurationCore repairHost.src)) l₁.flatten (classifierCore repairClassifierTemporary) = []
    rw [Function.update_of_ne (classifierCore_injective.ne repairClassifierTemporary_src)]
    exact htemporary
  · change Function.update S'.R (classifierCore (repairConfigurationCore repairHost.src)) l₁.flatten (classifierCore repairClassifierPhase) = []
    rw [Function.update_of_ne (classifierCore_injective.ne repairClassifierPhase_src)]
    exact hphase

end
end IntegerMultBounds.MathlibTM2.Routing
