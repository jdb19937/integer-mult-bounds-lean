module

public import IntegerMultBounds.MathlibTM2.Routing.CompactHeaderRepair
public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactHeaderInputFrame
public import IntegerMultBounds.MathlibTM2.Routing.RepairHeadersClean
public import IntegerMultBounds.MathlibTM2.Routing.CompactHeaderRepairProgram
public import IntegerMultBounds.MathlibTM2.Routing.RepairHeaderFrame
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveCompactGeneratedClassifiers
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveCompactConfiguration
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveCompact
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveEmbedded
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Header-generating exact repair remains ready after an arbitrary record
permutation. All configuration and workspace readiness follows from the initial
bank; only the stream changes and every phase is charged. -/

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

theorem compactHeaderRepairMoved_exec (body : P → Pr P repairT Q (prime + K) U)
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
    (v : HS repairCompactHeaderT Q (prime + K) U) (S : Stacks repairCompactConfigurationT (prime + K))
    (data : RepairPendingHeaderData p₀ X rb wb wm wp wk R B
      (embStk (compactDescriptorCore (J := 11)) (embStk (fieldCore (N := repairCompactT)) S)).R)
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
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (_hsrc : S.R ((fieldCore (N := repairCompactT)) ((compactDescriptorCore (J := 11)) repairHost.src)) = l.flatten)
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
    (hphase : S'.R (classifierCore repairCompactClassifierPhase) = [])
    (H : Stacks repairCompactHeaderT (prime + K)) (hHeaderProject : embStk sharedHeaderCore H = S')
    (headerBody : P → Pr P repairCompactHeaderT Q (prime + K) U)
    (hHeaderBody : ∀ f, headerBody f = embProg sharedHeaderCore id (classifierBody f))
    (Lrow Lwidth : ℕ) (hRbin : R < 2 ^ Lrow) (hWCbin : (p₀).wc < 2 ^ Lwidth)
    (hrowInput : H.R (sharedHeaderBinary 0) = binSyms Lrow R)
    (hwidthInput : H.R (sharedHeaderBinary 1) = binSyms Lwidth (p₀).wc)
    (hheaders : ∀ c i, H.R (repairCompactSharedHeaderBank c (.exchange (.base (.header i)))) = [])
    (hwork : ∀ r : HeaderWorkRole, (∀ i, r ≠ .binary i) → H.R (sharedHeaderWork r) = [])
    (π : Equiv.Perm (Fin (R * 2 ^ fieldsLen (selectiveLen p₀ X)))) :
    let l₁ := moveRecs π l
    let H₁ : Stacks repairCompactHeaderT (prime + K) := { H with R := Function.update H.R (repairCompactHeaderRawCore repairHost.src) l₁.flatten }
    ∃ (v' : HS repairCompactHeaderT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ compactHeaderRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B Lr Lm LK Ln Lo Lt Lrow Lwidth Lw Lg L H₁ ∧
      Exec headerBody (compactHeaderRepairProgram p₀ X rb hG₀ hK₀ active s Lr Lm Lw Lg L hQ hA)
        (mk v H₁) steps (mk v' { H₁ with R := Function.update H₁.R (repairCompactHeaderRawCore repairHost.src) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l₁).flatten }) := by
  let l₁ := moveRecs π l
  let C₁ : Stacks repairCompactConfigurationT (prime + K) := { S with R := Function.update S.R (repairCompactConfigurationCore repairHost.src) l₁.flatten }
  let S₁ : Stacks repairCompactClassifierT (prime + K) := { S' with R := Function.update S'.R (classifierCore (repairCompactConfigurationCore repairHost.src)) l₁.flatten }
  have hkeep (i : Fin repairCompactConfigurationT) (hi : i ≠ repairCompactConfigurationCore repairHost.src) : C₁.R i = S.R i := by
    dsimp only [C₁]
    exact Function.update_of_ne hi _ _
  have haux (i : Fin 16) : S₁.R (classifierAux i) = S'.R (classifierAux i) := by
    dsimp only [S₁]
    exact Function.update_of_ne (classifierCore_aux _ i).symm _ _
  have hdata : RepairPendingHeaderData p₀ X rb wb wm wp wk R B
      (fun i => C₁.R (repairCompactConfigurationCore i)) := by
    apply data.congr p₀ X rb
    intro key
    exact hkeep _ (repairCompactConfigurationSource_src key)
  let H₁ : Stacks repairCompactHeaderT (prime + K) := { H with R := Function.update H.R (repairCompactHeaderRawCore repairHost.src) l₁.flatten }
  have hworkKeep (r : HeaderWorkRole) : H₁.R (sharedHeaderWork r) = H.R (sharedHeaderWork r) := by
    dsimp only [H₁]
    exact compactHeaderWork_updateStream H.R l₁.flatten r
  apply compactHeaderRepair_exec ρ n m X rb scale active s body descriptorBody hdescriptor body' hbody
    classifierBody hclassifier Lr Lm hr hm Lw Lg L hQ hA hscale hn hR hB hrb hs v C₁ hdata
    (l := l₁) (S' := S₁) (LK := LK) (Ln := Ln) (Lo := Lo) (Lt := Lt)
    (H := H₁) (headerBody := headerBody) (Lrow := Lrow) (Lwidth := Lwidth)
  · intro key
    change C₁.R (repairCompactConfigurationCore (repairSetupTarget key)) = []
    rw [hkeep _ (repairCompactConfigurationCore_injective.ne (repairSetup_target_src key))]; exact hempty key
  · exact hL
  · intro j hj
    change C₁.R (repairCompactConfigurationCore j) = []
    rw [hkeep _ (repairCompactConfigurationCore_injective.ne (repairBlank_src j hj))]; exact hblank j hj
  · exact hwidthFit
  · exact hW
  · exact hsize
  · intro j; dsimp only [embStk, Function.comp_apply]; rw [hkeep _ (repairCompactConfigurationDescriptorAux_src (.width j))]; exact hwidth j
  · intro j; dsimp only [embStk, Function.comp_apply]; rw [hkeep _ (repairCompactConfigurationDescriptorAux_src (.sourceWidth j))]; exact hsourceWidth j
  · intro j; dsimp only [embStk, Function.comp_apply]; rw [hkeep _ (repairCompactConfigurationDescriptorAux_src (.input j))]; exact hinput j
  · intro r hi hw hs; dsimp only [embStk, Function.comp_apply]; rw [hkeep _ (repairCompactConfigurationDescriptorAux_src r)]; exact hscratch r hi hw hs
  · intro d
    change C₁.R (repairCompactConfigurationCore (repairDescriptorSource d)) = []
    rw [hkeep _ (repairCompactConfigurationCore_injective.ne (by rw [repairDescriptorSource_eq]; exact repairSetup_source_src _))]
    exact hdesc d
  · rw [hkeep _ (repairCompactConfigurationAux_src 0)]; exact hrowWidth
  · rw [hkeep _ (repairCompactConfigurationAux_src 1)]; exact hmaskWidth
  · intro i hi; rw [hkeep _ (repairCompactConfigurationAux_src i)]; exact hwidthScratch i hi
  · change C₁.R (repairCompactConfigurationCore (repairSetupSource (.inr .row))) = []
    rw [hkeep _ (repairCompactConfigurationSource_src (.inr .row))]; exact hrow
  · change C₁.R (repairCompactConfigurationCore (repairSetupSource (.inr .keyMask))) = []
    rw [hkeep _ (repairCompactConfigurationSource_src (.inr .keyMask))]; exact hmask
  · exact length_moveRecs _ _
  · intro r hr; exact hlen r (mem_moveRecs _ hl hr)
  · simp [C₁, repairCompactConfigurationCore]
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
  · change Function.update S'.R (classifierCore (repairCompactConfigurationCore repairHost.src)) l₁.flatten (classifierCore repairCompactClassifierTemporary) = []
    rw [Function.update_of_ne (classifierCore_injective.ne repairCompactClassifierTemporary_src)]
    exact htemporary
  · change Function.update S'.R (classifierCore (repairCompactConfigurationCore repairHost.src)) l₁.flatten (classifierCore repairCompactClassifierPhase) = []
    rw [Function.update_of_ne (classifierCore_injective.ne repairCompactClassifierPhase_src)]
    exact hphase

  · dsimp only [H₁, S₁, repairCompactHeaderRawCore]
    rw [embStk_update_stream sharedHeaderCore sharedHeaderCore_injective, hHeaderProject]
  · exact hHeaderBody
  · exact hRbin
  · exact hWCbin
  · change H₁.R (sharedHeaderWork (.binary 0)) = _
    rw [hworkKeep]; exact hrowInput
  · change H₁.R (sharedHeaderWork (.binary 1)) = _
    rw [hworkKeep]; exact hwidthInput
  · intro c i
    change Function.update H.R (repairCompactHeaderRawCore repairHost.src) l₁.flatten (repairCompactSharedHeaderBank c (.exchange (.base (.header i)))) = []
    rw [repairCompactSharedHeaderBank_header]
    change Function.update H.R (repairCompactHeaderRawCore repairHost.src) l₁.flatten (repairCompactHeaderRawCore (repairRoutingConfig (.header c i))) = []
    have hne : repairRoutingConfig (.header c i) ≠ repairHost.src := repairSetup_source_src (.inl (.header c i))
    rw [Function.update_of_ne (repairCompactHeaderRawCore_injective.ne hne)]
    exact hheaders c i
  · intro r hr; rw [hworkKeep]; exact hwork r hr

end
end IntegerMultBounds.MathlibTM2.Routing
