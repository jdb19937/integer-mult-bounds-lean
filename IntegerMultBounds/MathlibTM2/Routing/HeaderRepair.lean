module

public import IntegerMultBounds.MathlibTM2.Routing.ClassifierRepairGeneratedHeaders
public import IntegerMultBounds.MathlibTM2.Routing.RepairHeadersClean
public import IntegerMultBounds.MathlibTM2.Routing.HeaderRepairProgram
public import IntegerMultBounds.MathlibTM2.Routing.RepairHeaderFrame
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveGeneratedClassifiers
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveConfiguration
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveDescriptor
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveEmbedded
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Generate all ten headers, execute classifier-generated exact repair and
erase the headers. Only the record stream changes; every phase is charged. -/

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

theorem headerRepair_exec (body : P → Pr P repairT Q (prime + K) U)
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
    (v : HS repairHeaderT Q (prime + K) U) (S : Stacks repairConfigurationT (prime + K))
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
    (H : Stacks repairHeaderT (prime + K)) (hHeaderProject : embStk sharedHeaderCore H = S')
    (headerBody : P → Pr P repairHeaderT Q (prime + K) U)
    (hHeaderBody : ∀ f, headerBody f = embProg sharedHeaderCore id (classifierBody f))
    (Lrow Lwidth : ℕ) (hRbin : R < 2 ^ Lrow) (hWCbin : (p₀).wc < 2 ^ Lwidth)
    (hrowInput : H.R (sharedHeaderBinary 0) = binSyms Lrow R)
    (hwidthInput : H.R (sharedHeaderBinary 1) = binSyms Lwidth (p₀).wc)
    (hheaders : ∀ c i, H.R (repairSharedHeaderBank c (.exchange (.base (.header i)))) = [])
    (hwork : ∀ r : HeaderWorkRole, (∀ i, r ≠ .binary i) → H.R (sharedHeaderWork r) = []) :
    ∃ (v' : HS repairHeaderT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ headerRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B Lr Lm LK Ln Lo Lt Lrow Lwidth L H ∧
      Exec headerBody (headerRepairProgram p₀ X rb hG₀ hK₀ active s Lr Lm L hQ hA)
        (mk v H) steps (mk v' { H with R := Function.update H.R (repairHeaderRawCore repairHost.src) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  unfold headerRepairPrice headerRepairProgram
  let G : Stacks repairHeaderT (prime + K) := { H with R := repairHeaderPairBank p₀ X rb R B repairSharedHeaderBank H.R }
  let C := embStk sharedHeaderCore G
  have hinner (i : Fin repairConfigurationT) : H.R (sharedHeaderCore (classifierCore i)) = S.R i := by
    rw [← hproject, ← hHeaderProject]; rfl
  have dataH : RepairPendingHeaderData p₀ X rb wb wm wp wk R B (fun i => H.R (repairHeaderRawCore i)) := by
    change RepairPendingHeaderData p₀ X rb wb wm wp wk R B (fun i => S.R (repairConfigurationCore i)) at data
    simpa only [repairHeaderRawCore, hinner] using data
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁, _⟩ := repairHeaderData_exec headerBody p₀ X rb R B wb wm wp wk Lrow Lwidth
    hRbin hR hWCbin (by omega) v H dataH hrowInput hwidthInput hheaders hwork
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := classifierRepairGeneratedHeaders_exec ρ n m X rb scale active s
    body descriptorBody hdescriptor body' hbody classifierBody hclassifier Lr Lm hr hm L hQ hA hscale hn hR hB hrb hs
    (embDn sharedHeaderCore v₁) S data hempty hL hblank hfit hwidth hinput hscratch hdesc hrowWidth hmaskWidth
    hwidthScratch hrow hmask l hl hlen hsrc S' hproject LK Ln Lo Lt hsegment hcountFit hoffsetFit htopFit
    hsegmentInput hrunInput hcountInput hoffsetInput hphaseOffsetInput htopInput hclassifierScratch htemporary hphase H hHeaderProject
  obtain ⟨v₃, hu₃, he₃⟩ := exec_emb_stream sharedHeaderCore sharedHeaderCore_injective id classifierBody headerBody hHeaderBody
    _ v₁ G v₂ m₂ (classifierCore (repairConfigurationCore repairHost.src))
    (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten he₂
  obtain ⟨v₄, hu₄, he₄⟩ := repairHeadersClean_exec headerBody p₀ X rb R B v₃ H
    (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten
    (by intro c k; exact hheaders c k)
  change v₂.user = v₁.user at hu₂
  have hu : v₄.user = v.user := hu₄.trans (hu₃.trans (hu₂.trans hu₁))
  refine ⟨v₄, m₁ + (m₂ + repairHeaderErasePrice p₀ X rb R B), hu, ?_, ?_⟩
  · have hc₁ : (m₁ : ℝ) ≤ (2 * (14 * ((p₀).wc + (p₀).wy + X) + 18 * Lrow + 24 * Lwidth + 52 * wb + 280) : ℕ) := by
      exact_mod_cast hm₁
    push_cast
    push_cast at hc₁
    linarith
  · dsimp only [G, repairHeaderRawCore] at he₃ he₄
    exact Exec.seq he₁ (Exec.seq he₃ he₄)

end
end IntegerMultBounds.MathlibTM2.Routing
