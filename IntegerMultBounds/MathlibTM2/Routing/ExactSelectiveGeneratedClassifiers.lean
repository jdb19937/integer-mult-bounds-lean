module

public import IntegerMultBounds.MathlibTM2.Routing.RepairClassifierFrame
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveConfiguration
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveDescriptor
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveEmbedded
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Execute exact repair from the generated classifier bank. All remaining
readiness facts follow from the initial mask-free configuration inputs.
This theorem starts after mask generation; its cost is the repair cost only. -/

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

theorem exactSelectiveGeneratedClassifiers_exec (body : P → Pr P repairT Q (prime + K) U)
    (descriptorBody : P → Pr P repairDescriptorT Q (prime + K) U)
    (hdescriptor : ∀ f, descriptorBody f = embProg (descriptorCore (J := 11)) id (body f))
    (body' : P → Pr P repairConfigurationT Q (prime + K) U)
    (hbody : ∀ f, body' f = embProg (fieldCore (N := repairDescriptorT)) id (descriptorBody f))
    (Lr Lm : ℕ) (hr : rb < 2 ^ Lr) (hm : (p₀).wy < 2 ^ Lm)
    (L : Fin 11 → ℕ)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS repairConfigurationT Q (prime + K) U) (S : Stacks repairConfigurationT (prime + K))
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
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (hsrc : S.R ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) repairHost.src)) = l.flatten) :
    let M : Stacks repairConfigurationT (prime + K) := { S with R := repairConfigurationClassifierBank p₀ S.R }
    let W : Stacks repairConfigurationT (prime + K) := { M with R := repairConfigurationWidthBank rb (p₀).wy M.R }
    let C := embStk (fieldCore (N := repairDescriptorT)) W
    let cfg := repairDescriptorJobs p₀ X hG₀ hK₀ active s L
    let D : Stacks repairDescriptorT (prime + K) := { C with R := descriptorBankGenerated C.R cfg }
    let jobs := repairJobs p₀ X rb wb wm wp wk R B
    let installed := metadataInstalled (embStk (descriptorCore (J := 11)) D).R jobs
    ∃ (v' : HS repairConfigurationT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ ((Lr * (4 * rb + 11) + 8 * rb + 12) + (Lm * (4 * (p₀).wy + 11) + 2 * (p₀).wy + 6) + 1 : ℕ) +
        descriptorBatchCost cfg + metadataInstallCost (embStk (descriptorCore (J := 11)) D).R jobs +
        repairDensityCoreCost p₀ X rb R B scale { embStk (descriptorCore (J := 11)) D with R := installed } +
        metadataCleanCost installed repairTargets + descriptorEraseCost cfg + (2 * rb + 2 * (p₀).wy + 5 : ℕ) ∧
      Exec body' (.seq (binaryFieldBatch (repairConfigurationWidthJobs Lr Lm rb (p₀).wy))
        (.seq (embProg (fieldCore (N := repairDescriptorT)) id (.seq (descriptorBatch cfg)
          (.seq (embProg (descriptorCore (J := 11)) id (repairProgram hQ hA)) (metadataClean (cfg.map DescriptorJob.dst)))))
          (metadataClean [(fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) (repairSetupSource (.inr .row))), (fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) (repairSetupSource (.inr .keyMask)))])))
        (mk v M) steps (mk v' { M with R := Function.update M.R ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) repairHost.src)) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  let M : Stacks repairConfigurationT (prime + K) := { S with R := repairConfigurationClassifierBank p₀ S.R }
  apply exactSelectiveConfiguration_exec ρ n m X rb scale active s body descriptorBody hdescriptor body' hbody
    Lr Lm hr hm L hQ hA hscale hn hR hB hrb hs v M (l := l)
  · exact data.configurationGenerated p₀ X rb
  · intro key
    change repairConfigurationClassifierBank p₀ S.R (repairConfigurationCore (repairSetupTarget key)) = []
    rw [repairConfigurationClassifierBank_targets]
    exact hempty key
  · exact hL
  · intro j hj
    change repairConfigurationClassifierBank p₀ S.R (repairConfigurationCore j) = []
    rw [repairConfigurationClassifierBank_blank _ _ _ hj]
    exact hblank j hj
  · exact hfit
  · intro j
    change repairConfigurationClassifierBank p₀ S.R (fieldCore (N := repairDescriptorT) (descriptorBankReg (N := repairT) (J := 11) j .width)) = _
    rw [repairConfigurationClassifierBank_descriptorReg]
    exact hwidth j
  · intro j
    change repairConfigurationClassifierBank p₀ S.R (fieldCore (N := repairDescriptorT) (descriptorBankSelectors (N := repairT) (J := 11) j)) = _
    rw [repairConfigurationClassifierBank_selectors]
    exact hinput j
  · intro i hi
    change repairConfigurationClassifierBank p₀ S.R (fieldCore (N := repairDescriptorT) (descriptorAux (N := repairT) (J := 11) i)) = []
    rw [repairConfigurationClassifierBank_descriptorAux]
    exact hscratch i hi
  · intro d
    change repairConfigurationClassifierBank p₀ S.R (repairConfigurationCore (repairDescriptorSource d)) = []
    rw [repairConfigurationClassifierBank_descriptors]
    exact hdesc d
  · have ha := repairConfigurationClassifierBank_widthAux p₀ S.R 0
    dsimp only [fieldAux] at ha
    dsimp only [M, fieldAux]
    exact ha.trans hrowWidth
  · have ha := repairConfigurationClassifierBank_widthAux p₀ S.R 1
    dsimp only [fieldAux] at ha
    dsimp only [M, fieldAux]
    exact ha.trans hmaskWidth
  · intro i hi
    have ha := repairConfigurationClassifierBank_widthAux p₀ S.R i
    dsimp only [fieldAux] at ha
    dsimp only [M, fieldAux]
    exact ha.trans (hwidthScratch i hi)
  · change repairConfigurationClassifierBank p₀ S.R (repairConfigurationCore (repairSetupSource (.inr .row))) = []
    rw [repairConfigurationClassifierBank_row]
    exact hrow
  · change repairConfigurationClassifierBank p₀ S.R (repairConfigurationCore (repairSetupSource (.inr .keyMask))) = []
    rw [repairConfigurationClassifierBank_keyMask]
    exact hmask
  · exact hl
  · exact hlen
  · change repairConfigurationClassifierBank p₀ S.R (repairConfigurationCore repairHost.src) = l.flatten
    rw [repairConfigurationClassifierBank_src]
    exact hsrc

end
end IntegerMultBounds.MathlibTM2.Routing
