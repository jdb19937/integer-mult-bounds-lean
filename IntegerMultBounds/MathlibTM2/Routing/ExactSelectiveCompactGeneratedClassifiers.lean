module

public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactClassifierFrame
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveCompactConfiguration
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveCompact
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

theorem exactSelectiveCompactGeneratedClassifiers_exec (body : P → Pr P repairT Q (prime + K) U)
    (descriptorBody : P → Pr P repairCompactT Q (prime + K) U)
    (hdescriptor : ∀ f, descriptorBody f = embProg (compactDescriptorCore (J := 11)) id (body f))
    (body' : P → Pr P repairCompactConfigurationT Q (prime + K) U)
    (hbody : ∀ f, body' f = embProg (fieldCore (N := repairCompactT)) id (descriptorBody f))
    (Lr Lm : ℕ) (hr : rb < 2 ^ Lr) (hm : (p₀).wy < 2 ^ Lm)
    (Lw Lg L : Fin 11 → ℕ)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS repairCompactConfigurationT Q (prime + K) U) (S : Stacks repairCompactConfigurationT (prime + K))
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
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (hsrc : S.R ((fieldCore (N := repairCompactT)) ((compactDescriptorCore (J := 11)) repairHost.src)) = l.flatten) :
    let M : Stacks repairCompactConfigurationT (prime + K) := { S with R := repairCompactConfigurationClassifierBank p₀ S.R }
    let W : Stacks repairCompactConfigurationT (prime + K) := { M with R := repairCompactWidthBank rb (p₀).wy M.R }
    let C := embStk (fieldCore (N := repairCompactT)) W
    let cfg := repairCompactJobs p₀ X hG₀ hK₀ active s Lw Lg L
    let D : Stacks repairCompactT (prime + K) := { C with R := compactDescriptorBankGenerated C.R cfg }
    let jobs := repairJobs p₀ X rb wb wm wp wk R B
    let installed := metadataInstalled (embStk (compactDescriptorCore (J := 11)) D).R jobs
    ∃ (v' : HS repairCompactConfigurationT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ ((Lr * (4 * rb + 11) + 8 * rb + 12) + (Lm * (4 * (p₀).wy + 11) + 2 * (p₀).wy + 6) + 1 : ℕ) +
        compactDescriptorBatchCost cfg + metadataInstallCost (embStk (compactDescriptorCore (J := 11)) D).R jobs +
        repairDensityCoreCost p₀ X rb R B scale { embStk (compactDescriptorCore (J := 11)) D with R := installed } +
        metadataCleanCost installed repairTargets + compactDescriptorEraseCost cfg + (2 * rb + 2 * (p₀).wy + 5 : ℕ) ∧
      Exec body' (.seq (binaryFieldBatch (repairCompactWidthJobs Lr Lm rb (p₀).wy))
        (.seq (embProg (fieldCore (N := repairCompactT)) id (.seq (compactDescriptorBatch cfg)
          (.seq (embProg (compactDescriptorCore (J := 11)) id (repairProgram hQ hA)) (metadataClean (cfg.map CompactDescriptorJob.dst)))))
          (metadataClean [(fieldCore (N := repairCompactT)) ((compactDescriptorCore (J := 11)) (repairSetupSource (.inr .row))), (fieldCore (N := repairCompactT)) ((compactDescriptorCore (J := 11)) (repairSetupSource (.inr .keyMask)))])))
        (mk v M) steps (mk v' { M with R := Function.update M.R ((fieldCore (N := repairCompactT)) ((compactDescriptorCore (J := 11)) repairHost.src)) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  let M : Stacks repairCompactConfigurationT (prime + K) := { S with R := repairCompactConfigurationClassifierBank p₀ S.R }
  apply exactSelectiveCompactConfiguration_exec ρ n m X rb scale active s body descriptorBody hdescriptor body' hbody
    Lr Lm hr hm Lw Lg L hQ hA hscale hn hR hB hrb hs v M (l := l)
  · exact data.compactConfigurationGenerated p₀ X rb
  · intro key
    change repairCompactConfigurationClassifierBank p₀ S.R (repairCompactConfigurationCore (repairSetupTarget key)) = []
    rw [repairCompactConfigurationClassifierBank_targets]
    exact hempty key
  · exact hL
  · intro j hj
    change repairCompactConfigurationClassifierBank p₀ S.R (repairCompactConfigurationCore j) = []
    rw [repairCompactConfigurationClassifierBank_blank _ _ _ hj]
    exact hblank j hj
  · exact hwidthFit
  · exact hW
  · exact hsize
  · intro j
    change repairCompactConfigurationClassifierBank p₀ S.R (fieldCore (compactDescriptorAux (.width j))) = _
    rw [repairCompactConfigurationClassifierBank_compactDescriptorAux]
    exact hwidth j
  · intro j
    change repairCompactConfigurationClassifierBank p₀ S.R (fieldCore (compactDescriptorAux (.sourceWidth j))) = _
    rw [repairCompactConfigurationClassifierBank_compactDescriptorAux]
    exact hsourceWidth j
  · intro j
    change repairCompactConfigurationClassifierBank p₀ S.R (fieldCore (compactDescriptorAux (.input j))) = _
    rw [repairCompactConfigurationClassifierBank_compactDescriptorAux]
    exact hinput j
  · intro r hi hw hs
    change repairCompactConfigurationClassifierBank p₀ S.R (fieldCore (compactDescriptorAux r)) = []
    rw [repairCompactConfigurationClassifierBank_compactDescriptorAux]
    exact hscratch r hi hw hs
  · intro d
    change repairCompactConfigurationClassifierBank p₀ S.R (repairCompactConfigurationCore (repairDescriptorSource d)) = []
    rw [repairCompactConfigurationClassifierBank_descriptors]
    exact hdesc d
  · have ha := repairCompactConfigurationClassifierBank_widthAux p₀ S.R 0
    dsimp only [fieldAux] at ha
    dsimp only [M, fieldAux]
    exact ha.trans hrowWidth
  · have ha := repairCompactConfigurationClassifierBank_widthAux p₀ S.R 1
    dsimp only [fieldAux] at ha
    dsimp only [M, fieldAux]
    exact ha.trans hmaskWidth
  · intro i hi
    have ha := repairCompactConfigurationClassifierBank_widthAux p₀ S.R i
    dsimp only [fieldAux] at ha
    dsimp only [M, fieldAux]
    exact ha.trans (hwidthScratch i hi)
  · change repairCompactConfigurationClassifierBank p₀ S.R (repairCompactConfigurationCore (repairSetupSource (.inr .row))) = []
    rw [repairCompactConfigurationClassifierBank_row]
    exact hrow
  · change repairCompactConfigurationClassifierBank p₀ S.R (repairCompactConfigurationCore (repairSetupSource (.inr .keyMask))) = []
    rw [repairCompactConfigurationClassifierBank_keyMask]
    exact hmask
  · exact hl
  · exact hlen
  · change repairCompactConfigurationClassifierBank p₀ S.R (repairCompactConfigurationCore repairHost.src) = l.flatten
    rw [repairCompactConfigurationClassifierBank_src]
    exact hsrc

end
end IntegerMultBounds.MathlibTM2.Routing
