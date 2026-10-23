module

public import IntegerMultBounds.MathlibTM2.Routing.RepairConfigurationFrame
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveDescriptor
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveEmbedded
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Compile eleven descriptors, execute exact R2 and erase the generated
tables. Only the record stream changes; every phase is charged. -/

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

theorem exactSelectiveConfiguration_exec (body : P → Pr P repairT Q (prime + K) U)
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
    (data : RepairPendingConfigurationData p₀ X rb wb wm wp wk R B
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
    (hwidthScratch : ∀ i : Fin 6, 2 ≤ i.val → S.R (fieldAux i) = [])
    (hrow : S.R ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) (repairSetupSource (.inr .row)))) = [])
    (hmask : S.R ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) (repairSetupSource (.inr .keyMask)))) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (hsrc : S.R ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) repairHost.src)) = l.flatten) :
    let W : Stacks repairConfigurationT (prime + K) := { S with R := repairConfigurationWidthBank rb (p₀).wy S.R }
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
        (mk v S) steps (mk v' { S with R := Function.update S.R ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) repairHost.src)) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  dsimp only
  let W : Stacks repairConfigurationT (prime + K) := { S with R := repairConfigurationWidthBank rb (p₀).wy S.R }
  let C := embStk (fieldCore (N := repairDescriptorT)) W
  let cfg := repairDescriptorJobs p₀ X hG₀ hK₀ active s L
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := repairConfigurationWidths_exec body' Lr Lm rb (p₀).wy hr hm v S
    hrowWidth hmaskWidth hwidthScratch hrow hmask
  have hd : RepairPendingDescriptorData p₀ X rb wb wm wp wk R B (repairCanonicalHeaders p₀ X rb R B)
      (embStk (descriptorCore (J := 11)) C).R := data.widthBank_data p₀ X rb
  have ht : ∀ key, C.R ((descriptorCore (J := 11)) (repairSetupTarget key)) = [] := by
    intro key
    rw [show C.R ((descriptorCore (J := 11)) (repairSetupTarget key)) = S.R ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) (repairSetupTarget key))) from
      repairConfigurationWidthBank_targets rb (p₀).wy S.R key]
    exact hempty key
  have hb : ∀ j, RepairBlank j → C.R ((descriptorCore (J := 11)) j) = [] := by
    intro j hj
    rw [show C.R ((descriptorCore (J := 11)) j) = S.R ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) j)) from
      repairConfigurationWidthBank_blank rb (p₀).wy S.R j hj]
    exact hblank j hj
  have ha := repairConfigurationWidthBank_aux (A := prime + K) rb (p₀).wy S.R
  have hsrc₁ : C.R ((descriptorCore (J := 11)) repairHost.src) = l.flatten := by
    rw [show C.R ((descriptorCore (J := 11)) repairHost.src) = S.R ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) repairHost.src)) from
      repairConfigurationWidthBank_core rb (p₀).wy S.R repairHost.src
        (repairSetup_source_src (.inr .row)).symm (repairSetup_source_src (.inr .keyMask)).symm]
    exact hsrc
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := exactSelectiveDescriptor_exec ρ n m X rb scale active s body
    descriptorBody hdescriptor L hQ hA hscale hn hR hB hrb hs (embDn (fieldCore (N := repairDescriptorT)) v₁) C hd ht hL hb hfit
    (fun j => by
      dsimp only [C, W, embStk, Function.comp_apply]
      dsimp only [descriptorBankReg]
      rw [ha ⟨j.val, by omega⟩]
      exact hwidth j)
    (fun j => by
      dsimp only [C, W, embStk, Function.comp_apply]
      dsimp only [descriptorBankSelectors]
      rw [ha ⟨11 + j.val, by omega⟩]
      exact hinput j)
    (fun i hi => by
      dsimp only [C, W, embStk, Function.comp_apply]
      rw [ha i]
      exact hscratch i hi)
    (fun d => by rw [show C.R ((descriptorCore (J := 11)) (repairDescriptorSource d)) = S.R ((fieldCore (N := repairDescriptorT)) ((descriptorCore (J := 11)) (repairDescriptorSource d))) from
      repairConfigurationWidthBank_descriptors rb (p₀).wy S.R d]; exact hdesc d) l hl hlen hsrc₁
  obtain ⟨v₃, hu₃, he₃⟩ := exec_emb_stream (fieldCore (N := repairDescriptorT)) fieldCore_injective id descriptorBody body' hbody _ v₁ W v₂ m₂
    ((descriptorCore (J := 11)) repairHost.src) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten he₂
  obtain ⟨v₄, hu₄, he₄⟩ := fieldPairClean_exec body' ((descriptorCore (J := 11)) (repairSetupSource (.inr .row)))
    ((descriptorCore (J := 11)) (repairSetupSource (.inr .keyMask))) ((descriptorCore (J := 11)) repairHost.src)
    ((descriptorCore_injective (J := 11)).ne (by simp [repairSetupSource]))
    ((descriptorCore_injective (J := 11)).ne (repairSetup_source_src (.inr .row)))
    ((descriptorCore_injective (J := 11)).ne (repairSetup_source_src (.inr .keyMask))) rb (p₀).wy v₃ S
    (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten hrow hmask
  refine ⟨v₄, m₁ + (m₂ + (2 * rb + 2 * (p₀).wy + 5)), hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_,
    Exec.seq he₁ (Exec.seq he₃ he₄)⟩
  have hc₁ : (m₁ : ℝ) ≤ ((Lr * (4 * rb + 11) + 8 * rb + 12) +
      (Lm * (4 * (p₀).wy + 11) + 2 * (p₀).wy + 6) + 1 : ℕ) := by exact_mod_cast hm₁
  push_cast
  push_cast at hc₁
  linarith

end
end IntegerMultBounds.MathlibTM2.Routing
