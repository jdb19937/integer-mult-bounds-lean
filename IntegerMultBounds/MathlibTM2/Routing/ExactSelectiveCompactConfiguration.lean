module

public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactWidthFrame
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveCompact
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

theorem exactSelectiveCompactConfiguration_exec (body : P → Pr P repairT Q (prime + K) U)
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
    (data : RepairPendingConfigurationData p₀ X rb wb wm wp wk R B
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
    (hwidthScratch : ∀ i : Fin 6, 2 ≤ i.val → S.R (fieldAux i) = [])
    (hrow : S.R ((fieldCore (N := repairCompactT)) ((compactDescriptorCore (J := 11)) (repairSetupSource (.inr .row)))) = [])
    (hmask : S.R ((fieldCore (N := repairCompactT)) ((compactDescriptorCore (J := 11)) (repairSetupSource (.inr .keyMask)))) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (hsrc : S.R ((fieldCore (N := repairCompactT)) ((compactDescriptorCore (J := 11)) repairHost.src)) = l.flatten) :
    let W : Stacks repairCompactConfigurationT (prime + K) := { S with R := repairCompactWidthBank rb (p₀).wy S.R }
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
        (mk v S) steps (mk v' { S with R := Function.update S.R ((fieldCore (N := repairCompactT)) ((compactDescriptorCore (J := 11)) repairHost.src)) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  dsimp only
  let W : Stacks repairCompactConfigurationT (prime + K) := { S with R := repairCompactWidthBank rb (p₀).wy S.R }
  let C := embStk (fieldCore (N := repairCompactT)) W
  let cfg := repairCompactJobs p₀ X hG₀ hK₀ active s Lw Lg L
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := repairCompactWidths_exec body' Lr Lm rb (p₀).wy hr hm v S
    hrowWidth hmaskWidth hwidthScratch hrow hmask
  have hd : RepairPendingDescriptorData p₀ X rb wb wm wp wk R B (repairCanonicalHeaders p₀ X rb R B)
      (embStk (compactDescriptorCore (J := 11)) C).R := data.compactWidthBank_data p₀ X rb
  have ht : ∀ key, C.R ((compactDescriptorCore (J := 11)) (repairSetupTarget key)) = [] := by
    intro key
    rw [show C.R ((compactDescriptorCore (J := 11)) (repairSetupTarget key)) = S.R ((fieldCore (N := repairCompactT)) ((compactDescriptorCore (J := 11)) (repairSetupTarget key))) from
      repairCompactWidthBank_targets rb (p₀).wy S.R key]
    exact hempty key
  have hb : ∀ j, RepairBlank j → C.R ((compactDescriptorCore (J := 11)) j) = [] := by
    intro j hj
    rw [show C.R ((compactDescriptorCore (J := 11)) j) = S.R ((fieldCore (N := repairCompactT)) ((compactDescriptorCore (J := 11)) j)) from
      repairCompactWidthBank_blank rb (p₀).wy S.R j hj]
    exact hblank j hj
  have ha := repairCompactWidthBank_aux (A := prime + K) rb (p₀).wy S.R
  have hsrc₁ : C.R ((compactDescriptorCore (J := 11)) repairHost.src) = l.flatten := by
    rw [show C.R ((compactDescriptorCore (J := 11)) repairHost.src) = S.R ((fieldCore (N := repairCompactT)) ((compactDescriptorCore (J := 11)) repairHost.src)) from
      repairCompactWidthBank_core rb (p₀).wy S.R repairHost.src
        (repairSetup_source_src (.inr .row)).symm (repairSetup_source_src (.inr .keyMask)).symm]
    exact hsrc
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := exactSelectiveCompact_exec ρ n m X rb scale active s body
    descriptorBody hdescriptor Lw Lg L hQ hA hscale hn hR hB hrb hs (embDn (fieldCore (N := repairCompactT)) v₁) C hd ht hL hb hwidthFit hW hsize
    (fun j => by
      dsimp only [C, W, embStk, Function.comp_apply]
      rw [ha (.width j)]
      exact hwidth j)
    (fun j => by
      dsimp only [C, W, embStk, Function.comp_apply]
      rw [ha (.sourceWidth j)]
      exact hsourceWidth j)
    (fun j => by
      dsimp only [C, W, embStk, Function.comp_apply]
      rw [ha (.input j)]
      exact hinput j)
    (fun r hi hw hs => by
      dsimp only [C, W, embStk, Function.comp_apply]
      rw [ha r]
      exact hscratch r hi hw hs)
    (fun d => by rw [show C.R ((compactDescriptorCore (J := 11)) (repairDescriptorSource d)) = S.R ((fieldCore (N := repairCompactT)) ((compactDescriptorCore (J := 11)) (repairDescriptorSource d))) from
      repairCompactWidthBank_descriptors rb (p₀).wy S.R d]; exact hdesc d) l hl hlen hsrc₁
  obtain ⟨v₃, hu₃, he₃⟩ := exec_emb_stream (fieldCore (N := repairCompactT)) fieldCore_injective id descriptorBody body' hbody _ v₁ W v₂ m₂
    ((compactDescriptorCore (J := 11)) repairHost.src) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten he₂
  obtain ⟨v₄, hu₄, he₄⟩ := fieldPairClean_exec body' ((compactDescriptorCore (J := 11)) (repairSetupSource (.inr .row)))
    ((compactDescriptorCore (J := 11)) (repairSetupSource (.inr .keyMask))) ((compactDescriptorCore (J := 11)) repairHost.src)
    ((compactDescriptorCore_injective (J := 11)).ne (by simp [repairSetupSource]))
    ((compactDescriptorCore_injective (J := 11)).ne (repairSetup_source_src (.inr .row)))
    ((compactDescriptorCore_injective (J := 11)).ne (repairSetup_source_src (.inr .keyMask))) rb (p₀).wy v₃ S
    (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten hrow hmask
  change v₂.user = v₁.user at hu₂
  have hu : v₄.user = v.user := hu₄.trans (hu₃.trans (hu₂.trans hu₁))
  refine ⟨v₄, m₁ + (m₂ + (2 * rb + 2 * (p₀).wy + 5)), hu, ?_,
    Exec.seq he₁ (Exec.seq he₃ he₄)⟩
  have hc₁ : (m₁ : ℝ) ≤ ((Lr * (4 * rb + 11) + 8 * rb + 12) +
      (Lm * (4 * (p₀).wy + 11) + 2 * (p₀).wy + 6) + 1 : ℕ) := by exact_mod_cast hm₁
  push_cast
  push_cast at hc₁
  linarith

end
end IntegerMultBounds.MathlibTM2.Routing
