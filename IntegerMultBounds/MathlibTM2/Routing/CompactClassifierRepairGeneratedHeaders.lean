module

public import IntegerMultBounds.MathlibTM2.Routing.CompactClassifierRepairExec
public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactHeaderFrame
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveCompactGeneratedClassifiers
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveCompactConfiguration
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveCompact
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveEmbedded
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Execute classifier-generated exact repair from the generated header bank.
Every readiness fact follows from initial data that omits the ten headers.
This theorem starts after header generation and charges repair only. -/

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

theorem compactClassifierRepairGeneratedHeaders_exec (body : P → Pr P repairT Q (prime + K) U)
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
    (v : HS repairCompactClassifierT Q (prime + K) U) (S : Stacks repairCompactConfigurationT (prime + K))
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
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (hsrc : S.R ((fieldCore (N := repairCompactT)) ((compactDescriptorCore (J := 11)) repairHost.src)) = l.flatten)
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
    (H : Stacks repairCompactHeaderT (prime + K)) (hHeaderProject : embStk sharedHeaderCore H = S') :
    let G : Stacks repairCompactHeaderT (prime + K) := { H with R := repairHeaderPairBank p₀ X rb R B repairCompactSharedHeaderBank H.R }
    let C := embStk sharedHeaderCore G
    ∃ (v' : HS repairCompactClassifierT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ compactClassifierRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B Lr Lm LK Ln Lo Lt Lw Lg L C ∧
      Exec classifierBody (compactClassifierRepairProgram p₀ X rb hG₀ hK₀ active s Lr Lm Lw Lg L hQ hA)
        (mk v C) steps (mk v' { C with R := Function.update C.R (classifierCore (repairCompactConfigurationCore repairHost.src)) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  let G : Stacks repairCompactHeaderT (prime + K) := { H with R := repairHeaderPairBank p₀ X rb R B repairCompactSharedHeaderBank H.R }
  let C := embStk sharedHeaderCore G
  let D := embStk classifierCore C
  have hbase (i : Fin repairCompactClassifierT) : H.R (sharedHeaderCore i) = S'.R i := by
    rw [← hHeaderProject]; rfl
  have hinner (i : Fin repairCompactConfigurationT) : H.R (sharedHeaderCore (classifierCore i)) = S.R i := by
    rw [hbase, ← hproject]; rfl
  have dataH : RepairPendingHeaderData p₀ X rb wb wm wp wk R B (fun i => H.R (repairCompactHeaderRawCore i)) := by
    change RepairPendingHeaderData p₀ X rb wb wm wp wk R B (fun i => S.R (repairCompactConfigurationCore i)) at data
    simpa only [repairCompactHeaderRawCore, hinner] using data
  have hLC : C.L = S'.L := by
    change (embStk sharedHeaderCore H).L = S'.L
    exact congrArg Stacks.L hHeaderProject
  have hLD : D.L = S.L := by
    change C.L ∘ classifierCore = S.L
    rw [hLC]
    have hp := congrArg (fun Z : Stacks repairCompactConfigurationT (prime + K) => Z.L) hproject
    dsimp only [embStk] at hp
    exact hp
  apply compactClassifierRepair_exec ρ n m X rb scale active s body descriptorBody hdescriptor body' hbody
    classifierBody hclassifier Lr Lm hr hm Lw Lg L hQ hA hscale hn hR hB hrb hs v D
    (l := l) (S' := C) (LK := LK) (Ln := Ln) (Lo := Lo) (Lt := Lt)
  · exact dataH.compactGenerated p₀ X rb
  · intro key
    exact (repairCompactHeaderPairBank_targets p₀ X rb R B H.R key).trans ((hinner _).trans (hempty key))
  · intro j
    rw [hLD]
    exact hL j
  · intro j hj
    exact (repairCompactHeaderPairBank_blank p₀ X rb R B H.R j hj).trans ((hinner _).trans (hblank j hj))
  · exact hwidthFit
  · exact hW
  · exact hsize
  · intro j
    dsimp only [D, C, G, embStk, Function.comp_apply]
    exact (repairCompactHeaderPairBank_compactDescriptorAux p₀ X rb R B H.R (.width j)).trans
      ((hinner (fieldCore (N := repairCompactT) (compactDescriptorAux (N := repairT) (J := 11) (.width j)))).trans (hwidth j))
  · intro j
    dsimp only [D, C, G, embStk, Function.comp_apply]
    exact (repairCompactHeaderPairBank_compactDescriptorAux p₀ X rb R B H.R (.sourceWidth j)).trans
      ((hinner (fieldCore (N := repairCompactT) (compactDescriptorAux (N := repairT) (J := 11) (.sourceWidth j)))).trans (hsourceWidth j))
  · intro j
    dsimp only [D, C, G, embStk, Function.comp_apply]
    exact (repairCompactHeaderPairBank_compactDescriptorAux p₀ X rb R B H.R (.input j)).trans
      ((hinner (fieldCore (N := repairCompactT) (compactDescriptorAux (N := repairT) (J := 11) (.input j)))).trans (hinput j))
  · intro r hi hw hs
    dsimp only [D, C, G, embStk, Function.comp_apply]
    exact (repairCompactHeaderPairBank_compactDescriptorAux p₀ X rb R B H.R r).trans
      ((hinner (fieldCore (N := repairCompactT) (compactDescriptorAux (N := repairT) (J := 11) r))).trans (hscratch r hi hw hs))
  · intro d
    exact (repairCompactHeaderPairBank_descriptors p₀ X rb R B H.R d).trans ((hinner _).trans (hdesc d))
  · have hh := repairCompactHeaderPairBank_widthAux p₀ X rb R B H.R 0
    have hinnerEq := hinner (fieldAux (N := repairCompactT) 0)
    dsimp only [fieldAux] at hh hinnerEq
    dsimp only [D, C, G, embStk, Function.comp_apply, fieldAux]
    exact hh.trans (hinnerEq.trans hrowWidth)
  · have hh := repairCompactHeaderPairBank_widthAux p₀ X rb R B H.R 1
    have hinnerEq := hinner (fieldAux (N := repairCompactT) 1)
    dsimp only [fieldAux] at hh hinnerEq
    dsimp only [D, C, G, embStk, Function.comp_apply, fieldAux]
    exact hh.trans (hinnerEq.trans hmaskWidth)
  · intro i hi
    have hh := repairCompactHeaderPairBank_widthAux p₀ X rb R B H.R i
    have hinnerEq := hinner (fieldAux (N := repairCompactT) i)
    dsimp only [fieldAux] at hh hinnerEq
    dsimp only [D, C, G, embStk, Function.comp_apply, fieldAux]
    exact hh.trans (hinnerEq.trans (hwidthScratch i hi))
  · exact (repairCompactHeaderPairBank_extra p₀ X rb R B H.R .row).trans ((hinner _).trans hrow)
  · exact (repairCompactHeaderPairBank_extra p₀ X rb R B H.R .keyMask).trans ((hinner _).trans hmask)
  · exact hl
  · exact hlen
  · exact (repairCompactHeaderPairBank_src p₀ X rb R B H.R).trans ((hinner _).trans hsrc)
  · rfl
  · exact hsegment
  · exact hcountFit
  · exact hoffsetFit
  · exact htopFit
  · have hh := repairCompactHeaderPairBank_classifierAux p₀ X rb R B H.R 0
    have hiBase := hbase (classifierAux (N := repairCompactConfigurationT) 0)
    dsimp only [classifierAux] at hh hiBase
    dsimp only [C, G, embStk, Function.comp_apply, classifierAux]
    exact hh.trans (hiBase.trans hsegmentInput)
  · have hh := repairCompactHeaderPairBank_classifierAux p₀ X rb R B H.R 1
    have hiBase := hbase (classifierAux (N := repairCompactConfigurationT) 1)
    dsimp only [classifierAux] at hh hiBase
    dsimp only [C, G, embStk, Function.comp_apply, classifierAux]
    exact hh.trans (hiBase.trans hrunInput)
  · have hh := repairCompactHeaderPairBank_classifierAux p₀ X rb R B H.R 10
    have hiBase := hbase (classifierAux (N := repairCompactConfigurationT) 10)
    dsimp only [classifierAux] at hh hiBase
    dsimp only [C, G, embStk, Function.comp_apply, classifierAux]
    exact hh.trans (hiBase.trans hcountInput)
  · have hh := repairCompactHeaderPairBank_classifierAux p₀ X rb R B H.R 13
    have hiBase := hbase (classifierAux (N := repairCompactConfigurationT) 13)
    dsimp only [classifierAux] at hh hiBase
    dsimp only [C, G, embStk, Function.comp_apply, classifierAux]
    exact hh.trans (hiBase.trans hoffsetInput)
  · have hh := repairCompactHeaderPairBank_classifierAux p₀ X rb R B H.R 14
    have hiBase := hbase (classifierAux (N := repairCompactConfigurationT) 14)
    dsimp only [classifierAux] at hh hiBase
    dsimp only [C, G, embStk, Function.comp_apply, classifierAux]
    exact hh.trans (hiBase.trans hphaseOffsetInput)
  · have hh := repairCompactHeaderPairBank_classifierAux p₀ X rb R B H.R 15
    have hiBase := hbase (classifierAux (N := repairCompactConfigurationT) 15)
    dsimp only [classifierAux] at hh hiBase
    dsimp only [C, G, embStk, Function.comp_apply, classifierAux]
    exact hh.trans (hiBase.trans htopInput)
  · intro i hi hne hi'
    have hh := repairCompactHeaderPairBank_classifierAux p₀ X rb R B H.R i
    have hiBase := hbase (classifierAux (N := repairCompactConfigurationT) i)
    dsimp only [classifierAux] at hh hiBase
    dsimp only [C, G, embStk, Function.comp_apply, classifierAux]
    exact hh.trans (hiBase.trans (hclassifierScratch i hi hne hi'))
  · exact (repairCompactHeaderPairBank_extra p₀ X rb R B H.R .badMask).trans ((hbase _).trans htemporary)
  · exact (repairCompactHeaderPairBank_extra p₀ X rb R B H.R .badPhase).trans ((hbase _).trans hphase)

end
end IntegerMultBounds.MathlibTM2.Routing
