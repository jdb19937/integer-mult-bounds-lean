module

public import IntegerMultBounds.MathlibTM2.Routing.ClassifierRepairExec
public import IntegerMultBounds.MathlibTM2.Routing.RepairHeaderFrame
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveGeneratedClassifiers
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveConfiguration
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveDescriptor
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

theorem classifierRepairGeneratedHeaders_exec (body : P → Pr P repairT Q (prime + K) U)
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
    (H : Stacks repairHeaderT (prime + K)) (hHeaderProject : embStk sharedHeaderCore H = S') :
    let G : Stacks repairHeaderT (prime + K) := { H with R := repairHeaderPairBank p₀ X rb R B repairSharedHeaderBank H.R }
    let C := embStk sharedHeaderCore G
    ∃ (v' : HS repairClassifierT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ classifierRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B Lr Lm LK Ln Lo Lt L C ∧
      Exec classifierBody (classifierRepairProgram p₀ X rb hG₀ hK₀ active s Lr Lm L hQ hA)
        (mk v C) steps (mk v' { C with R := Function.update C.R (classifierCore (repairConfigurationCore repairHost.src)) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  let G : Stacks repairHeaderT (prime + K) := { H with R := repairHeaderPairBank p₀ X rb R B repairSharedHeaderBank H.R }
  let C := embStk sharedHeaderCore G
  let D := embStk classifierCore C
  have hbase (i : Fin repairClassifierT) : H.R (sharedHeaderCore i) = S'.R i := by
    rw [← hHeaderProject]; rfl
  have hinner (i : Fin repairConfigurationT) : H.R (sharedHeaderCore (classifierCore i)) = S.R i := by
    rw [hbase, ← hproject]; rfl
  have dataH : RepairPendingHeaderData p₀ X rb wb wm wp wk R B (fun i => H.R (repairHeaderRawCore i)) := by
    change RepairPendingHeaderData p₀ X rb wb wm wp wk R B (fun i => S.R (repairConfigurationCore i)) at data
    simpa only [repairHeaderRawCore, hinner] using data
  have hLC : C.L = S'.L := by
    change (embStk sharedHeaderCore H).L = S'.L
    exact congrArg Stacks.L hHeaderProject
  have hLD : D.L = S.L := by
    change C.L ∘ classifierCore = S.L
    rw [hLC]
    exact congrArg Stacks.L hproject
  apply classifierRepair_exec ρ n m X rb scale active s body descriptorBody hdescriptor body' hbody
    classifierBody hclassifier Lr Lm hr hm L hQ hA hscale hn hR hB hrb hs v D
    (l := l) (S' := C) (LK := LK) (Ln := Ln) (Lo := Lo) (Lt := Lt)
  · exact dataH.generated p₀ X rb
  · intro key
    exact (repairHeaderPairBank_targets p₀ X rb R B H.R key).trans ((hinner _).trans (hempty key))
  · intro j
    rw [hLD]
    exact hL j
  · intro j hj
    exact (repairHeaderPairBank_blank p₀ X rb R B H.R j hj).trans ((hinner _).trans (hblank j hj))
  · exact hfit
  · intro j
    dsimp only [D, C, G, embStk, Function.comp_apply]
    exact (repairHeaderPairBank_descriptorReg p₀ X rb R B H.R j .width).trans ((hinner (fieldCore (N := repairDescriptorT) (descriptorBankReg (N := repairT) (J := 11) j .width))).trans (hwidth j))
  · intro j
    dsimp only [D, C, G, embStk, Function.comp_apply]
    exact (repairHeaderPairBank_descriptorAux p₀ X rb R B H.R ⟨11 + j.val, by omega⟩).trans ((hinner (fieldCore (N := repairDescriptorT) (descriptorBankSelectors (N := repairT) (J := 11) j))).trans (hinput j))
  · intro i hi
    dsimp only [D, C, G, embStk, Function.comp_apply]
    exact (repairHeaderPairBank_descriptorAux p₀ X rb R B H.R i).trans ((hinner (fieldCore (N := repairDescriptorT) (descriptorAux (N := repairT) (J := 11) i))).trans (hscratch i hi))
  · intro d
    exact (repairHeaderPairBank_descriptors p₀ X rb R B H.R d).trans ((hinner _).trans (hdesc d))
  · have hh := repairHeaderPairBank_widthAux p₀ X rb R B H.R 0
    have hinnerEq := hinner (fieldAux (N := repairDescriptorT) 0)
    dsimp only [fieldAux] at hh hinnerEq
    dsimp only [D, C, G, embStk, Function.comp_apply, fieldAux]
    exact hh.trans (hinnerEq.trans hrowWidth)
  · have hh := repairHeaderPairBank_widthAux p₀ X rb R B H.R 1
    have hinnerEq := hinner (fieldAux (N := repairDescriptorT) 1)
    dsimp only [fieldAux] at hh hinnerEq
    dsimp only [D, C, G, embStk, Function.comp_apply, fieldAux]
    exact hh.trans (hinnerEq.trans hmaskWidth)
  · intro i hi
    have hh := repairHeaderPairBank_widthAux p₀ X rb R B H.R i
    have hinnerEq := hinner (fieldAux (N := repairDescriptorT) i)
    dsimp only [fieldAux] at hh hinnerEq
    dsimp only [D, C, G, embStk, Function.comp_apply, fieldAux]
    exact hh.trans (hinnerEq.trans (hwidthScratch i hi))
  · exact (repairHeaderPairBank_extra p₀ X rb R B H.R .row).trans ((hinner _).trans hrow)
  · exact (repairHeaderPairBank_extra p₀ X rb R B H.R .keyMask).trans ((hinner _).trans hmask)
  · exact hl
  · exact hlen
  · exact (repairHeaderPairBank_src p₀ X rb R B H.R).trans ((hinner _).trans hsrc)
  · rfl
  · exact hsegment
  · exact hcountFit
  · exact hoffsetFit
  · exact htopFit
  · have hh := repairHeaderPairBank_classifierAux p₀ X rb R B H.R 0
    have hiBase := hbase (classifierAux (N := repairConfigurationT) 0)
    dsimp only [classifierAux] at hh hiBase
    dsimp only [C, G, embStk, Function.comp_apply, classifierAux]
    exact hh.trans (hiBase.trans hsegmentInput)
  · have hh := repairHeaderPairBank_classifierAux p₀ X rb R B H.R 1
    have hiBase := hbase (classifierAux (N := repairConfigurationT) 1)
    dsimp only [classifierAux] at hh hiBase
    dsimp only [C, G, embStk, Function.comp_apply, classifierAux]
    exact hh.trans (hiBase.trans hrunInput)
  · have hh := repairHeaderPairBank_classifierAux p₀ X rb R B H.R 10
    have hiBase := hbase (classifierAux (N := repairConfigurationT) 10)
    dsimp only [classifierAux] at hh hiBase
    dsimp only [C, G, embStk, Function.comp_apply, classifierAux]
    exact hh.trans (hiBase.trans hcountInput)
  · have hh := repairHeaderPairBank_classifierAux p₀ X rb R B H.R 13
    have hiBase := hbase (classifierAux (N := repairConfigurationT) 13)
    dsimp only [classifierAux] at hh hiBase
    dsimp only [C, G, embStk, Function.comp_apply, classifierAux]
    exact hh.trans (hiBase.trans hoffsetInput)
  · have hh := repairHeaderPairBank_classifierAux p₀ X rb R B H.R 14
    have hiBase := hbase (classifierAux (N := repairConfigurationT) 14)
    dsimp only [classifierAux] at hh hiBase
    dsimp only [C, G, embStk, Function.comp_apply, classifierAux]
    exact hh.trans (hiBase.trans hphaseOffsetInput)
  · have hh := repairHeaderPairBank_classifierAux p₀ X rb R B H.R 15
    have hiBase := hbase (classifierAux (N := repairConfigurationT) 15)
    dsimp only [classifierAux] at hh hiBase
    dsimp only [C, G, embStk, Function.comp_apply, classifierAux]
    exact hh.trans (hiBase.trans htopInput)
  · intro i hi hne hi'
    have hh := repairHeaderPairBank_classifierAux p₀ X rb R B H.R i
    have hiBase := hbase (classifierAux (N := repairConfigurationT) i)
    dsimp only [classifierAux] at hh hiBase
    dsimp only [C, G, embStk, Function.comp_apply, classifierAux]
    exact hh.trans (hiBase.trans (hclassifierScratch i hi hne hi'))
  · exact (repairHeaderPairBank_extra p₀ X rb R B H.R .badMask).trans ((hbase _).trans htemporary)
  · exact (repairHeaderPairBank_extra p₀ X rb R B H.R .badPhase).trans ((hbase _).trans hphase)

end
end IntegerMultBounds.MathlibTM2.Routing
