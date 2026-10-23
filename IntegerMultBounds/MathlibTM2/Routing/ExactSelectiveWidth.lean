module

public import IntegerMultBounds.MathlibTM2.Routing.RepairWidthClean
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveEmbedded
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Generate the row and key mask, execute exact R2, and erase generated raw
configuration. Every tape except the record stream returns to its initial value. -/

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

theorem exactSelectiveWidth_exec (body : P → Pr P repairT Q (prime + K) U)
    (body' : P → Pr P (repairT + 6) Q (prime + K) U)
    (hbody : ∀ f, body' f = embProg fieldCore id (body f))
    (Lr Lm : ℕ) (hr : rb < 2 ^ Lr) (hm : (p₀).wy < 2 ^ Lm)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS (repairT + 6) Q (prime + K) U) (S : Stacks (repairT + 6) (prime + K))
    (data : RepairPendingWidthData p₀ X rb hG₀ hK₀ active s wb wm wp wk R B
      (repairCanonicalHeaders p₀ X rb R B) (embStk fieldCore S).R)
    (hempty : ∀ key, S.R (fieldCore (repairSetupTarget key)) = [])
    (hL : ∀ j, S.L (fieldCore j) = []) (hblank : ∀ j, RepairBlank j → S.R (fieldCore j) = [])
    (hrowWidth : S.R (fieldAux 0) = binSyms Lr rb)
    (hmaskWidth : S.R (fieldAux 1) = binSyms Lm (p₀).wy)
    (hscratch : ∀ i : Fin 6, 2 ≤ i.val → S.R (fieldAux i) = [])
    (hrow : S.R (fieldCore (repairSetupSource (.inr .row))) = [])
    (hmask : S.R (fieldCore (repairSetupSource (.inr .keyMask))) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (hsrc : S.R (fieldCore repairHost.src) = l.flatten) :
    let S₁ : Stacks (repairT + 6) (prime + K) := { S with R := repairWidthGenerated p₀ rb S.R }
    let jobs := repairJobs p₀ X rb wb wm wp wk R B
    let installed := metadataInstalled (embStk fieldCore S₁).R jobs
    ∃ (v' : HS (repairT + 6) Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ ((Lr * (4 * rb + 11) + 8 * rb + 12) +
        (Lm * (4 * (p₀).wy + 11) + 2 * (p₀).wy + 6) + 1 : ℕ) +
        metadataInstallCost (embStk fieldCore S₁).R jobs +
        repairDensityCoreCost p₀ X rb R B scale { embStk fieldCore S₁ with R := installed } +
        metadataCleanCost installed repairTargets + (2 * rb + 2 * (p₀).wy + 5 : ℕ) ∧
      Exec body' (.seq (binaryFieldBatch (repairWidthFields Lr Lm rb (p₀).wy))
        (.seq (embProg fieldCore id (repairProgram hQ hA)) (metadataClean repairWidthTargets)))
        (mk v S) steps
        (mk v' { S with R := Function.update S.R (fieldCore repairHost.src) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  dsimp only
  let S₁ : Stacks (repairT + 6) (prime + K) := { S with R := repairWidthGenerated p₀ rb S.R }
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := repairWidthFields_exec body' Lr Lm rb (p₀).wy hr hm v S
    hrowWidth hmaskWidth hscratch hrow hmask
  have hd : RepairSetupData p₀ X rb hG₀ hK₀ active s wb wm wp wk R B
      (repairCanonicalHeaders p₀ X rb R B) (embStk fieldCore S₁).R :=
    data.generated p₀ X rb hG₀ hK₀ active s
  have hs₁ : S₁.R (fieldCore repairHost.src) = l.flatten := by
    change repairWidthGenerated p₀ rb S.R (fieldCore repairHost.src) = l.flatten
    rw [repairWidthGenerated_core_keep p₀ rb S.R repairHost.src
      (repairSetup_source_src (.inr .row)).symm (repairSetup_source_src (.inr .keyMask)).symm]
    exact hsrc
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := exactSelectiveEmbedded_exec ρ n m X rb scale active s body
    fieldCore fieldCore_injective id body' hbody hQ hA hscale hn hR hB hrb hs v₁ S₁ hd
    (repairWidthGenerated_targets p₀ rb S.R hempty) hL
    (repairWidthGenerated_blank p₀ rb S.R hblank) l hl hlen hs₁
  obtain ⟨v₃, hu₃, he₃⟩ := repairWidthClean_exec body' p₀ rb v₂ S
    (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten hrow hmask
  refine ⟨v₃, m₁ + (m₂ + (2 * rb + 2 * (p₀).wy + 5)), hu₃.trans (hu₂.trans hu₁), ?_,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  have hc₁ : (m₁ : ℝ) ≤ ((Lr * (4 * rb + 11) + 8 * rb + 12) +
      (Lm * (4 * (p₀).wy + 11) + 2 * (p₀).wy + 6) + 1 : ℕ) := by exact_mod_cast hm₁
  push_cast
  push_cast at hc₁ hm₂
  linarith

end
end IntegerMultBounds.MathlibTM2.Routing
