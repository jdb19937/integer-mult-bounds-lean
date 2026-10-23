module

public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveWidth
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveEmbedded
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Exact repair with generated width fields in any larger routing bank.
Embedding preserves the complete stream-only frame and exact step count. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable section

variable {T Q K : ℕ} {P P' U : Type}
variable (ρ n m X rb scale : ℕ) (active : Fin n → Bool)
  (s : Fin n → SlotSource (routingParameters ρ n m (Nat.clog 2 scale)) X)

local notation "p₀" => routingParameters ρ n m (Nat.clog 2 scale)
local notation "hG₀" => And.left (routingParameters_guards ρ n m (Nat.clog 2 scale))
local notation "hK₀" => And.left (And.right (routingParameters_guards ρ n m (Nat.clog 2 scale)))

theorem exactSelectiveWidthEmbedded_exec (body : P → Pr P repairT Q (prime + K) U)
    (widthBody : P → Pr P (repairT + 6) Q (prime + K) U)
    (hwidth : ∀ f, widthBody f = embProg fieldCore id (body f))
    (e : Fin (repairT + 6) → Fin T) (he : Function.Injective e) (ι : P → P')
    (body' : P' → Pr P' T Q (prime + K) U)
    (hbody : ∀ f, body' (ι f) = embProg e ι (widthBody f))
    (Lr Lm : ℕ) (hr : rb < 2 ^ Lr) (hm : (p₀).wy < 2 ^ Lm)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (data : RepairPendingWidthData p₀ X rb hG₀ hK₀ active s wb wm wp wk R B
      (repairCanonicalHeaders p₀ X rb R B) (embStk fieldCore (embStk e S)).R)
    (hempty : ∀ key, S.R (e (fieldCore (repairSetupTarget key))) = [])
    (hL : ∀ j, S.L (e (fieldCore j)) = []) (hblank : ∀ j, RepairBlank j → S.R (e (fieldCore j)) = [])
    (hrowWidth : S.R (e (fieldAux 0)) = binSyms Lr rb)
    (hmaskWidth : S.R (e (fieldAux 1)) = binSyms Lm (p₀).wy)
    (hscratch : ∀ i : Fin 6, 2 ≤ i.val → S.R (e (fieldAux i)) = [])
    (hrow : S.R (e (fieldCore (repairSetupSource (.inr .row)))) = [])
    (hmask : S.R (e (fieldCore (repairSetupSource (.inr .keyMask)))) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (hsrc : S.R (e (fieldCore repairHost.src)) = l.flatten) :
    let S₁ : Stacks (repairT + 6) (prime + K) := { embStk e S with R := repairWidthGenerated p₀ rb (embStk e S).R }
    let jobs := repairJobs p₀ X rb wb wm wp wk R B
    let installed := metadataInstalled (embStk fieldCore S₁).R jobs
    ∃ (v' : HS T Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ ((Lr * (4 * rb + 11) + 8 * rb + 12) +
        (Lm * (4 * (p₀).wy + 11) + 2 * (p₀).wy + 6) + 1 : ℕ) +
        metadataInstallCost (embStk fieldCore S₁).R jobs +
        repairDensityCoreCost p₀ X rb R B scale { embStk fieldCore S₁ with R := installed } +
        metadataCleanCost installed repairTargets + (2 * rb + 2 * (p₀).wy + 5 : ℕ) ∧
      Exec body' (embProg e ι (.seq (binaryFieldBatch (repairWidthFields Lr Lm rb (p₀).wy))
        (.seq (embProg fieldCore id (repairProgram hQ hA)) (metadataClean repairWidthTargets))))
        (mk v S) steps
        (mk v' { S with R := Function.update S.R (e (fieldCore repairHost.src)) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  obtain ⟨v₁, steps, hu₁, hm₁, hex⟩ := exactSelectiveWidth_exec ρ n m X rb scale active s body
    widthBody hwidth Lr Lm hr hm hQ hA hscale hn hR hB hrb hs (embDn e v) (embStk e S)
    data hempty hL hblank hrowWidth hmaskWidth hscratch hrow hmask l hl hlen hsrc
  obtain ⟨v₂, hu₂, he₂⟩ := exec_emb_stream e he ι widthBody body' hbody _ v S v₁ steps
    (fieldCore repairHost.src) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten hex
  exact ⟨v₂, steps, hu₂.trans hu₁, hm₁, he₂⟩

end
end IntegerMultBounds.MathlibTM2.Routing
