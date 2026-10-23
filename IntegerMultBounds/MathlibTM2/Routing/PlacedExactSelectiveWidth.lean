module

public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveWidthEmbedded
public import IntegerMultBounds.MathlibTM2.Routing.PlacedExactSelective
public import IntegerMultBounds.MathlibTM2.Routing.RepairStreamFrame
public import IntegerMultBounds.MathlibTM2.Routing.BinaryReservoirPlacement

/-! Actual placement, embedded exact R2 update, and inverse placement, with
complete restoration and all three execution costs charged. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable def exactWidthRepairPrice {K : ℕ} (p : Par) (X rb scale wb wm wp wk R B Lr Lm : ℕ)
    (S : Stacks (repairT + 6) (prime + K)) : ℝ :=
  ((Lr * (4 * rb + 11) + 8 * rb + 12) + (Lm * (4 * p.wy + 11) + 2 * p.wy + 6) + 1 : ℕ) +
    exactRepairPrice p X rb scale wb wm wp wk R B
      (embStk fieldCore { S with R := repairWidthGenerated p rb S.R }) + (2 * rb + 2 * p.wy + 5 : ℕ)

variable {t₀ T Q K : ℕ} {P P' U : Type}
variable (ρ n m X rb scale : ℕ) (active : Fin n → Bool)
  (s : Fin n → SlotSource (routingParameters ρ n m (Nat.clog 2 scale)) X)

local notation "p₀" => routingParameters ρ n m (Nat.clog 2 scale)
local notation "hG₀" => And.left (routingParameters_guards ρ n m (Nat.clog 2 scale))
local notation "hK₀" => And.left (And.right (routingParameters_guards ρ n m (Nat.clog 2 scale)))

theorem placedExactSelectiveWidth_exec (body : P → Pr P repairT Q (prime + K) U)
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
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (hsrc : S.R (e (fieldCore repairHost.src)) = l.flatten)
    (tmp : Fin T) (H : ℕ) (hfit : 9 * H ≤ fieldsLen (selectiveLen p₀ X))
    (w : ℕ) (hw : w ≤ H) (reservoir : Fin 3)
    (calls : Fin 3 → BinaryExchangeCall t₀ T Q (fieldsLen (selectiveLen p₀ X)) R B (e (fieldCore repairHost.src)) tmp)
    (hspec : ∀ j, (calls j).spec = reservoirExchangeSpecs (fieldsLen (selectiveLen p₀ X)) H hfit w hw reservoir j)
    (hready : ∀ j, (calls j).Ready S) :
    let forward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hfit w hw reservoir R false
    let backward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hfit w hw reservoir R true
    let l₁ := moveRecs forward l
    let S₁ : Stacks T (prime + K) := { S with R := Function.update S.R (e (fieldCore repairHost.src)) l₁.flatten }
    ∃ (v' : HS T Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ binaryExchangeChainCost calls S (reservoirExchangeOrder false) +
        exactWidthRepairPrice p₀ X rb scale wb wm wp wk R B Lr Lm (embStk e S₁) +
        binaryExchangeChainCost calls S (reservoirExchangeOrder true) ∧
      Exec body' (.seq (binaryExchangeChain calls (reservoirExchangeOrder false))
        (.seq (embProg e ι (.seq (binaryFieldBatch (repairWidthFields Lr Lm rb (p₀).wy))
          (.seq (embProg fieldCore id (repairProgram hQ hA)) (metadataClean repairWidthTargets)))) (binaryExchangeChain calls (reservoirExchangeOrder true))))
        (mk v S) steps (mk v' { S with R := Function.update S.R (e (fieldCore repairHost.src)) (moveRecs backward (moveRecs (selectiveIdealPerm hK₀ active s R hs) l₁)).flatten }) := by
  let forward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hfit w hw reservoir R false
  let backward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hfit w hw reservoir R true
  let l₁ := moveRecs forward l
  let S₁ : Stacks T (prime + K) := { S with R := Function.update S.R (e (fieldCore repairHost.src)) l₁.flatten }
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := binaryReservoirPlacement_exec H hfit w hw reservoir false body' calls hspec
    v S hready l hl (fun r hr => (hlen r hr).1) (fun r hr => (hlen r hr).2) hsrc
  have hl₁ : l₁.length = R * 2 ^ fieldsLen (selectiveLen p₀ X) := length_moveRecs _ _
  have hmem₁ : ∀ r ∈ l₁, r ∈ l := fun r hr => mem_moveRecs _ hl hr
  have data₁ : RepairPendingWidthData p₀ X rb hG₀ hK₀ active s wb wm wp wk R B
      (repairCanonicalHeaders p₀ X rb R B) (embStk fieldCore (embStk e S₁)).R := by
    apply data.congr p₀ X rb hG₀ hK₀ active s
    intro key
    exact Function.update_of_ne (he.ne (fieldCore_injective.ne (repairSetup_source_src key))) _ _
  have hempty₁ : ∀ key, S₁.R (e (fieldCore (repairSetupTarget key))) = [] := by
    intro key
    rw [show S₁.R (e (fieldCore (repairSetupTarget key))) = S.R (e (fieldCore (repairSetupTarget key))) from
      Function.update_of_ne (he.ne (fieldCore_injective.ne (repairSetup_target_src key))) _ _]
    exact hempty key
  have hblank₁ : ∀ j, RepairBlank j → S₁.R (e (fieldCore j)) = [] := by
    intro j hj
    rw [show S₁.R (e (fieldCore j)) = S.R (e (fieldCore j)) from Function.update_of_ne (he.ne (fieldCore_injective.ne (repairBlank_src j hj))) _ _]
    exact hblank j hj
  have hkeep (j : Fin (repairT + 6)) (hj : j ≠ fieldCore repairHost.src) : S₁.R (e j) = S.R (e j) :=
    Function.update_of_ne (he.ne hj) _ _
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := exactSelectiveWidthEmbedded_exec ρ n m X rb scale active s body
    widthBody hwidth e he ι body' hbody Lr Lm hr hm hQ hA hscale hn hR hB hrb hs v₁ S₁ data₁ hempty₁ hL hblank₁
    (by rw [hkeep _ (fieldCore_aux repairHost.src 0).symm]; exact hrowWidth)
    (by rw [hkeep _ (fieldCore_aux repairHost.src 1).symm]; exact hmaskWidth)
    (fun i hi => by rw [hkeep _ (fieldCore_aux repairHost.src i).symm]; exact hscratch i hi)
    (by rw [hkeep _ (fieldCore_injective.ne (repairSetup_source_src (.inr .row)))]; exact hrow)
    (by rw [hkeep _ (fieldCore_injective.ne (repairSetup_source_src (.inr .keyMask)))]; exact hmask)
    l₁ hl₁ (fun r hr => hlen r (hmem₁ r hr)) (by simp [S₁])
  let l₂ := moveRecs (selectiveIdealPerm hK₀ active s R hs) l₁
  let S₂ : Stacks T (prime + K) := { S₁ with R := Function.update S₁.R (e (fieldCore repairHost.src)) l₂.flatten }
  have hl₂ : l₂.length = R * 2 ^ fieldsLen (selectiveLen p₀ X) := length_moveRecs _ _
  have hmem₂ : ∀ r ∈ l₂, r ∈ l := fun r hr => hmem₁ r (mem_moveRecs _ hl₁ hr)
  have hready₂ : ∀ j, (calls j).Ready S₂ := fun j =>
    BinaryExchangeCall.Ready.updateStream (calls j) S₁
      (BinaryExchangeCall.Ready.updateStream (calls j) S (hready j) l₁.flatten) l₂.flatten
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := binaryReservoirPlacement_exec H hfit w hw reservoir true body' calls hspec
    v₂ S₂ hready₂ l₂ hl₂ (fun r hr => (hlen r (hmem₂ r hr)).1)
    (fun r hr => (hlen r (hmem₂ r hr)).2) (by simp [S₂])
  have hcost : binaryExchangeChainCost calls S₂ (reservoirExchangeOrder true) =
      binaryExchangeChainCost calls S (reservoirExchangeOrder true) := by
    rw [binaryExchangeChainCost_updateStream calls S₁ l₂.flatten,
      binaryExchangeChainCost_updateStream calls S l₁.flatten]
  rw [hcost] at hm₃
  refine ⟨v₃, m₁ + (m₂ + m₃), hu₃.trans (hu₂.trans hu₁), ?_, ?_⟩
  · have hp : (m₂ : ℝ) ≤ exactWidthRepairPrice p₀ X rb scale wb wm wp wk R B Lr Lm (embStk e S₁) := by
      simpa only [exactWidthRepairPrice, exactRepairPrice, add_assoc] using hm₂
    simp only [Nat.cast_add]
    linarith only [hm₁, hp, hm₃]
  · dsimp only [S₁] at he₂
    simp only [Function.update_idem] at he₂
    dsimp only [S₂, S₁] at he₃
    simp only [Function.update_idem] at he₃
    exact Exec.seq he₁ (Exec.seq he₂ he₃)

end IntegerMultBounds.MathlibTM2.Routing
