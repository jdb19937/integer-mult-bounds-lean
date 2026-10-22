module

public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveEmbedded
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

noncomputable def exactRepairPrice {K : ℕ} (p : Par) (X rb scale wb wm wp wk R B : ℕ)
    (S : Stacks repairT (prime + K)) : ℝ :=
  let jobs := repairJobs p X rb wb wm wp wk R B
  let installed := metadataInstalled S.R jobs
  metadataInstallCost S.R jobs + repairDensityCoreCost p X rb R B scale { S with R := installed } +
    metadataCleanCost installed repairTargets

variable {t₀ T Q K : ℕ} {P P' U : Type}
variable (ρ n m X rb scale : ℕ) (active : Fin n → Bool)
  (s : Fin n → SlotSource (routingParameters ρ n m (Nat.clog 2 scale)) X)

local notation "p₀" => routingParameters ρ n m (Nat.clog 2 scale)
local notation "hG₀" => And.left (routingParameters_guards ρ n m (Nat.clog 2 scale))
local notation "hK₀" => And.left (And.right (routingParameters_guards ρ n m (Nat.clog 2 scale)))

theorem placedExactSelective_exec (body : P → Pr P repairT Q (prime + K) U)
    (e : Fin repairT → Fin T) (he : Function.Injective e) (ι : P → P')
    (body' : P' → Pr P' T Q (prime + K) U)
    (hbody : ∀ f, body' (ι f) = embProg e ι (body f))
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (data : RepairSetupData p₀ X rb hG₀ hK₀ active s wb wm wp wk R B
      (repairCanonicalHeaders p₀ X rb R B) (embStk e S).R)
    (hempty : ∀ key, S.R (e (repairSetupTarget key)) = [])
    (hL : ∀ j, S.L (e j) = []) (hblank : ∀ j, RepairBlank j → S.R (e j) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (hsrc : S.R (e repairHost.src) = l.flatten)
    (tmp : Fin T) (H : ℕ) (hfit : 9 * H ≤ fieldsLen (selectiveLen p₀ X))
    (w : ℕ) (hw : w ≤ H) (reservoir : Fin 3)
    (calls : Fin 3 → BinaryExchangeCall t₀ T Q (fieldsLen (selectiveLen p₀ X)) R B (e repairHost.src) tmp)
    (hspec : ∀ j, (calls j).spec = reservoirExchangeSpecs (fieldsLen (selectiveLen p₀ X)) H hfit w hw reservoir j)
    (hready : ∀ j, (calls j).Ready S) :
    let forward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hfit w hw reservoir R false
    let backward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hfit w hw reservoir R true
    let l₁ := moveRecs forward l
    let S₁ : Stacks T (prime + K) := { S with R := Function.update S.R (e repairHost.src) l₁.flatten }
    ∃ (v' : HS T Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ binaryExchangeChainCost calls S (reservoirExchangeOrder false) +
        exactRepairPrice p₀ X rb scale wb wm wp wk R B (embStk e S₁) +
        binaryExchangeChainCost calls S (reservoirExchangeOrder true) ∧
      Exec body' (.seq (binaryExchangeChain calls (reservoirExchangeOrder false))
        (.seq (embProg e ι (repairProgram hQ hA)) (binaryExchangeChain calls (reservoirExchangeOrder true))))
        (mk v S) steps (mk v' { S with R := Function.update S.R (e repairHost.src) (moveRecs backward (moveRecs (selectiveIdealPerm hK₀ active s R hs) l₁)).flatten }) := by
  let forward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hfit w hw reservoir R false
  let backward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hfit w hw reservoir R true
  let l₁ := moveRecs forward l
  let S₁ : Stacks T (prime + K) := { S with R := Function.update S.R (e repairHost.src) l₁.flatten }
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := binaryReservoirPlacement_exec H hfit w hw reservoir false body' calls hspec
    v S hready l hl (fun r hr => (hlen r hr).1) (fun r hr => (hlen r hr).2) hsrc
  have hl₁ : l₁.length = R * 2 ^ fieldsLen (selectiveLen p₀ X) := length_moveRecs _ _
  have hmem₁ : ∀ r ∈ l₁, r ∈ l := fun r hr => mem_moveRecs _ hl hr
  have data₁ : RepairSetupData p₀ X rb hG₀ hK₀ active s wb wm wp wk R B
      (repairCanonicalHeaders p₀ X rb R B) (embStk e S₁).R := by
    simpa only [S₁, embStk_update_stream e he] using
      data.updateStream p₀ X rb hG₀ hK₀ active s l₁.flatten
  have hempty₁ : ∀ key, S₁.R (e (repairSetupTarget key)) = [] := by
    intro key
    rw [show S₁.R (e (repairSetupTarget key)) = S.R (e (repairSetupTarget key)) from
      Function.update_of_ne (he.ne (repairSetup_target_src key)) _ _]
    exact hempty key
  have hblank₁ : ∀ j, RepairBlank j → S₁.R (e j) = [] := by
    intro j hj
    rw [show S₁.R (e j) = S.R (e j) from Function.update_of_ne (he.ne (repairBlank_src j hj)) _ _]
    exact hblank j hj
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := exactSelectiveEmbedded_exec ρ n m X rb scale active s body e he ι body' hbody
    hQ hA hscale hn hR hB hrb hs v₁ S₁ data₁ hempty₁ hL hblank₁ l₁ hl₁
    (fun r hr => hlen r (hmem₁ r hr)) (by simp [S₁])
  let l₂ := moveRecs (selectiveIdealPerm hK₀ active s R hs) l₁
  let S₂ : Stacks T (prime + K) := { S₁ with R := Function.update S₁.R (e repairHost.src) l₂.flatten }
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
  · change (m₂ : ℝ) ≤ exactRepairPrice p₀ X rb scale wb wm wp wk R B (embStk e S₁) at hm₂
    simp only [Nat.cast_add]
    linarith only [hm₁, hm₂, hm₃]
  · dsimp only [S₁] at he₂
    simp only [Function.update_idem] at he₂
    dsimp only [S₂, S₁] at he₃
    simp only [Function.update_idem] at he₃
    exact Exec.seq he₁ (Exec.seq he₂ he₃)

end IntegerMultBounds.MathlibTM2.Routing
