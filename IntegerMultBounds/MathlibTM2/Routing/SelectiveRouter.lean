module

public import IntegerMultBounds.MathlibTM2.Routing.SelectivePlacement
public import IntegerMultBounds.MathlibTM2.Routing.SelectiveDensity

/-!
# Complete selective routing primitive

The concrete host executes installation, all routing passes and cleanup. Its
canonical interchange values and logarithmic guard widths are fixed here. The
same physical good set supplies both the XOR endpoint and the repair density.
Raw configuration generation and exact exceptional repair belong to R3 and R2.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

def routingHeaders (p : Par) (X R B : ℕ) (c : Fin 2) (k : Fin 5) : List Bool :=
  GrowingCounterData.advance (selectiveSwapValues p X R B c k) []

variable {Q K : ℕ} {P U : Type}
variable (ρ n m X scale : ℕ) (active : Fin n → Bool)
  (s : Fin n → SlotSource (routingParameters ρ n m (Nat.clog 2 scale)) X)

local notation "p₀" => routingParameters ρ n m (Nat.clog 2 scale)
local notation "hG₀" => And.left (routingParameters_guards ρ n m (Nat.clog 2 scale))
local notation "hK₀" => And.left (And.right (routingParameters_guards ρ n m (Nat.clog 2 scale)))

open Classical in
theorem selectiveRouting_exec (body : P → Pr P selectiveT Q (prime + K) U)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hscale : 0 < scale) (hn : n ≤ scale)
    (hallowed : ∀ c, (s c).Allowed active)
    {wb wm R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B)
    (v : HS selectiveT Q (prime + K) U) (S : Stacks selectiveT (prime + K))
    (data : SetupData p₀ X hG₀ hK₀ active s placedSelectiveConfig wb wm B
      (R * 2 ^ fieldsLen (selectiveLen p₀ X)) (routingHeaders p₀ X R B) S.R)
    (hempty : ∀ key : SetupKey, S.R (key.target placedSelectiveHost) = [])
    (hL : ∀ j, S.L j = []) (hblank : ∀ k, placedSelectiveHost.Blank k → S.R k = [])
    (l : List (List (Fin (prime + K + 4))))
    (hstream : S.R placedSelectiveHost.src = l.flatten)
    (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlB : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) :
    let jobs := setupJobs placedSelectiveHost placedSelectiveConfig wb wm B (R * 2 ^ fieldsLen (selectiveLen p₀ X))
    let installed := metadataInstalled S.R jobs
    ∃ (v' : HS selectiveT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ metadataInstallCost S.R jobs +
        ((progW.map (fun o => selectiveOpCost p₀ X selectiveT R B
          (fun c => ∑ j, (installed (placedSelectiveHost.swaps c j)).length) o.1)).sum + 1) +
        metadataCleanCost installed (setupTargets placedSelectiveHost) ∧
      Exec body (selectiveProgram placedSelectiveHost placedSelectiveHost_valid hQ placedSelectiveHost_swapT placedSelectiveConfig) (mk v S) steps
        (mk v' { S with R := Function.update S.R placedSelectiveHost.src (moveRecs (listPerm (selectivePerm p₀ X hG₀ hK₀ (by have h := (routingParameters_guards ρ n m (Nat.clog 2 scale)).2.2; omega) active s R) progW) l).flatten }) ∧
      (∀ i : Fin (R * 2 ^ fieldsLen (selectiveLen p₀ X)),
        Good p₀ (selectiveView p₀ X i) →
        (listPerm (selectivePerm p₀ X hG₀ hK₀ (by have h := (routingParameters_guards ρ n m (Nat.clog 2 scale)).2.2; omega) active s R) progW i : ℕ) =
          setDigit (selectiveLen p₀ X) 1
            ((selectiveView p₀ X i).y ^^^ targetWord p₀ active s
              (selectiveView p₀ X i).y (selectiveView p₀ X i).x) i) ∧
      (((Finset.range (R * 2 ^ fieldsLen (selectiveLen p₀ X))).filter
        fun i => ¬ Good p₀ (selectiveView p₀ X i)).card : ℝ) ≤
        5 / (128 * (scale : ℝ) ^ 3) * (R * 2 ^ fieldsLen (selectiveLen p₀ X) : ℕ) := by
  have hg := routingParameters_guards ρ n m (Nat.clog 2 scale)
  have hgk : (p₀).G < (p₀).K := by omega
  obtain ⟨v', steps, hu, hcost, he, hgood⟩ :=
    selectiveProgram_exec p₀ X hg.1 hg.2.1 hgk active s body
      placedSelectiveHost placedSelectiveHost_valid hQ placedSelectiveHost_swapT
      placedSelectiveConfig placedSelectiveHost_setup hallowed hR hB
      (routingHeaders p₀ X R B) (fun c k => GrowingCounterData.empty_value _)
      (fun c k => GrowingCounterData.advance_canonical _ [] (Or.inl rfl))
      v S data hempty hL hblank l hstream hl hlB
  exact ⟨v', steps, hu, hcost, he, hgood,
    routingParameters_clog_density ρ n m X R scale hscale hn⟩

end IntegerMultBounds.MathlibTM2.Routing
