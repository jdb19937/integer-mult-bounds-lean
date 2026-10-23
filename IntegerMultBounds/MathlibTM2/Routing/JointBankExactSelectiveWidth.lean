module

public import IntegerMultBounds.MathlibTM2.Routing.PlacedExactSelectiveWidth
public import IntegerMultBounds.MathlibTM2.Routing.WidthPlacementLayout
public import IntegerMultBounds.MathlibTM2.Routing.SharedScheduleInput
public import IntegerMultBounds.MathlibTM2.Routing.BinaryScheduleCalls

/-! Concrete common-bank entry point for actual placed exact repair. Initial
binary words derive every placement invariant; core words supply raw R2 inputs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable {t₀ Q K : ℕ} {P P' U : Type}
variable (ρ n m X rb scale : ℕ) (active : Fin n → Bool)
  (s : Fin n → SlotSource (routingParameters ρ n m (Nat.clog 2 scale)) X)

local notation "p₀" => routingParameters ρ n m (Nat.clog 2 scale)
local notation "hG₀" => And.left (routingParameters_guards ρ n m (Nat.clog 2 scale))
local notation "hK₀" => And.left (And.right (routingParameters_guards ρ n m (Nat.clog 2 scale)))

local notation "T₀" => widthPlacementT t₀
local notation "e₀" => widthPlacementEmbed (t₀ := t₀)
local notation "slot₀" => widthPlacementSlot (t₀ := t₀)

theorem jointBankExactSelectiveWidth_exec (body : P → Pr P repairT Q (prime + K) U)
    (widthBody : P → Pr P (repairT + 6) Q (prime + K) U)
    (hwidthBody : ∀ f, widthBody f = embProg fieldCore id (body f))
    (ι : P → P')
    (body' : P' → Pr P' T₀ Q (prime + K) U)
    (hbody : ∀ f, body' (ι f) = embProg e₀ ι (widthBody f))
    (Lr Lm : ℕ) (hr : rb < 2 ^ Lr) (hm : (p₀).wy < 2 ^ Lm)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS T₀ Q (prime + K) U) (S : Stacks T₀ (prime + K))
    (coreWords : Fin (repairT + 6) → List (Fin (prime + K + 4)))
    (data : RepairPendingWidthData p₀ X rb hG₀ hK₀ active s wb wm wp wk R B
      (repairCanonicalHeaders p₀ X rb R B) (fun i => coreWords (fieldCore i)))
    (hempty : ∀ key, coreWords (fieldCore (repairSetupTarget key)) = [])
    (hL : ∀ j, S.L j = []) (hblank : ∀ j, RepairBlank j → coreWords (fieldCore j) = [])
    (hrowWidth : coreWords (fieldAux 0) = binSyms Lr rb)
    (hmaskWidth : coreWords (fieldAux 1) = binSyms Lm (p₀).wy)
    (hscratch : ∀ i : Fin 6, 2 ≤ i.val → coreWords (fieldAux i) = [])
    (hrow0 : coreWords (fieldCore (repairSetupSource (.inr .row))) = [])
    (hmask0 : coreWords (fieldCore (repairSetupSource (.inr .keyMask))) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (hsrc : coreWords (fieldCore repairHost.src) = l.flatten)
    (H : ℕ) (hfit : 9 * H ≤ fieldsLen (selectiveLen p₀ X))
    (w : ℕ) (hw : w ≤ H) (reservoir : Fin 3)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd) (hpay : ∀ k, hd k ≠ pay)
    (hQplacement : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T₀)
    (rowBits : List Bool) (Lc L : ℕ) (hwidth : fieldsLen (selectiveLen p₀ X) < 2 ^ Lc) (hBin : B < 2 ^ L)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ []) (hrowValue : Counter.value rowBits = R)
    (bankWords : Fin (swapT t₀) → List (Fin (prime + K + 4)))
    (hpay0 : bankWords (reg pay) = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → bankWords j = [])
    (hhdr0 : ∀ k, bankWords (reg (hd k)) = [])
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) → ∀ x ∈ bankWords (reg i), x ≠ blank ∧ x.val < prime + 4)
    (hinput : S.R = sharedScheduleInputBank (fieldCore repairHost.src) coreWords
      (reservoirExchangeSpecs (fieldsLen (selectiveLen p₀ X)) H hfit w hw reservoir) bankWords Lc L B rowBits l.flatten) :
    let calls := binaryScheduleCalls slot₀ widthPlacementSlot_injective hd pay hhd hpay hQplacement hT
      (reservoirExchangeSpecs (fieldsLen (selectiveLen p₀ X)) H hfit w hw reservoir) hR hB rowBits Lc L hwidth hBin hrow hrowNe hrowValue
    let forward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hfit w hw reservoir R false
    let backward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hfit w hw reservoir R true
    let l₁ := moveRecs forward l
    let S₁ : Stacks T₀ (prime + K) := { S with R := Function.update S.R (e₀ (fieldCore repairHost.src)) l₁.flatten }
    ∃ (v' : HS T₀ Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ binaryExchangeChainCost calls S (reservoirExchangeOrder false) +
        exactWidthRepairPrice p₀ X rb scale wb wm wp wk R B Lr Lm (embStk e₀ S₁) +
        binaryExchangeChainCost calls S (reservoirExchangeOrder true) ∧
      Exec body' (.seq (binaryExchangeChain calls (reservoirExchangeOrder false))
        (.seq (embProg e₀ ι (.seq (binaryFieldBatch (repairWidthFields Lr Lm rb (p₀).wy))
          (.seq (embProg fieldCore id (repairProgram hQ hA)) (metadataClean repairWidthTargets)))) (binaryExchangeChain calls (reservoirExchangeOrder true))))
        (mk v S) steps (mk v' { S with R := Function.update S.R (e₀ (fieldCore repairHost.src)) (moveRecs backward (moveRecs (selectiveIdealPerm hK₀ active s R hs) l₁)).flatten }) := by
  let spec := reservoirExchangeSpecs (fieldsLen (selectiveLen p₀ X)) H hfit w hw reservoir
  let calls := binaryScheduleCalls slot₀ widthPlacementSlot_injective hd pay hhd hpay hQplacement hT
    spec hR hB rowBits Lc L hwidth hBin hrow hrowNe hrowValue
  have hcore (i : Fin (repairT + 6)) : S.R (e₀ i) = coreWords i := by
    rw [hinput]
    exact sharedScheduleInputBank_core (fieldCore repairHost.src) coreWords spec bankWords Lc L B rowBits l.flatten i
  have hplacement (r : BinaryScheduleReg t₀ 3) :
      S.R (slot₀ r) = binaryScheduleInputWords spec bankWords Lc L B rowBits l.flatten r := by
    rw [hinput]
    exact sharedScheduleInputBank_schedule (fieldCore repairHost.src) coreWords spec bankWords Lc L B rowBits l.flatten hsrc r
  have hready : ∀ j, (calls j).Ready S := binaryScheduleCalls_ready slot₀ widthPlacementSlot_injective
    hd pay hhd hpay hQplacement hT spec hR hB rowBits Lc L hwidth hBin hrow hrowNe hrowValue
    bankWords hpay0 hpriv hhdr0 hother S hL l.flatten hplacement
  have data' : RepairPendingWidthData p₀ X rb hG₀ hK₀ active s wb wm wp wk R B
      (repairCanonicalHeaders p₀ X rb R B) (embStk fieldCore (embStk e₀ S)).R :=
    data.congr p₀ X rb hG₀ hK₀ active s (fun key => hcore (fieldCore (repairSetupSource key)))
  exact placedExactSelectiveWidth_exec ρ n m X rb scale active s body widthBody hwidthBody
    e₀ widthPlacementEmbed_injective ι body' hbody Lr Lm hr hm
    hQ hA hscale hn hR hB hrb hs v S data' (fun key => (hcore _).trans (hempty key))
    (fun j => hL _) (fun j hj => (hcore _).trans (hblank j hj))
    ((hcore _).trans hrowWidth) ((hcore _).trans hmaskWidth)
    (fun i hi => (hcore _).trans (hscratch i hi)) ((hcore _).trans hrow0) ((hcore _).trans hmask0)
    l hl hlen ((hcore _).trans hsrc) (slot₀ .tmp) H hfit w hw reservoir calls
    (binaryScheduleCalls_spec slot₀ widthPlacementSlot_injective hd pay hhd hpay hQplacement hT spec hR hB
      rowBits Lc L hwidth hBin hrow hrowNe hrowValue) hready

end IntegerMultBounds.MathlibTM2.Routing
