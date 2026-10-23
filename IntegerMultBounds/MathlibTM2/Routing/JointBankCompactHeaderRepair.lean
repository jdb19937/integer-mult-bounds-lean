module

public import IntegerMultBounds.MathlibTM2.Routing.PlacedCompactHeaderRepair
public import IntegerMultBounds.MathlibTM2.Routing.CompactHeaderPlacementLayout
public import IntegerMultBounds.MathlibTM2.Routing.SharedScheduleInput
public import IntegerMultBounds.MathlibTM2.Routing.BinaryScheduleCalls
public import IntegerMultBounds.MathlibTM2.Routing.PlacementAround
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveCompactGeneratedClassifiers
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveCompactConfiguration
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveCompact
public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveEmbedded
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Concrete shared-bank execution of placement, header-generating exact
repair and inverse placement. Initial bank words derive placement readiness. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable section

variable {t₀ Q K : ℕ} {P P' U : Type}
variable (ρ n m X rb scale : ℕ) (active : Fin n → Bool)
  (s : Fin n → SlotSource (routingParameters ρ n m (Nat.clog 2 scale)) X)

local notation "p₀" => routingParameters ρ n m (Nat.clog 2 scale)
local notation "hG₀" => And.left (routingParameters_guards ρ n m (Nat.clog 2 scale))
local notation "hK₀" => And.left (And.right (routingParameters_guards ρ n m (Nat.clog 2 scale)))

local notation "T₀" => compactHeaderPlacementT t₀
local notation "e₀" => compactHeaderPlacementEmbed (t₀ := t₀)
local notation "slot₀" => compactHeaderPlacementSlot (t₀ := t₀)

theorem jointBankCompactHeaderRepair_exec (body : P → Pr P repairT Q (prime + K) U)
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
    (v : HS T₀ Q (prime + K) U) (S : Stacks repairCompactConfigurationT (prime + K))
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
    (D : Stacks repairCompactHeaderT (prime + K)) (hHeaderProject : embStk sharedHeaderCore D = S')
    (headerBody : P → Pr P repairCompactHeaderT Q (prime + K) U)
    (hHeaderBody : ∀ f, headerBody f = embProg sharedHeaderCore id (classifierBody f))
    (Lrow Lwidth : ℕ) (hRbin : R < 2 ^ Lrow) (hWCbin : (p₀).wc < 2 ^ Lwidth)
    (hrowInput : D.R (sharedHeaderBinary 0) = binSyms Lrow R)
    (hwidthInput : D.R (sharedHeaderBinary 1) = binSyms Lwidth (p₀).wc)
    (hheaders : ∀ c i, D.R (repairCompactSharedHeaderBank c (.exchange (.base (.header i)))) = [])
    (hwork : ∀ r : HeaderWorkRole, (∀ i, r ≠ .binary i) → D.R (sharedHeaderWork r) = [])
    (ι : P → P')
    (outerBody : P' → Pr P' T₀ Q (prime + K) U)
    (houter : ∀ f, outerBody (ι f) = embProg e₀ ι (headerBody f))
    (S'' : Stacks T₀ (prime + K)) (houterProject : embStk e₀ S'' = D)
    (H : ℕ) (hplacementFit : 9 * H ≤ fieldsLen (selectiveLen p₀ X))
    (w : ℕ) (hw : w ≤ H) (reservoir : Fin 3)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd) (hpay : ∀ k, hd k ≠ pay)
    (hQplacement : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T₀)
    (rowBits : List Bool) (Lc Lp : ℕ) (hwidthPlacement : fieldsLen (selectiveLen p₀ X) < 2 ^ Lc) (hBin : B < 2 ^ Lp)
    (hrowCanonical : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ []) (hrowValue : Counter.value rowBits = R)
    (bankWords : Fin (swapT t₀) → List (Fin (prime + K + 4)))
    (hpay0 : bankWords (reg pay) = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → bankWords j = [])
    (hhdr0 : ∀ k, bankWords (reg (hd k)) = [])
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) → ∀ x ∈ bankWords (reg i), x ≠ blank ∧ x.val < prime + 4)
    (hleft : ∀ j, S''.L j = [])
    (hbank : S''.R = sharedScheduleInputBank (repairCompactHeaderRawCore repairHost.src) D.R
      (reservoirExchangeSpecs (fieldsLen (selectiveLen p₀ X)) H hplacementFit w hw reservoir)
      bankWords Lc Lp B rowBits l.flatten) :
    let calls := binaryScheduleCalls slot₀ compactHeaderPlacementSlot_injective hd pay hhd hpay hQplacement hT
      (reservoirExchangeSpecs (fieldsLen (selectiveLen p₀ X)) H hplacementFit w hw reservoir) hR hB rowBits Lc Lp
      hwidthPlacement hBin hrowCanonical hrowNe hrowValue
    let forward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hplacementFit w hw reservoir R false
    let backward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) H hplacementFit w hw reservoir R true
    let l₁ := moveRecs forward l
    let C₁ : Stacks repairCompactHeaderT (prime + K) := { D with R := Function.update D.R (repairCompactHeaderRawCore repairHost.src) l₁.flatten }
    ∃ (v' : HS T₀ Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ binaryExchangeChainCost calls S'' (reservoirExchangeOrder false) +
        compactHeaderRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B Lr Lm LK Ln Lo Lt Lrow Lwidth Lw Lg L C₁ +
        binaryExchangeChainCost calls S'' (reservoirExchangeOrder true) ∧
      Exec outerBody (.seq (binaryExchangeChain calls (reservoirExchangeOrder false))
        (.seq (embProg e₀ ι (compactHeaderRepairProgram p₀ X rb hG₀ hK₀ active s Lr Lm Lw Lg L hQ hA))
          (binaryExchangeChain calls (reservoirExchangeOrder true))))
        (mk v S'') steps (mk v' { S'' with R := Function.update S''.R (e₀ (repairCompactHeaderRawCore repairHost.src)) (moveRecs backward (moveRecs (selectiveIdealPerm hK₀ active s R hs) l₁)).flatten }) := by
  let spec := reservoirExchangeSpecs (fieldsLen (selectiveLen p₀ X)) H hplacementFit w hw reservoir
  let calls := binaryScheduleCalls slot₀ compactHeaderPlacementSlot_injective hd pay hhd hpay hQplacement hT
      (reservoirExchangeSpecs (fieldsLen (selectiveLen p₀ X)) H hplacementFit w hw reservoir) hR hB rowBits Lc Lp
      hwidthPlacement hBin hrowCanonical hrowNe hrowValue
  have hstream : D.R (repairCompactHeaderRawCore repairHost.src) = l.flatten := by
    rw [← hproject, ← hHeaderProject] at hsrc
    exact hsrc
  have hplacement (r : BinaryScheduleReg t₀ 3) :
      S''.R (slot₀ r) = binaryScheduleInputWords spec bankWords Lc Lp B rowBits l.flatten r := by
    rw [hbank]
    exact sharedScheduleInputBank_schedule (repairCompactHeaderRawCore repairHost.src) D.R
      spec bankWords Lc Lp B rowBits l.flatten hstream r
  have hready : ∀ j, (calls j).Ready S'' := binaryScheduleCalls_ready slot₀ compactHeaderPlacementSlot_injective
    hd pay hhd hpay hQplacement hT spec hR hB rowBits Lc Lp hwidthPlacement hBin hrowCanonical hrowNe hrowValue
    bankWords hpay0 hpriv hhdr0 hother S'' hleft l.flatten hplacement
  have houterSrc : S''.R (e₀ (repairCompactHeaderRawCore repairHost.src)) = l.flatten := by
    have hc := sharedScheduleInputBank_core (repairCompactHeaderRawCore repairHost.src) D.R
      spec bankWords Lc Lp B rowBits l.flatten (repairCompactHeaderRawCore repairHost.src)
    rw [hbank]
    exact hc.trans hstream
  exact placedCompactHeaderRepair_exec ρ n m X rb scale active s body descriptorBody hdescriptor body' hbody
    classifierBody hclassifier Lr Lm hr hm Lw Lg L hQ hA hscale hn hR hB hrb hs v S data hempty hL hblank hwidthFit hW hsize
    hwidth hsourceWidth hinput hscratch hdesc hrowWidth hmaskWidth hwidthScratch hrow hmask l hl hlen hsrc S' hproject
    LK Ln Lo Lt hsegment hcountFit hoffsetFit htopFit hsegmentInput hrunInput hcountInput hoffsetInput
    hphaseOffsetInput htopInput hclassifierScratch htemporary hphase D hHeaderProject headerBody hHeaderBody Lrow Lwidth hRbin hWCbin
    hrowInput hwidthInput hheaders hwork e₀ compactHeaderPlacementEmbed_injective ι outerBody houter
    S'' houterProject (slot₀ .tmp) H hplacementFit w hw reservoir calls
    (binaryScheduleCalls_spec slot₀ compactHeaderPlacementSlot_injective hd pay hhd hpay hQplacement hT spec hR hB
      rowBits Lc Lp hwidthPlacement hBin hrowCanonical hrowNe hrowValue) hready houterSrc

end
end IntegerMultBounds.MathlibTM2.Routing
