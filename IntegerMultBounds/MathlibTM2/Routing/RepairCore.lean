module

public import IntegerMultBounds.MathlibTM2.Routing.RepairPlacement
public import IntegerMultBounds.MathlibTM2.Routing.SelectiveRepairPass
public import IntegerMultBounds.MathlibTM2.Node.CompactCore

/-!
# Exact key/route/repair execution on one shared bank

The actual full-rank key pass, complete routing schedule and concrete classifier
with scan/sort/merge/strip repair compose on the same physical stream. This
prepared boundary still needs executed metadata installation and final cleanup.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable {Q K : ℕ} {P U : Type}
variable (p : Par) (X rb : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

structure RepairPrepared (R B : ℕ) (headers : Fin 2 → Fin 5 → List Bool)
    (S : Stacks repairT (prime + K)) : Prop where
  routing : SelectivePrepared p X repairHost hG hK active s
    (fieldsLen (selectiveKeyLen p X rb) + B) (R * 2 ^ fieldsLen (selectiveLen p X)) headers S
  key : KeyPatternInv p X rb active s repairKey S.R 0
  bad : BadInv p X repairBad S.R 0
  payload : (S.R (repairReg .payload)).length = B
  keyLength : (S.R (repairReg .keyLength)).length = fieldsLen (selectiveKeyLen p X rb)
  acc : S.R (repairReg .acc) = []

noncomputable def repairCore
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) : Pr P repairT Q (prime + K) U :=
  .seq (selectiveKeyPass repairKey repairHost.src (repairReg .acc) (repairReg .payload) repairHost.tmp)
    (.seq (Prog.seqList (progW.map (fun o =>
      selectivePass repairHost repairHost_valid hQ repairHost_swapT o.1)))
      (repairAtC (badClassifier repairBad hA) (codeSel (badC (prime + K) hA))
        repairHost.src (repairHost.dst 0) (repairHost.dst 1) (repairHost.aux 0) (repairHost.aux 1)
        repairHost.ctr (repairReg .payload) (repairReg .keyLength) repairHost.cnt repairHost.tmp
        (repairBad .st) (fun f => repairBad (.fld f)) (fun r => repairBad (.spare r))))

noncomputable def repairScanCost (R B : ℕ) : ℕ := by
  classical
  let k := fieldsLen (selectiveKeyLen p X rb)
  exact (R * 2 ^ fieldsLen (selectiveLen p X)) *
      (2 * idxStepCost (badClassifierCost p.wy) (k + B) (selectiveLen p X) + 6 * (k + B) + 15) +
    k * (((Finset.range (R * 2 ^ fieldsLen (selectiveLen p X))).filter
      fun i => ¬ Good p (selectiveView p X i)).card * (12 * k + 6 * B + 13)) +
    10 * k + 8 * fieldsLen (selectiveLen p X) + 8 * 5 + 18

noncomputable def repairCoreCost (R B : ℕ) (S : Stacks repairT (prime + K)) : ℝ :=
  selectiveKeyPassCost p X rb (R * 2 ^ fieldsLen (selectiveLen p X)) B +
    ((progW.map (fun o => selectiveOpCost p X repairT R (fieldsLen (selectiveKeyLen p X rb) + B)
      (fun c => ∑ j, (S.R (repairHost.swaps c j)).length) o.1)).sum + 1) +
    repairScanCost p X rb R B

/-- Actual all-address exact selective update from shared prepared metadata. -/
theorem repairCore_exec (hGK : p.G + 1 < p.K)
    (body : P → Pr P repairT Q (prime + K) U)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) {R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (headers : Fin 2 → Fin 5 → List Bool)
    (hv : ∀ c j, Counter.value (headers c j) =
      selectiveSwapValues p X R (fieldsLen (selectiveKeyLen p X rb) + B) c j)
    (hc : ∀ c j, GrowingCounterData.Canonical (headers c j))
    (v : HS repairT Q (prime + K) U) (S : Stacks repairT (prime + K))
    (prepared : RepairPrepared p X rb hG hK active s R B headers S)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (hsrc : S.R repairHost.src = l.flatten) :
    ∃ (v' : HS repairT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ repairCoreCost p X rb R B S ∧
      Exec body (repairCore hQ hA) (mk v S) steps
        (mk v' { S with R := Function.update S.R repairHost.src (moveRecs (selectiveIdealPerm hK active s R hs) l).flatten }) := by
  have hgk : p.G < p.K := by omega
  let k := fieldsLen (selectiveKeyLen p X rb)
  let keyed := keyRecs k (selectiveIdealPerm hK active s R hs) l
  let actual := listPerm (selectivePerm p X hG hK hgk active s R) progW
  obtain ⟨v₁, hu₁, he₁⟩ := selectiveKeyPass_exec p X rb hK active s hs body repairKey
    repairKey_injective repairHost.src (repairReg .acc) (repairReg .payload) repairHost.tmp
    repairKey_src repairKey_acc repairKey_driver hB l hl (fun r hr => (hlen r hr).1)
    v S prepared.key hsrc prepared.acc prepared.payload prepared.routing.tmp
  have hkl : keyed.length = R * 2 ^ fieldsLen (selectiveLen p X) := length_keyRecs _ _ _
  have hkb : ∀ r ∈ keyed, r.length = k + B ∧ ∀ a ∈ r, a.val < 8 := fun r hr =>
    ⟨keyRecs_length_mem k B _ l hl (fun r hr => (hlen r hr).1) r hr,
      mem_keyRecs_sym hl (fun r hr => (hlen r hr).2) r hr⟩
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := selectivePrepared_exec p X hG hK hgk active s body
    repairHost repairHost_valid hQ repairHost_swapT hR (by omega) headers hv hc S
    prepared.routing keyed hkl hkb v₁
  let routed := (moveRecs actual keyed).flatten
  have hb : BadInv p X repairBad (Function.update S.R repairHost.src routed) 0 := by
    intro r hr
    rw [Function.update_of_ne (repairBad_src r)]
    exact prepared.bad r hr
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := selectiveRepair_exec p X hG hK hgk active s hs R body
    (badClassifier_spec p X repairBad repairBad_injective hA hG hGK body)
    repair_scan_index_separate repair_fields_payload repair_fields_keyLength repair_scan_regs
    repair_sort_separate repair_sort_injective repair_sort_fields hB
    (selectiveKey_rank_bound p X rb R hrb) l hl (fun r hr => (hlen r hr).1)
    v₂ { S with R := Function.update S.R repairHost.src routed } (by
      change Function.update S.R repairHost.src routed repairHost.src = routed
      simp)
    (by simpa using prepared.routing.dst 0) (by simpa using prepared.routing.dst 1)
    (by simpa using prepared.routing.aux 0) (by simpa using prepared.routing.aux 1)
    (by simpa using prepared.routing.ctr) (by simpa using prepared.payload)
    (by simpa using prepared.keyLength) (by simpa using prepared.routing.cnt)
    (by simpa using prepared.routing.tmp)
    (fun r => by simpa [repairBad] using prepared.bad (.spare r) (by simp)) hb
  have he₃' := he₃
  simp only [Function.update_idem] at he₃'
  refine ⟨v₃, selectiveKeyPassCost p X rb (R * 2 ^ fieldsLen (selectiveLen p X)) B + (m₂ + m₃),
    hu₃.trans (hu₂.trans hu₁), ?_, Exec.seq he₁ (Exec.seq he₂ he₃')⟩
  unfold repairCoreCost
  have hm₃' : (m₃ : ℝ) ≤ repairScanCost p X rb R B := by exact_mod_cast hm₃
  push_cast
  linarith

end IntegerMultBounds.MathlibTM2.Routing
