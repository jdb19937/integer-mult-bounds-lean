module

public import IntegerMultBounds.MathlibTM2.Node.CompactDescriptorBank
public import IntegerMultBounds.MathlibTM2.Node.CompactEncodingOffset
public import IntegerMultBounds.MathlibTM2.Node.CompactSlotPrepared
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Fully computed compact slot execution: runtime descriptors, native execution,
and cleanup. Low address digits are folded without moving the encoded stream. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData
noncomputable section
variable {s : Shape} {T Q K : ℕ} {U P : Type}

def compactComputedOutputs (e : Fin 30 → Fin T) (i : Fin 8) : Fin T :=
  e ⟨16+i.val,by have := i.isLt; omega⟩

lemma compactComputedOutputs_injective (e : Fin 30 → Fin T) (he : Function.Injective e) :
    Function.Injective (compactComputedOutputs e) := by
  intro i j hij
  have hv := congrArg Fin.val (he hij)
  apply Fin.ext
  simpa [compactComputedOutputs] using hv

lemma compactComputedOutputs_at {A : ℕ} (e : Fin 30 → Fin T) (he : Function.Injective e)
    (R : Fin T → List (Fin (A+4))) (i : Fin 8) :
    compactDescriptorBankState e R (compactComputedOutputs e i) =
      List.replicate (compactDescriptorBankValues
        (fun j => (R (e (Fin.castAdd 14 j))).length) i) tick := by
  fin_cases i <;> simp [compactComputedOutputs,compactDescriptorBankState,he.eq_iff]

private lemma computed_clear_update {A : ℕ} (e : Fin 30 → Fin T) (he : Function.Injective e)
    (R : Fin T → List (Fin (A+4))) (str : Fin T) (out : List (Fin (A+4)))
    (hz : ∀ i : Fin 30, 16 ≤ i.val → R (e i)=[]) (hstr : ∀ i,e i≠str) :
    compactHeaderFill (compactComputedOutputs e) (fun _ => []) 8
      (Function.update (compactDescriptorBankState e R) str out) = Function.update R str out := by
  funext z
  by_cases hmem : ∃ i,compactComputedOutputs e i=z
  · obtain ⟨i,rfl⟩ := hmem
    rw [compactHeaderFill_at _ (compactComputedOutputs_injective e he),ite_eq_left i.isLt,
      Function.update_of_ne (show compactComputedOutputs e i≠str from hstr _)]
    exact (hz _ (by simp)).symm
  · have hout : ∀ i,compactComputedOutputs e i≠z := by simpa using hmem
    rw [compactHeaderFill_out _ _ _ _ _ hout]
    by_cases hzs : z=str
    · subst z; simp only [Function.update_self]
    · rw [Function.update_of_ne hzs,Function.update_of_ne hzs]
      apply compactDescriptorBank_frame
      intro j hj hj' heq
      let i : Fin 8 := ⟨j.val-16,by omega⟩
      have hi : compactComputedOutputs e i=e j := by
        apply congrArg e
        apply Fin.ext
        dsimp [compactComputedOutputs,i]
        omega
      exact hout i (hi.trans heq.symm)

/-- The native row count includes every unselected high address digit. -/
def compactSlotComputedInputs {n a₀ k ρ left right : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x y : Fin m) (hxy : x≠y)
    (rowCount : ℕ) (hG : 1 ≤ s.guard) (hGK : s.guard+1 ≤ s.chunk)
    (hr : 0<rowCount) (hrecord : s.bits+1 ≤ s.payload) : Inputs s :=
  compactRecursiveInputs layout x y hxy (2^(n-s.bits)*rowCount) hG hGK
    (Nat.mul_pos (pow_pos (by decide) _) hr) hrecord

lemma compactSlotComputed_volume {n a₀ k ρ left right : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (rowCount : ℕ) :
    (2^(n-s.bits)*rowCount)*s.recordWidth = (rowCount*2^n)*s.payload := by
  unfold Shape.recordWidth
  rw [show (2^(n-s.bits)*rowCount)*(2^s.bits*s.payload) =
    (rowCount*(2^(n-s.bits)*2^s.bits))*s.payload by ring]
  rw [←pow_add,Nat.sub_add_cancel layout.totalFits]

/-- Conversion scratch reuses restored descriptor roles 27 and 28. -/
def compactSlotComputedProg (hQ : compactRuntimeStates ≤ Q)
    (ι : Fin ActivePrefixStageRuntimeProgram.count → Fin T) (hι : Function.Injective ι)
    (hT : ActivePrefixStageRuntimeProgram.count ≤ T)
    (e : Fin 30 → Fin T) (str tmp : Fin T) : Pr P T Q (prime+K) U :=
  .seq (compactDescriptorBankProg e) <|
  .seq (compactSlotPreparedProg hQ ι hι hT (compactDescriptorBankSources e) (e 27) (e 28) str tmp)
    (compactHeadersClear (compactComputedOutputs e))

def compactSlotComputedCost (T K D : ℕ) (d : Inputs s)
    (hp : 1<d.stage.f → ActivePrefixStageRuntimeData.Packed d D)
    (input : Fin 16 → ℕ) (length : ℕ) :=
  compactDescriptorBankCost input + compactSlotPreparedCost T K D d hp length +
    (∑ i : Fin 8,(2*compactDescriptorBankValues input i+2))+1

/-- Actual runtime computation through the original low-offset stream semantics.
Only current-node/global unary length facts are supplied; descriptors and the
native bit volume are proved internally. All workspace registers are restored. -/
theorem compactSlotComputed_exec {n a₀ k ρ left right o rowCount r w : ℕ}
    (body : P → Pr P T Q (prime+K) U)
    (hQ : compactRuntimeStates ≤ Q)
    (ι : Fin ActivePrefixStageRuntimeProgram.count → Fin T) (hι : Function.Injective ι)
    (hT : ActivePrefixStageRuntimeProgram.count ≤ T)
    (e : Fin 30 → Fin T) (he : Function.Injective e) (str tmp : Fin T)
    (hebank : ∀ i j,e i≠ι j) (hestr : ∀ i,e i≠str) (hetmp : ∀ i,e i≠tmp)
    (hst : str≠tmp) (hstr : ∀ j,ι j≠str) (htmp : ∀ j,ι j≠tmp)
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x y : Fin m) (hxy : x≠y)
    (hG : 1 ≤ s.guard) (hGK : s.guard+1 ≤ s.chunk) (hr : 0<rowCount)
    (hrecord : s.bits+1 ≤ s.payload) (hA : 4 ≤ prime+K)
    (hpayload : s.payload=2^o*(3*(r*w))) (D : ℕ)
    (hp : 1<k → ActivePrefixStageRuntimeData.Packed
      (compactSlotComputedInputs layout x y hxy rowCount hG hGK hr hrecord) D)
    (Z : ZArr (Fin rowCount × Fin r) (o+n))
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hL : ∀ j,S.L j=[]) (hbank : ∀ j,S.R (ι j)=[])
    (hz : ∀ i : Fin 30, 16 ≤ i.val → S.R (e i)=[])
    (hR : S.R str=encZ (prime+K) w Z) (htmp0 : S.R tmp=[])
    (hin : ∀ i : Fin 16,(S.R (e (Fin.castAdd 14 i))).length =
      compactDescriptorBankInputs layout o rowCount r w x y i) :
    ∃ v' steps,v'.user=v.user ∧
      steps ≤ compactSlotComputedCost T K D
        (compactSlotComputedInputs layout x y hxy rowCount hG hGK hr hrecord) hp
        (compactDescriptorBankInputs layout o rowCount r w x y) (encZ (prime+K) w Z).length ∧
      Exec body (compactSlotComputedProg hQ ι hι hT e str tmp) (mk v S) steps
        (mk v' {S with R:=Function.update S.R str (encZ (prime+K) w
          (pullM (compactOffsetEmbedding o (compactRecursiveBits layout)) (sxXorCol x y) Z))}) := by
  let input := compactDescriptorBankInputs layout o rowCount r w x y
  let d := compactSlotComputedInputs layout x y hxy rowCount hG hGK hr hrecord
  have hinput : (fun i : Fin 16 => (S.R (e (Fin.castAdd 14 i))).length)=input := funext hin
  have hchunk : 1 ≤ (S.R (e 1)).length := by
    have h1 := hin 1
    change (S.R (e 1)).length=s.chunk at h1
    rw [h1]
    exact lt_of_le_of_lt (Nat.zero_le ρ) layout.selectedFits
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := compactDescriptorBank_runs body e he S.R hchunk hz v S hL rfl
  let S₁ : Stacks T (prime+K) := {S with R:=compactDescriptorBankState e S.R}
  have hS₁out (z : Fin T) (houtside : ∀ i,e i≠z) : S₁.R z=S.R z :=
    compactDescriptorBank_frame e S.R z (fun i _ _ => (houtside i).symm)
  have hS₁scratch (i : Fin 30) (hi : 24 ≤ i.val) : S₁.R (e i)=[] := by
    change compactDescriptorBankState e S.R (e i)=[]
    rw [compactDescriptorBank_frame e S.R (e i)
      (fun j _ hj => he.ne (by intro hij; have hh := congrArg Fin.val hij; omega))]
    exact hz i (by omega)
  have hsrc₁ : ∀ i,compactDescriptorBankSources e i≠e 27 := by
    intro i; fin_cases i <;> simp [compactDescriptorBankSources,he.eq_iff]
  have hsrc₂ : ∀ i,compactDescriptorBankSources e i≠e 28 := by
    intro i; fin_cases i <;> simp [compactDescriptorBankSources,he.eq_iff]
  have hvalues : ∀ i,(S₁.R (compactDescriptorBankSources e i)).length =
      ActivePrefixStageHeadersData.originalValues d.stage d.rows i :=
    compactDescriptorBank_original_lengths layout o rowCount r w x y hxy hpayload e he S.R hin
  have hpayload' : s.payload=3*((2^o*r)*w) := hpayload.trans (compactOffset_payload o r w).symm
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := compactSlotPrepared_exec body hQ ι hι hT
    (compactDescriptorBankSources e) (e 27) (e 28) str tmp
    (fun i j => hebank _ j) hsrc₁ hsrc₂ (fun i => hestr _) (fun i => hetmp _)
    (fun j => (hebank 27 j).symm) (fun j => (hebank 28 j).symm) (he.ne (by decide))
    (hestr 27) (hestr 28) (hetmp 27) (hetmp 28) hst hstr htmp
    layout x y hxy hG hGK (Nat.mul_pos (pow_pos (by decide) _) hr) hrecord hA hpayload'
    (compactSlotComputed_volume layout rowCount) D hp (compactOffsetArray Z) v₁ S₁
    (fun j => hL _) (fun j => (hS₁out (ι j) (fun i => hebank i j)).trans (hbank j))
    ((hS₁out str hestr).trans (hR.trans (compactOffsetArray_encZ Z).symm))
    ((hS₁out tmp hetmp).trans htmp0) (hS₁scratch 27 (by decide)) (hS₁scratch 28 (by decide)) hvalues
  let output := encZ (prime+K) w
    (pullM (compactOffsetEmbedding o (compactRecursiveBits layout)) (sxXorCol x y) Z)
  have hout : encZ (prime+K) w
      (pullM (compactRecursiveBits layout) (sxXorCol x y) (compactOffsetArray Z))=output :=
    compactOffsetArray_encZ_pullM _ (compactRecursiveBits_injective layout) x y Z
  rw [hout] at he₂
  rw [compactOffsetArray_encZ] at hm₂
  let S₂ : Stacks T (prime+K) := {S₁ with R:=Function.update S₁.R str output}
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := compactHeadersClear_exec body (compactComputedOutputs e)
    (compactComputedOutputs_injective e he) v₂ S₂
  have hS₂len (i : Fin 8) : (S₂.R (compactComputedOutputs e i)).length =
      compactDescriptorBankValues input i := by
    change (Function.update S₁.R str output (compactComputedOutputs e i)).length=_
    rw [Function.update_of_ne (show compactComputedOutputs e i≠str from hestr _)]
    change (compactDescriptorBankState e S.R (compactComputedOutputs e i)).length=_
    rw [compactComputedOutputs_at e he S.R i,List.length_replicate,hinput]
  rw [hinput] at hm₁
  simp only [hS₂len] at hm₃
  change m₂ ≤ compactSlotPreparedCost T K D d hp (encZ (prime+K) w Z).length at hm₂
  refine ⟨v₃,m₁+(m₂+m₃),hu₃.trans (hu₂.trans hu₁),?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) rfl ?_⟩
  · change _ ≤ compactSlotComputedCost T K D d hp input _
    unfold compactSlotComputedCost
    omega
  · congr 1
    refine Stacks.ext rfl rfl rfl ?_
    exact computed_clear_update e he S.R str output hz hestr

end
end IntegerMultBounds.MathlibTM2.Node
