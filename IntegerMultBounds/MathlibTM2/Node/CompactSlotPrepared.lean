module

public import IntegerMultBounds.MathlibTM2.Node.CompactSlotXor
public import IntegerMultBounds.MathlibTM2.Node.CompactHeaderBank
public import IntegerMultBounds.MathlibTM2.Node.CompactHeaderClear

/-! Runtime unary descriptors prepare the native bank, execute an encoded slot XOR,
and clear the descriptors. Only the live stream changes in the complete frame. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData
noncomputable section
variable {s : Shape} {T Q K : ℕ} {U F : Type}

private lemma clear_fill_update {A H : ℕ}
    (dst : Fin H → Fin T) (hd : Function.Injective dst)
    (words : Fin H → List (Fin (A+4))) (R : Fin T → List (Fin (A+4)))
    (str : Fin T) (out : List (Fin (A+4)))
    (hempty : ∀ i,R (dst i)=[]) (hstr : ∀ i,dst i≠str) :
    compactHeaderFill dst (fun _ => []) H
      (Function.update (compactHeaderFill dst words H R) str out) =
      Function.update R str out := by
  funext z
  by_cases hz : ∃ i,dst i=z
  · obtain ⟨i,rfl⟩ := hz
    rw [compactHeaderFill_at dst hd,ite_eq_left i.isLt,
      Function.update_of_ne (hstr i),hempty]
  · have ho : ∀ i,dst i≠z := by simpa using hz
    rw [compactHeaderFill_out _ _ _ _ _ ho]
    by_cases hs : z=str
    · subst z
      simp only [Function.update_self]
    · rw [Function.update_of_ne hs,Function.update_of_ne hs,
        compactHeaderFill_out _ _ _ _ _ ho]

/-- Fixed program parameters contain register addresses, with all descriptor
values supplied at execution time in unary source stacks. -/
def compactSlotPreparedProg (hQ : compactRuntimeStates ≤ Q)
    (ι : Fin ActivePrefixStageRuntimeProgram.count → Fin T) (hι : Function.Injective ι)
    (hT : ActivePrefixStageRuntimeProgram.count ≤ T)
    (src : Fin 13 → Fin T) (t₁ t₂ str tmp : Fin T) : Pr F T Q (prime+K) U :=
  let dst := fun i => ι (compactRawHeader compactRuntimeCount i)
  .seq (compactHeadersBuild src dst t₁ t₂)
    (.seq (compactSlotXorProg hQ ι hι hT str tmp) (compactHeadersClear dst))

def compactSlotPreparedCost (T K D : ℕ) (d : Inputs s)
    (hp : 1<d.stage.f → ActivePrefixStageRuntimeData.Packed d D) (length : ℕ) :=
  (∑ i : Fin 13,(16*ActivePrefixStageHeadersData.originalValues d.stage d.rows i+5))+1 +
  compactSlotXorCost T K D d hp length +
  (∑ i : Fin 13,(2*(compactHeaderWord (prime+K)
    (ActivePrefixStageHeadersData.originalValues d.stage d.rows i)).length+2))+1

open IntegerMultBounds.MathlibTM2.Layer in
/-- Complete runtime preparation, encoded slot action, and cleanup. In particular,
all unary sources, scratch tapes, and native bank tapes are restored exactly. -/
theorem compactSlotPrepared_exec {n a₀ k ρ left right rows R r w : ℕ}
    (body : F → Pr F T Q (prime+K) U)
    (hQ : compactRuntimeStates ≤ Q)
    (ι : Fin ActivePrefixStageRuntimeProgram.count → Fin T) (hι : Function.Injective ι)
    (hT : ActivePrefixStageRuntimeProgram.count ≤ T)
    (src : Fin 13 → Fin T) (t₁ t₂ str tmp : Fin T)
    (hsrc : ∀ i j,src i≠ι j) (hsrc₁ : ∀ i,src i≠t₁) (hsrc₂ : ∀ i,src i≠t₂)
    (_hsrcstr : ∀ i,src i≠str) (_hsrctmp : ∀ i,src i≠tmp)
    (h₁bank : ∀ j,ι j≠t₁) (h₂bank : ∀ j,ι j≠t₂) (h₁₂ : t₁≠t₂)
    (_h₁str : t₁≠str) (_h₂str : t₂≠str) (_h₁tmp : t₁≠tmp) (_h₂tmp : t₂≠tmp)
    (hst : str≠tmp) (hstr : ∀ j,ι j≠str) (htmp : ∀ j,ι j≠tmp)
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x y : Fin m) (hxy : x≠y)
    (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (hr : 0<rows) (hrecord : s.bits+1≤s.payload)
    (hA : 4≤prime+K) (hpayload : s.payload=3*(r*w))
    (hvolume : rows*s.recordWidth=(R*2^n)*s.payload)
    (D : ℕ)
    (hp : 1<k → ActivePrefixStageRuntimeData.Packed
      (compactRecursiveInputs layout x y hxy rows hG hGK hr hrecord) D)
    (Z : ZArr (Fin R × Fin r) n)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hL : ∀ j,S.L (ι j)=[]) (hbank : ∀ j,S.R (ι j)=[])
    (hR : S.R str=encZ (prime+K) w Z)
    (htmp0 : S.R tmp=[]) (h₁ : S.R t₁=[]) (h₂ : S.R t₂=[])
    (hvalues : ∀ i,(S.R (src i)).length = ActivePrefixStageHeadersData.originalValues
      (compactRecursiveInputs layout x y hxy rows hG hGK hr hrecord).stage rows i) :
    ∃ v' steps,v'.user=v.user ∧
      steps ≤ compactSlotPreparedCost T K D
        (compactRecursiveInputs layout x y hxy rows hG hGK hr hrecord) hp
        (encZ (prime+K) w Z).length ∧
      Exec body (compactSlotPreparedProg hQ ι hι hT src t₁ t₂ str tmp) (mk v S) steps
        (mk v' {S with R:=Function.update S.R str (encZ (prime+K) w (pullM (compactRecursiveBits layout) (sxXorCol x y) Z))}) := by
  let d := compactRecursiveInputs layout x y hxy rows hG hGK hr hrecord
  let dst : Fin 13 → Fin T := fun i => ι (compactRawHeader compactRuntimeCount i)
  let words := fun i => compactHeaderWord (prime+K) (S.R (src i)).length
  have hd : Function.Injective dst := hι.comp (compactRawHeader_injective compactRuntimeCount)
  have hdststr : ∀ i,dst i≠str := fun i => hstr _
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := compactHeadersBuild_exec body src dst hd t₁ t₂
    (fun i j => hsrc i _) hsrc₁ hsrc₂ (fun i => h₁bank _) (fun i => h₂bank _) h₁₂
    v S (fun i => hbank _) h₁ h₂
  let S₁ : Stacks T (prime+K) := {S with R:=compactHeaderFill dst words 13 S.R}
  have hS₁out (z : Fin T) (hz : ∀ i,dst i≠z) : S₁.R z=S.R z :=
    compactHeaderFill_out dst words 13 S.R z hz
  have hraw : ∀ i,dst i≠ι compactRuntimeRaw := by
    intro i he
    have hv := congrArg Fin.val (hι he)
    have hi := i.isLt
    change i.val=65 at hv
    omega
  have hhdr : ∀ j,j≠compactRuntimeRaw → S₁.R (ι j)=compactRawWords d (fun _ => false) j := by
    intro j hj
    exact compactHeaderFill_native d compactRuntimeCount ι hι src S.R hvalues hbank j
      (fun h => hj (Fin.ext h))
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := compactSlotXor_exec body hQ ι hι hT str tmp hst hstr htmp
    layout x y hxy hG hGK hr hrecord hA hpayload hvolume D hp Z v₁ S₁ hL
    ((hS₁out str hdststr).trans hR)
    ((hS₁out tmp (fun i => htmp _)).trans htmp0)
    ((hS₁out (ι compactRuntimeRaw) hraw).trans (hbank _)) hhdr
  let output := encZ (prime+K) w (pullM (compactRecursiveBits layout) (sxXorCol x y) Z)
  let S₂ : Stacks T (prime+K) := {S₁ with R:=Function.update S₁.R str output}
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := compactHeadersClear_exec body dst hd v₂ S₂
  have hS₂dst (i : Fin 13) : S₂.R (dst i)=words i := by
    change Function.update S₁.R str output (dst i)=words i
    rw [Function.update_of_ne (hdststr i)]
    exact (compactHeaderFill_at dst hd words 13 S.R i).trans (ite_eq_left i.isLt)
  have hvalues' : ∀ i,(S.R (src i)).length = ActivePrefixStageHeadersData.originalValues d.stage d.rows i := by
    simpa only [d,compactRecursiveInputs] using hvalues
  change m₂ ≤ compactSlotXorCost T K D d hp (encZ (prime+K) w Z).length at hm₂
  have hcost₁ : m₁≤(∑ i : Fin 13,(16*ActivePrefixStageHeadersData.originalValues d.stage d.rows i+5))+1 := by
    simpa only [hvalues'] using hm₁
  have hcost₃ : m₃≤(∑ i : Fin 13,(2*(compactHeaderWord (prime+K)
      (ActivePrefixStageHeadersData.originalValues d.stage d.rows i)).length+2))+1 := by
    simpa only [hS₂dst,words,hvalues'] using hm₃
  refine ⟨v₃,m₁+(m₂+m₃),hu₃.trans (hu₂.trans hu₁),?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) rfl ?_⟩
  · change _ ≤ compactSlotPreparedCost T K D d hp _
    unfold compactSlotPreparedCost
    omega
  · congr 1
    refine Stacks.ext rfl rfl rfl ?_
    exact clear_fill_update dst hd words S.R str output (fun i => hbank _) hdststr

end
end IntegerMultBounds.MathlibTM2.Node
