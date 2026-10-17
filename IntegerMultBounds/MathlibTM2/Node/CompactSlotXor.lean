module

public import IntegerMultBounds.MathlibTM2.Node.CompactRotRuntime
import IntegerMultBounds.MathlibTM2.Node.CompactEncoding
public import IntegerMultBounds.MathlibTM2.Node.CompactGeometryRecursive
import Mathlib.Tactic.Positivity.Finset

/-! Actual symbol-stream execution of the complete compact runtime, including both
three-bit codecs, their transfers, and restoration of the supplied native header bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData
open ActiveRepairLayoutRecordsData (Array)
noncomputable section
variable {s : Shape} {T Q K : ℕ} {U F : Type}

/-- The complete runtime's original raw array register. -/
def compactRuntimeRaw : Fin ActivePrefixStageRuntimeProgram.count :=
  ⟨65, by have := compactRuntimeCount; omega⟩

lemma compactRawWords_raw (d : Inputs s) (x : Array s d.rows) :
    compactRawWords (K:=K) d x compactRuntimeRaw = List.ofFn (fun j => bitSymbol (x j)) := by
  simp [compactRawWords,compactStageWords,compactRuntimeRaw]

lemma compactRawWords_other (d : Inputs s) (x y : Array s d.rows)
    (j : Fin ActivePrefixStageRuntimeProgram.count) (hj : j ≠ compactRuntimeRaw) :
    compactRawWords (K:=K) d x j = compactRawWords d y j := by
  have hv : j.val ≠ 65 := fun h => hj (Fin.ext h)
  simp [compactRawWords,compactStageWords,hv]

private theorem compactRuntime_exec_update (body : F → Pr F T Q (prime+K) U)
    (hQ : compactRuntimeStates ≤ Q)
    (ι : Fin ActivePrefixStageRuntimeProgram.count → Fin T) (hι : Function.Injective ι)
    (hT : ActivePrefixStageRuntimeProgram.count ≤ T)
    (D : ℕ) (d : Inputs s) (x : Array s d.rows)
    (hp : 1<d.stage.f → ActivePrefixStageRuntimeData.Packed d D)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hL : ∀ j, S.L (ι j)=[]) (hR : ∀ j, S.R (ι j)=compactRawWords d x j) :
    ∃ v' m, v'.user=v.user ∧
      m ≤ (T+12*ActivePrefixStageRuntimeProgram.count+5)*(ActivePrefixStageRuntimeData.cost D d hp) +
        6*(∑ j : Fin ActivePrefixStageRuntimeProgram.count,
          (compactRawWords (K:=prime+K) d x j).length) + 2*T+6*ActivePrefixStageRuntimeProgram.count+23 ∧
      Exec body (compactRuntimeProg hQ ι hι hT) (mk v S) m
        (mk v' { S with R := Function.update S.R (ι compactRuntimeRaw) (List.ofFn (fun j => bitSymbol (ActivePrefixStageRuntimeData.result d x j))) }) := by
  obtain ⟨v',m,hu,hm,he⟩ := compactRuntimeProg_exec body hQ ι hι hT D d x hp v S hL hR
  refine ⟨v',m,hu,hm,Exec.cast he rfl ?_⟩
  congr 1
  refine Stacks.ext rfl rfl ?_ ?_
  · funext z
    change (if z ∈ Set.range ι then [] else S.L z) = S.L z
    split_ifs with hz
    · obtain ⟨j,rfl⟩ := hz
      exact (hL j).symm
    · rfl
  · funext z
    change (if h : z ∈ Set.range ι then compactRawWords d (ActivePrefixStageRuntimeData.result d x) (Classical.choose h) else S.R z) =
      Function.update S.R (ι compactRuntimeRaw) (List.ofFn (fun j => bitSymbol (ActivePrefixStageRuntimeData.result d x j))) z
    by_cases hz : z ∈ Set.range ι
    · obtain ⟨j,rfl⟩ := hz
      simp only [dite_eq_left (Set.mem_range_self j)]
      have hj : Classical.choose (Set.mem_range_self (f:=ι) j) = j := hι (Classical.choose_spec (Set.mem_range_self j))
      rw [hj]
      by_cases hr : j=compactRuntimeRaw
      · subst j
        rw [Function.update_self,compactRawWords_raw]
      · rw [Function.update_of_ne (fun h => hr (hι h)),hR,compactRawWords_other d _ x j hr]
    · have hn : z ≠ ι compactRuntimeRaw := fun h => hz ⟨compactRuntimeRaw,h.symm⟩
      rw [dite_eq_right hz,Function.update_of_ne hn]

lemma compactRawWords_length (d : Inputs s) (x y : Array s d.rows)
    (j : Fin ActivePrefixStageRuntimeProgram.count) :
    (compactRawWords (K:=K) d x j).length = (compactRawWords (K:=K) d y j).length := by
  unfold compactRawWords compactStageWords
  split_ifs <;> simp

/-- Includes both codec traversals and both transfers, as well as complete native-bank normalization. -/
def compactSlotXorCost (T K D : ℕ) (d : Inputs s)
    (hp : 1<d.stage.f → ActivePrefixStageRuntimeData.Packed d D) (length : ℕ) :=
  (T+12*ActivePrefixStageRuntimeProgram.count+5)*ActivePrefixStageRuntimeData.cost D d hp +
    6*(∑ j : Fin ActivePrefixStageRuntimeProgram.count,
      (compactRawWords (K:=prime+K) d (fun _ => false) j).length) +
    16*length+2*T+6*ActivePrefixStageRuntimeProgram.count+35

/-- Codecs surround the entire native runtime, rather than its internal swaps. -/
def compactSlotXorProg (hQ : compactRuntimeStates ≤ Q)
    (ι : Fin ActivePrefixStageRuntimeProgram.count → Fin T) (hι : Function.Injective ι)
    (hT : ActivePrefixStageRuntimeProgram.count ≤ T) (str tmp : Fin T) : Pr F T Q (prime+K) U :=
  .seq (toBitsPass str tmp)
    (.seq (moveR tmp (ι compactRuntimeRaw) id)
      (.seq (compactRuntimeProg hQ ι hι hT)
        (.seq (moveR (ι compactRuntimeRaw) tmp id) (ofBitsPass tmp str))))

/-- Codec composition with the actual native runtime. The two list equalities are
serialization witnesses; the final live-array theorem discharges them canonically. -/
theorem compactSlotXor_codec_exec (body : F → Pr F T Q (prime+K) U)
    (hQ : compactRuntimeStates ≤ Q)
    (ι : Fin ActivePrefixStageRuntimeProgram.count → Fin T) (hι : Function.Injective ι)
    (hT : ActivePrefixStageRuntimeProgram.count ≤ T)
    (str tmp : Fin T) (hst : str ≠ tmp) (hstr : ∀ j, ι j ≠ str) (htmp : ∀ j, ι j ≠ tmp)
    (D : ℕ) (d : Inputs s) (x : Array s d.rows)
    (hp : 1<d.stage.f → ActivePrefixStageRuntimeData.Packed d D)
    (w w' : List (Fin (prime+K+4)))
    (hin : List.ofFn (fun j => bitSymbol (x j)) = toBits w)
    (hout : List.ofFn (fun j => bitSymbol (ActivePrefixStageRuntimeData.result d x j)) = toBits w')
    (h8 : ∀ z ∈ w', z.val < 8)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hL : ∀ j, S.L (ι j)=[]) (hR : S.R str=w) (htmp0 : S.R tmp=[])
    (hpay0 : S.R (ι compactRuntimeRaw)=[])
    (hhdr : ∀ j, j≠compactRuntimeRaw → S.R (ι j)=compactRawWords d x j) :
    ∃ v' m, v'.user=v.user ∧
      m ≤ (T+12*ActivePrefixStageRuntimeProgram.count+5)*(ActivePrefixStageRuntimeData.cost D d hp) +
        6*(∑ j : Fin ActivePrefixStageRuntimeProgram.count,
          (compactRawWords (K:=prime+K) d x j).length) + 16*w.length+2*T+6*ActivePrefixStageRuntimeProgram.count+35 ∧
      Exec body (compactSlotXorProg hQ ι hι hT str tmp) (mk v S) m
        (mk v' { S with R := Function.update S.R str w' }) := by
  let pr := ι compactRuntimeRaw
  have hpay_str : pr ≠ str := hstr _
  have hpay_tmp : pr ≠ tmp := htmp _
  have hpr0 : S.R pr=[] := hpay0
  have hwlen : w'.length=w.length := by
    have hi := congrArg List.length hin
    have ho := congrArg List.length hout
    simp only [List.length_ofFn,length_toBits] at hi ho
    omega
  obtain ⟨v₁,hu₁,he₁⟩ := toBitsPass_exec body str tmp hst v S
  set S₁ : Stacks T (prime+K) := {S with R:=pushedR S.R str tmp (toBits (S.R str)).reverse} with hS₁
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body tmp pr hpay_tmp.symm id v₁ S₁
  set S₂ : Stacks T (prime+K) := {S₁ with R:=movedR S₁.R tmp pr id (S₁.R tmp)} with hS₂
  have hS₁tmp : S₁.R tmp=(toBits w).reverse := by
    simp only [hS₁,pushedR,Function.update_self,hR,htmp0,List.append_nil]
  have hS₁pr : S₁.R pr=[] := by
    simp only [hS₁,pushedR,Function.update_of_ne hpay_tmp,Function.update_of_ne hpay_str,hpr0]
  have hS₂pr : S₂.R pr=toBits w := by
    simp only [hS₂,movedR,Function.update_self,hS₁tmp,hS₁pr,List.map_id,List.reverse_reverse,List.append_nil]
  have hS₂oth : ∀ z,z≠pr → z≠str → z≠tmp → S₂.R z=S.R z := by
    intro z h₁ h₂ h₃
    simp [hS₂,movedR,hS₁,pushedR,h₁,h₂,h₃]
  have hS₂str : S₂.R str=[] := by simp [hS₂,movedR,hS₁,pushedR,hst,Ne.symm hpay_str]
  have hS₂tmp : S₂.R tmp=[] := by simp [hS₂,movedR,hS₁,pushedR,Ne.symm hpay_tmp]
  have hbank : ∀ j,S₂.R (ι j)=compactRawWords d x j := by
    intro j
    by_cases hj : j=compactRuntimeRaw
    · subst j
      rw [←show pr=ι compactRuntimeRaw from rfl,hS₂pr,compactRawWords_raw,hin]
    · rw [hS₂oth _ (fun h => hj (hι h)) (hstr j) (htmp j),hhdr j hj]
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := compactRuntime_exec_update body hQ ι hι hT D d x hp v₂ S₂ hL hbank
  set S₃ : Stacks T (prime+K) := {S₂ with R:=Function.update S₂.R pr (List.ofFn (fun j => bitSymbol (ActivePrefixStageRuntimeData.result d x j)))} with hS₃
  have hS₃pr : S₃.R pr=toBits w' := by simp only [hS₃,Function.update_self,hout]
  obtain ⟨v₄,hu₄,he₄⟩ := moveR_exec body pr tmp hpay_tmp id v₃ S₃
  set S₄ : Stacks T (prime+K) := {S₃ with R:=movedR S₃.R pr tmp id (S₃.R pr)} with hS₄
  have hS₃tmp : S₃.R tmp=[] := by simp only [hS₃,Function.update_of_ne (Ne.symm hpay_tmp),hS₂tmp]
  have hS₄tmp : S₄.R tmp=(toBits w').reverse := by
    simp only [hS₄,movedR,Function.update_self,hS₃pr,hS₃tmp,List.map_id,List.append_nil]
  obtain ⟨v₅,hu₅,he₅⟩ := ofBitsPass_exec body tmp str hst.symm w' h8 v₄ S₄ hS₄tmp
  refine ⟨v₅,_,hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))) rfl ?_⟩
  · rw [hR,hS₁tmp,List.length_reverse,length_toBits,hS₃pr,length_toBits,hwlen]
    omega
  · congr 1
    refine Stacks.ext rfl rfl rfl ?_
    funext z
    by_cases hzs : z=str
    · subst z
      simp [pushedR,hst,hS₄,movedR,hS₃,Ne.symm hpay_str,hS₂str]
    · by_cases hzt : z=tmp
      · subst z
        simp [pushedR,hzs,htmp0]
      · by_cases hzp : z=pr
        · subst z
          simp [pushedR,hzs,hzt,hS₄,movedR,hpr0]
        · simp [pushedR,hzs,hzt,hzp,hS₄,movedR,hS₃,hS₂oth z hzp hzs hzt]


open IntegerMultBounds.MathlibTM2.Layer in
/-- Actual encoded live slot-XOR execution, with canonical native headers supplied.
No caller execution, array-action, or permutation premise is required. -/
theorem compactSlotXor_exec {n a₀ k ρ left right rows R r w : ℕ}
    (body : F → Pr F T Q (prime+K) U)
    (hQ : compactRuntimeStates ≤ Q)
    (ι : Fin ActivePrefixStageRuntimeProgram.count → Fin T) (hι : Function.Injective ι)
    (hT : ActivePrefixStageRuntimeProgram.count ≤ T)
    (str tmp : Fin T) (hst : str ≠ tmp) (hstr : ∀ j,ι j≠str) (htmp : ∀ j,ι j≠tmp)
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x y : Fin m) (hxy : x≠y)
    (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (hr : 0<rows) (hrecord : s.bits+1≤s.payload)
    (hA : 4≤prime+K) (hpayload : s.payload=3*(r*w))
    (hvolume : rows*s.recordWidth=(R*2^n)*s.payload)
    (D : ℕ)
    (hp : 1<k → ActivePrefixStageRuntimeData.Packed
      (compactRecursiveInputs layout x y hxy rows hG hGK hr hrecord) D)
    (Z : ZArr (Fin R × Fin r) n)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hL : ∀ j,S.L (ι j)=[]) (hR : S.R str=encZ (prime+K) w Z)
    (htmp0 : S.R tmp=[]) (hpay0 : S.R (ι compactRuntimeRaw)=[])
    (hhdr : ∀ j,j≠compactRuntimeRaw → S.R (ι j)=compactRawWords
      (compactRecursiveInputs layout x y hxy rows hG hGK hr hrecord) (fun _ => false) j) :
    ∃ v' steps,v'.user=v.user ∧
      steps ≤ compactSlotXorCost T K D (compactRecursiveInputs layout x y hxy rows hG hGK hr hrecord) hp
        (encZ (prime+K) w Z).length ∧
      Exec body (compactSlotXorProg hQ ι hι hT str tmp) (mk v S) steps
        (mk v' {S with R:=Function.update S.R str (encZ (prime+K) w (pullM (compactRecursiveBits layout) (sxXorCol x y) Z))}) := by
  let d := compactRecursiveInputs layout x y hxy rows hG hGK hr hrecord
  obtain ⟨array,hin⟩ := compactEncoding_exists (s:=s) hA Z (hvolume.trans (by rw [hpayload]))
  have hout := compactEncoding_runtime_result layout x y hxy hG hGK hr hrecord hA hpayload hvolume Z array hin
  have h8 : ∀ z ∈ encZ (prime+K) w (pullM (compactRecursiveBits layout) (sxXorCol x y) Z), z.val<8 := by
    rw [sx_encZ_eq_flatten]
    intro z hz
    obtain ⟨rec,hrec,hz⟩ := List.mem_flatten.mp hz
    exact (sx_recSyms_facts hA _).2.2 rec hrec z hz
  obtain ⟨v',steps,hu,hm,he⟩ := compactSlotXor_codec_exec body hQ ι hι hT str tmp hst hstr htmp
    D d array hp _ _ hin hout h8 v S hL hR htmp0 hpay0
    (fun j hj => (hhdr j hj).trans (compactRawWords_other d _ array j hj))
  refine ⟨v',steps,hu,?_,he⟩
  have hs : (∑ j : Fin ActivePrefixStageRuntimeProgram.count,
      (compactRawWords (K:=prime+K) d array j).length) =
      ∑ j : Fin ActivePrefixStageRuntimeProgram.count,(compactRawWords (K:=prime+K) d (fun _ => false) j).length :=
    Finset.sum_congr rfl (fun j _ => compactRawWords_length d _ _ j)
  rw [hs] at hm
  exact hm

end
end IntegerMultBounds.MathlibTM2.Node
