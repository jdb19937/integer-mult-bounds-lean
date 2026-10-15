module

public import IntegerMultBounds.MathlibTM2.Node.CompactBasisSlot
public import IntegerMultBounds.MathlibTM2.Node.Regs

/-! Concrete compact basis changes, with parent-length setup after factor saveDiv. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
noncomputable section
variable {s : Shape} {T Q K : ℕ} {U P : Type}

lemma compactBasis_stream_length {A R r n w : ℕ} (Z : ZArr (Fin R × Fin r) n) :
    (encZ A w Z).length=R*2^n*r*w := by
  rw [encZ,length_flatMap_const _ w (length_coeffSyms A w),length_coeffList]

lemma compactBasis_inputs_target {n a₀ k ρ left right : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right)
    (o R r w : ℕ) (x y z : Fin m) (i : Fin 16) (hi : i≠12) :
    compactDescriptorBankInputs layout o R r w x y i =
      compactDescriptorBankInputs layout o R r w x z i := by
  fin_cases i <;> simp_all [compactDescriptorBankInputs]

section Basis
variable {n a₀ k ρ left right o rowCount r w : ℕ}
variable (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x : Fin m)
variable (hG : 1 ≤ s.guard) (hGK : s.guard+1 ≤ s.chunk) (hr : 0<rowCount)
variable (hrecord : s.bits+1 ≤ s.payload) (D : ℕ)
variable (hp : ∀ y (hxy : x≠y),1<k → ActivePrefixStageRuntimeData.Packed
  (compactSlotComputedInputs layout x y hxy rowCount hG hGK hr hrecord) D)

def compactBasisTargetCost (T K o r w : ℕ) (y : Fin m) :=
  if hxy : x≠y then
    compactBasisSlotCost T K D
      (compactSlotComputedInputs layout x y hxy rowCount hG hGK hr hrecord) (hp y hxy)
      (compactDescriptorBankInputs layout o rowCount r w x y) (s.chunk*k)
      (rowCount*2^(o+n)*r*w) x y
  else 0

variable (body : P → Pr P T Q (prime+K) U) (hQ : compactRuntimeStates ≤ Q)
    (ι : Fin ActivePrefixStageRuntimeProgram.count → Fin T) (hι : Function.Injective ι)
    (hT : ActivePrefixStageRuntimeProgram.count ≤ T)
    (e : Fin 30 → Fin T) (he : Function.Injective e) (ell str tmp : Fin T)
    (hell : ∀ i,ell≠e i) (hellstr : ell≠str) (hebank : ∀ i j,e i≠ι j)
    (hestr : ∀ i,e i≠str) (hetmp : ∀ i,e i≠tmp)
    (hst : str≠tmp) (hstr : ∀ j,ι j≠str) (htmp : ∀ j,ι j≠tmp)
    (hA : 4 ≤ prime+K) (hpayload : s.payload=2^o*(3*(r*w)))

include he hell hellstr hebank hestr hetmp hst hstr htmp hA hpayload

/-- Every step is the concrete computed-slot program, with no execution premise. -/
theorem compactBasisList_exec :
    ∀ (l : List (Fin m)), (∀ y ∈ l,y≠x) →
    ∀ (Z : ZArr (Fin rowCount × Fin r) (o+n))
      (v : HS T Q (prime+K) U) (S : Stacks T (prime+K)),
    (∀ j,S.L j=[]) → (∀ j,S.R (ι j)=[]) →
    (∀ i : Fin 30, 16 ≤ i.val → S.R (e i)=[]) →
    (∀ i,S.R (compactBasisSeeds e i)=[]) →
    (S.R ell).length=s.chunk*k → S.R str=encZ (prime+K) w Z → S.R tmp=[] →
    (∀ i : Fin 16,i≠0 → i≠11 → i≠12 →
      (S.R (e (Fin.castAdd 14 i))).length=compactDescriptorBankInputs layout o rowCount r w x x i) →
    ∃ v' steps,v'.user=v.user ∧
      steps ≤ (l.map (compactBasisTargetCost layout x hG hGK hr hrecord D hp T K o r w)).sum+1 ∧
      Exec body (Prog.seqList (l.map (compactBasisSlotProg hQ ι hι hT e ell str tmp x)))
        (mk v S) steps (mk v' {S with R:=Function.update S.R str (encZ (prime+K) w
          (pullM (compactOffsetEmbedding o (compactRecursiveBits layout)) (basisFold x l) Z))})
  | [], _, Z, v, S, _, _, _, _, _, hR, _, _ => by
    refine ⟨v,1,rfl,by simp,Exec.cast (Exec.act (body:=body) .done (mk v S)) rfl ?_⟩
    have hid : basisFold x []=id := rfl
    rw [run_done,hid,basis_pullM_id,←hR,Function.update_eq_self]
  | y::l, hl, Z, v, S, hL, hbank, hz, hseed, hellen, hR, htmp0, hin => by
    have hxy : x≠y := (hl y List.mem_cons_self).symm
    obtain ⟨v₁,c₁,hu₁,hc₁,he₁⟩ := compactBasisSlot_exec body hQ ι hι hT e he ell str tmp
      hell hebank hestr hetmp hst hstr htmp layout x y hxy hG hGK hr hrecord hA hpayload D
      (hp y hxy) Z v S hL hbank hz hseed hellen hR htmp0
      (by intro i hi0 hi11 hi12; rw [compactBasis_inputs_target layout o rowCount r w x y x i hi12]; exact hin i hi0 hi11 hi12)
    let E := compactOffsetEmbedding o (compactRecursiveBits layout)
    let Z₁ := pullM E (sxXorCol x y) Z
    obtain ⟨v₂,c₂,hu₂,hc₂,he₂⟩ := compactBasisList_exec l
      (fun z hz => hl z (List.mem_cons_of_mem _ hz)) Z₁ v₁
      {S with R:=Function.update S.R str (encZ (prime+K) w Z₁)} hL
      (fun j => by simpa only [Function.update_of_ne (hstr j)] using hbank j)
      (fun i hi => by simpa only [Function.update_of_ne (hestr i)] using hz i hi)
      (fun i => by simpa only [Function.update_of_ne (show compactBasisSeeds e i≠str from hestr _)] using hseed i)
      (by simpa only [Function.update_of_ne hellstr] using hellen) (by simp)
      (by simpa only [Function.update_of_ne hst.symm] using htmp0)
      (by intro i hi0 hi11 hi12; simpa only [Function.update_of_ne (hestr _)] using hin i hi0 hi11 hi12)
    have hfold : pullM E (basisFold x l) Z₁=pullM E (basisFold x (y::l)) Z := by
      rw [show Z₁=pullM E (sxXorCol x y) Z from rfl,
        basis_pullM_pullM (compactOffsetEmbedding_injective o (compactRecursiveBits_injective layout))]
      rfl
    have hc₁' : c₁ ≤ compactBasisTargetCost layout x hG hGK hr hrecord D hp T K o r w y := by
      simpa only [compactBasisTargetCost,dite_eq_left hxy,compactBasis_stream_length] using hc₁
    refine ⟨v₂,c₁+c₂,hu₂.trans hu₁,?_,Exec.cast (Exec.seq he₁ he₂) rfl ?_⟩
    · simp only [List.map_cons,List.sum_cons]
      omega
    · rw [Function.update_idem,hfold]

def compactBasisProg (vv : BinaryWalsh.Address m) : Pr P T Q (prime+K) U :=
  Prog.seqList ((basisTargets vv x).map (compactBasisSlotProg hQ ι hι hT e ell str tmp x))

/-- Exact-frame basisW-style result from the actual finite list of compact slot operations. -/
theorem compactBasis_exec (vv : BinaryWalsh.Address m) (hv : vv x=1)
    (Z : ZArr (Fin rowCount × Fin r) (o+n)) (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hL : ∀ j,S.L j=[]) (hbank : ∀ j,S.R (ι j)=[])
    (hz : ∀ i : Fin 30,16 ≤ i.val → S.R (e i)=[]) (hseed : ∀ i,S.R (compactBasisSeeds e i)=[])
    (hellen : (S.R ell).length=s.chunk*k) (hR : S.R str=encZ (prime+K) w Z) (htmp0 : S.R tmp=[])
    (hin : ∀ i : Fin 16,i≠0 → i≠11 → i≠12 →
      (S.R (e (Fin.castAdd 14 i))).length=compactDescriptorBankInputs layout o rowCount r w x x i) :
    ∃ v' steps,v'.user=v.user ∧
      steps ≤ ((basisTargets vv x).map (compactBasisTargetCost layout x hG hGK hr hrecord D hp T K o r w)).sum+1 ∧
      Exec body (compactBasisProg x hQ ι hι hT e ell str tmp vv) (mk v S) steps
        (mk v' {S with R:=Function.update S.R str (encZ (prime+K) w
          (pullM (compactOffsetEmbedding o (compactRecursiveBits layout)) (basisMap vv x) Z))}) := by
  obtain ⟨v',steps,hu,hc,hex⟩ := compactBasisList_exec layout x hG hGK hr hrecord D hp body hQ ι hι hT
    e he ell str tmp hell hellstr hebank hestr hetmp hst hstr htmp hA hpayload (basisTargets vv x)
    (fun y hy => (mem_basisTargets.mp hy).2) Z v S hL hbank hz hseed hellen hR htmp0 hin
  rw [basisFold_eq vv x hv] at hex
  exact ⟨v',steps,hu,hc,hex⟩
end Basis

end
end IntegerMultBounds.MathlibTM2.Node
