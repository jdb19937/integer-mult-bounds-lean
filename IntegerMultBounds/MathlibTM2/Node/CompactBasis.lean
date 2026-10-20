module

public import IntegerMultBounds.MathlibTM2.Node.CompactBasisSlot
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import IntegerMultBounds.MathlibTM2.Node.Basis

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

/-- The step bound of the slot operation with target `y`. -/
def compactBasisTargetCost {n a₀ k ρ left right rowCount : ℕ}
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x : Fin m) (_hG : 1 ≤ s.guard)
    (_hGK : s.guard+1 ≤ s.chunk) (_hr : 0<rowCount) (_hrecord : s.bits+1 ≤ s.payload) (D : ℕ)
    (_hp : CompactSlotPacked s k (2^(n-s.bits)*rowCount) D) (T _K o r w : ℕ) (y : Fin m) : ℕ :=
  if x≠y then compactBasisSlotCost T D layout rowCount o r w else 0

section Basis
variable {n a₀ k ρ left right o rowCount r w : ℕ}
variable (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x : Fin m)
variable (hG : 1 ≤ s.guard) (hGK : s.guard+1 ≤ s.chunk) (hr : 0<rowCount)
variable (hrecord : s.bits+1 ≤ s.payload) (D : ℕ)
variable (hp : CompactSlotPacked s k (2^(n-s.bits)*rowCount) D)


variable (body : P → Pr P T Q (prime+K) U) (hQ : compactRuntimeStates ≤ Q)
    (ι : CxSlotReg → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (e : Fin 30 → Fin T) (he : Function.Injective e) (ell str : Fin T)
    (hell : ∀ i,ell≠e i) (hellstr : ell≠str) (hebank : ∀ i j,e i≠ι j)
    (hestr : ∀ i,e i≠str) (hellι : ∀ j,ell≠ι j) (hstr : ∀ j,ι j≠str)
    (hA : 4 ≤ prime+K) (hpayload : s.payload=2^o*(3*(r*w)))

include he hell hellstr hebank hestr hellι hA hpayload hp

/-- Every step is the concrete computed-slot program, with no execution premise. -/
theorem compactBasisList_exec :
    ∀ (l : List (Fin m)), (∀ y ∈ l,y≠x) →
    ∀ (Z : ZArr (Fin rowCount × Fin r) (o+n))
      (v : HS T Q (prime+K) U) (S : Stacks T (prime+K)),
    (∀ j,S.L j=[]) → (∀ j,S.R (ι j)=[]) →
    (S.R ell).length=s.chunk*k → S.R str=encZ (prime+K) w Z →
    (∀ i : Fin 16,i≠0 → i≠11 → i≠12 →
      (S.R (e (Fin.castAdd 14 i))).length=compactDescriptorBankInputs layout o rowCount r w x x i) →
    ∃ v' steps,v'.user=v.user ∧
      steps ≤ (l.map (compactBasisTargetCost layout x hG hGK hr hrecord D hp T K o r w)).sum+1 ∧
      Exec body (Prog.seqList (l.map (compactBasisSlotProg (str := str) hQ hι hstr hT e ell x)))
        (mk v S) steps (mk v' {S with R:=Function.update S.R str (encZ (prime+K) w
          (pullM (compactOffsetEmbedding o (compactRecursiveBits layout)) (basisFold x l) Z))})
  | [], _, Z, v, S, _, _, _, hR, _ => by
    refine ⟨v,1,rfl,by simp,Exec.cast (Exec.act (body:=body) .done (mk v S)) rfl ?_⟩
    have hid : basisFold x []=id := rfl
    rw [run_done,hid,basis_pullM_id,←hR,Function.update_eq_self]
  | y::l, hl, Z, v, S, hL, hbank, hellen, hR, hin => by
    have hxy : x≠y := (hl y List.mem_cons_self).symm
    obtain ⟨v₁,c₁,hu₁,hc₁,he₁⟩ := compactBasisSlot_exec body hQ hι hT e he ell
      hell hebank hestr hellι hellstr hstr layout x y hxy hG hr hA hpayload D
      hp Z v S hL hbank hellen hR
      (by intro i hi0 hi11 hi12; rw [compactBasis_inputs_target layout o rowCount r w x y x i hi12]; exact hin i hi0 hi11 hi12)
    let E := compactOffsetEmbedding o (compactRecursiveBits layout)
    let Z₁ := pullM E (sxXorCol x y) Z
    obtain ⟨v₂,c₂,hu₂,hc₂,he₂⟩ := compactBasisList_exec l
      (fun z hz => hl z (List.mem_cons_of_mem _ hz)) Z₁ v₁
      {S with R:=Function.update S.R str (encZ (prime+K) w Z₁)} hL
      (fun j => by simpa only [Function.update_of_ne (hstr j)] using hbank j)
      (by simpa only [Function.update_of_ne hellstr] using hellen) (by simp)
      (by intro i hi0 hi11 hi12; simpa only [Function.update_of_ne (hestr _)] using hin i hi0 hi11 hi12)
    have hfold : pullM E (basisFold x l) Z₁=pullM E (basisFold x (y::l)) Z := by
      rw [show Z₁=pullM E (sxXorCol x y) Z from rfl,
        basis_pullM_pullM (compactOffsetEmbedding_injective o (compactRecursiveBits_injective layout))]
      rfl
    have hc₁' : c₁ ≤ compactBasisTargetCost layout x hG hGK hr hrecord D hp T K o r w y := by
      simpa only [compactBasisTargetCost,hxy,ne_eq,not_false_eq_true,↓reduceIte] using hc₁
    refine ⟨v₂,c₁+c₂,hu₂.trans hu₁,?_,Exec.cast (Exec.seq he₁ he₂) rfl ?_⟩
    · simp only [List.map_cons,List.sum_cons]
      omega
    · rw [Function.update_idem,hfold]

omit he hell hellstr hebank hestr hellι hA hpayload hp in
def compactBasisProg (vv : BinaryWalsh.Address m) : Pr P T Q (prime+K) U :=
  Prog.seqList ((basisTargets vv x).map (compactBasisSlotProg (str := str) hQ hι hstr hT e ell x))

/-- Exact-frame basisW-style result from the actual finite list of compact slot operations. -/
theorem compactBasis_exec (vv : BinaryWalsh.Address m) (hv : vv x=1)
    (Z : ZArr (Fin rowCount × Fin r) (o+n)) (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hL : ∀ j,S.L j=[]) (hbank : ∀ j,S.R (ι j)=[])
    (hellen : (S.R ell).length=s.chunk*k) (hR : S.R str=encZ (prime+K) w Z)
    (hin : ∀ i : Fin 16,i≠0 → i≠11 → i≠12 →
      (S.R (e (Fin.castAdd 14 i))).length=compactDescriptorBankInputs layout o rowCount r w x x i) :
    ∃ v' steps,v'.user=v.user ∧
      steps ≤ ((basisTargets vv x).map (compactBasisTargetCost layout x hG hGK hr hrecord D hp T K o r w)).sum+1 ∧
      Exec body (compactBasisProg x hQ ι hι hT e ell str hstr vv) (mk v S) steps
        (mk v' {S with R:=Function.update S.R str (encZ (prime+K) w
          (pullM (compactOffsetEmbedding o (compactRecursiveBits layout)) (basisMap vv x) Z))}) := by
  obtain ⟨v',steps,hu,hc,hex⟩ := compactBasisList_exec layout x hG hGK hr hrecord D hp body hQ ι hι hT
    e he ell str hell hellstr hebank hestr hellι hstr hA hpayload (basisTargets vv x)
    (fun y hy => (mem_basisTargets.mp hy).2) Z v S hL hbank hellen hR hin
  rw [basisFold_eq vv x hv] at hex
  exact ⟨v',steps,hu,hc,hex⟩
end Basis

end
end IntegerMultBounds.MathlibTM2.Node
