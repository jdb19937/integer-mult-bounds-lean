module

public import IntegerMultBounds.MathlibTM2.Node.CompactSlotComputed
public import IntegerMultBounds.MathlibTM2.Node.Basis

/-! A slot operation at the post-saveDiv boundary: construct parent length from
the child length, seed the two fixed slot indices, and restore all three counters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
noncomputable section
variable {s : Shape} {T Q K : ℕ} {U P : Type}

def compactBasisSeeds (e : Fin 30 → Fin T) : Fin 3 → Fin T := fun i => e (![0,11,12] i)

lemma compactBasisSeeds_injective (e : Fin 30 → Fin T) (he : Function.Injective e) :
    Function.Injective (compactBasisSeeds e) := he.comp (by decide)

def compactBasisSeedState {A : ℕ} (e : Fin 30 → Fin T)
    (R : Fin T → List (Fin (A+4))) (L : ℕ) (x y : Fin m) :=
  Function.update (Function.update (Function.update R (e 0) (List.replicate (m*L) tick))
    (e 11) (List.replicate x.val tick)) (e 12) (List.replicate y.val tick)

def compactBasisSeed (e : Fin 30 → Fin T) (ell : Fin T) (x y : Fin m) : Pr P T Q A U :=
  .seq (umul m ell (e 0) (e 27)) <|
  .seq (compactDescriptorConst x.val (e 11)) (compactDescriptorConst y.val (e 12))

lemma compactBasisSeed_runs {A : ℕ} (body : P → Pr P T Q A U)
    (e : Fin 30 → Fin T) (he : Function.Injective e) (ell : Fin T) (hell : ∀ i,ell≠e i)
    (x y : Fin m) (R : Fin T → List (Fin (A+4)))
    (h0 : R (e 0)=[]) (h11 : R (e 11)=[]) (h12 : R (e 12)=[]) (h27 : R (e 27)=[]) :
    LayRuns body (compactBasisSeed e ell x y) R (compactBasisSeedState e R (R ell).length x y)
      (4*(R ell).length+6) := by
  refine lr_weaken body
    ((lr_umul body m (a:=ell) (b:=e 0) (t:=e 27) (hell _) (hell _) (he.ne (by decide)) h27).seq <|
    (compactDescriptorConst_runs body x.val (e 11) _).seq <|
    compactDescriptorConst_runs body y.val (e 12) _) ?_ ?_
  · simp [compactBasisSeedState,he.eq_iff,h0,h11,h12]
  · omega

lemma compactBasisSeed_clear {A : ℕ} (e : Fin 30 → Fin T) (he : Function.Injective e)
    (R : Fin T → List (Fin (A+4))) (L : ℕ) (x y : Fin m) (str : Fin T)
    (out : List (Fin (A+4))) (hs : ∀ i,e i≠str)
    (hz : ∀ i,R (compactBasisSeeds e i)=[]) :
    compactHeaderFill (compactBasisSeeds e) (fun _ => []) 3
      (Function.update (compactBasisSeedState e R L x y) str out)=Function.update R str out := by
  funext z
  by_cases hm : ∃ i,compactBasisSeeds e i=z
  · obtain ⟨i,rfl⟩ := hm
    rw [compactHeaderFill_at _ (compactBasisSeeds_injective e he),ite_eq_left i.isLt,
      Function.update_of_ne (show compactBasisSeeds e i≠str from hs _),hz]
  · have ho : ∀ i,compactBasisSeeds e i≠z := by simpa using hm
    rw [compactHeaderFill_out _ _ _ _ _ ho]
    by_cases hzs : z=str
    · subst z; simp only [Function.update_self]
    · rw [Function.update_of_ne hzs,Function.update_of_ne hzs]
      have h0 : z≠e 0 := (ho 0).symm
      have h11 : z≠e 11 := (ho 1).symm
      have h12 : z≠e 12 := (ho 2).symm
      simp [compactBasisSeedState,Function.update_of_ne,h0,h11,h12]

def compactBasisSlotProg (hQ : compactRuntimeStates ≤ Q)
    (ι : Fin ActivePrefixStageRuntimeProgram.count → Fin T) (hι : Function.Injective ι)
    (hT : ActivePrefixStageRuntimeProgram.count ≤ T) (e : Fin 30 → Fin T)
    (ell str tmp : Fin T) (x y : Fin m) : Pr P T Q (prime+K) U :=
  .seq (compactBasisSeed e ell x y) <|
  .seq (compactSlotComputedProg hQ ι hι hT e str tmp) (compactHeadersClear (compactBasisSeeds e))

def compactBasisSlotCost (T K D : ℕ) (d : ActivePrefixStageFullData.Inputs s)
    (hp : 1<d.stage.f → ActivePrefixStageRuntimeData.Packed d D)
    (input : Fin 16 → ℕ) (L length : ℕ) (x y : Fin m) :=
  (4*L+6)+compactSlotComputedCost T K D d hp input length+
    ((2*(m*L)+2)+(2*x.val+2)+(2*y.val+2)+1)

theorem compactBasisSlot_exec {n a₀ k ρ left right o rowCount r w : ℕ}
    (body : P → Pr P T Q (prime+K) U) (hQ : compactRuntimeStates ≤ Q)
    (ι : Fin ActivePrefixStageRuntimeProgram.count → Fin T) (hι : Function.Injective ι)
    (hT : ActivePrefixStageRuntimeProgram.count ≤ T)
    (e : Fin 30 → Fin T) (he : Function.Injective e) (ell str tmp : Fin T)
    (hell : ∀ i,ell≠e i) (hebank : ∀ i j,e i≠ι j)
    (hestr : ∀ i,e i≠str) (hetmp : ∀ i,e i≠tmp)
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
    (hseed : ∀ i,S.R (compactBasisSeeds e i)=[])
    (hellen : (S.R ell).length=s.chunk*k)
    (hR : S.R str=encZ (prime+K) w Z) (htmp0 : S.R tmp=[])
    (hin : ∀ i : Fin 16,i≠0 → i≠11 → i≠12 →
      (S.R (e (Fin.castAdd 14 i))).length=compactDescriptorBankInputs layout o rowCount r w x y i) :
    ∃ v' steps,v'.user=v.user ∧
      steps ≤ compactBasisSlotCost T K D
        (compactSlotComputedInputs layout x y hxy rowCount hG hGK hr hrecord) hp
        (compactDescriptorBankInputs layout o rowCount r w x y) (s.chunk*k)
        (encZ (prime+K) w Z).length x y ∧
      Exec body (compactBasisSlotProg hQ ι hι hT e ell str tmp x y) (mk v S) steps
        (mk v' {S with R:=Function.update S.R str (encZ (prime+K) w
          (pullM (compactOffsetEmbedding o (compactRecursiveBits layout)) (sxXorCol x y) Z))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := compactBasisSeed_runs body e he ell hell x y S.R
    (hseed 0) (hseed 1) (hseed 2) (hz 27 (by decide)) v S hL rfl
  let S₁ : Stacks T (prime+K) := {S with R:=compactBasisSeedState e S.R (S.R ell).length x y}
  have hframe (z : Fin T) (h0 : z≠e 0) (h11 : z≠e 11) (h12 : z≠e 12) : S₁.R z=S.R z := by
    simp [S₁,compactBasisSeedState,Function.update_of_ne,h0,h11,h12]
  have hin' : ∀ i : Fin 16,(S₁.R (e (Fin.castAdd 14 i))).length=
      compactDescriptorBankInputs layout o rowCount r w x y i := by
    intro i
    by_cases hi0 : i=0
    · subst i; simp [S₁,compactBasisSeedState,he.eq_iff,hellen,compactDescriptorBankInputs]; ring
    by_cases hi11 : i=11
    · subst i; simp [S₁,compactBasisSeedState,he.eq_iff,compactDescriptorBankInputs]
    by_cases hi12 : i=12
    · subst i; simp [S₁,compactBasisSeedState,compactDescriptorBankInputs]
    rw [hframe _ (he.ne (by intro h; exact hi0 (Fin.ext (congrArg (fun z : Fin 30 => z.val) h)))) (he.ne (by intro h; exact hi11 (Fin.ext (congrArg (fun z : Fin 30 => z.val) h))))
      (he.ne (by intro h; exact hi12 (Fin.ext (congrArg (fun z : Fin 30 => z.val) h))))]
    exact hin i hi0 hi11 hi12
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := compactSlotComputed_exec body hQ ι hι hT e he str tmp
    hebank hestr hetmp hst hstr htmp layout x y hxy hG hGK hr hrecord hA hpayload D hp Z v₁ S₁ hL
    (fun j => (hframe _ (hebank 0 j).symm (hebank 11 j).symm (hebank 12 j).symm).trans (hbank j))
    (by intro i hi; rw [hframe _ (he.ne (by intro h; subst i; simp at hi))
          (he.ne (by intro h; subst i; simp at hi)) (he.ne (by intro h; subst i; simp at hi))]; exact hz i hi)
    ((hframe _ (hestr 0).symm (hestr 11).symm (hestr 12).symm).trans hR)
    ((hframe _ (hetmp 0).symm (hetmp 11).symm (hetmp 12).symm).trans htmp0) hin'
  let output := encZ (prime+K) w
    (pullM (compactOffsetEmbedding o (compactRecursiveBits layout)) (sxXorCol x y) Z)
  let S₂ : Stacks T (prime+K) := {S₁ with R:=Function.update S₁.R str output}
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := compactHeadersClear_exec body (compactBasisSeeds e)
    (compactBasisSeeds_injective e he) v₂ S₂
  have hclear : m₃ ≤ (2*(m*(s.chunk*k))+2)+(2*x.val+2)+(2*y.val+2)+1 := by
    simpa [S₂,S₁,compactBasisSeeds,compactBasisSeedState,Fin.sum_univ_succ,he.eq_iff,
      Function.update_of_ne,hestr,hellen,Nat.add_assoc] using hm₃
  rw [hellen] at hm₁
  refine ⟨v₃,m₁+(m₂+m₃),hu₃.trans (hu₂.trans hu₁),?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) rfl ?_⟩
  · unfold compactBasisSlotCost
    omega
  · congr 1
    refine Stacks.ext rfl rfl rfl ?_
    exact compactBasisSeed_clear e he S.R (S.R ell).length x y str output hestr hseed

end
end IntegerMultBounds.MathlibTM2.Node
