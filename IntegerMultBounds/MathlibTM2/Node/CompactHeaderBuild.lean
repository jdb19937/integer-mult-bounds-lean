module

public import IntegerMultBounds.MathlibTM2.Node.SlotXor
public import IntegerMultBounds.MathlibTM2.Host.SSMul

/-! Materialize the thirteen original native descriptors from runtime unary registers.
Every input register and scratch stack is restored; derived stage headers remain the
responsibility of the existing complete native runtime. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Host.SS
noncomputable section
variable {T Q A H : ℕ} {U F : Type}

/-- Canonical marked binary representation required by the native header bank. -/
def compactHeaderWord (A value : ℕ) : List (Fin (A+4)) :=
  separator :: (RecursiveChildQuotientsConstant.bits value).map bitSymbol

def compactHeaderStep (src dst t₁ t₂ : Fin T) : Pr F T Q A U :=
  .seq (sxBinConv src dst t₁ t₂) (.act (pushSym dst separator))

theorem compactHeaderStep_exec (body : F → Pr F T Q A U)
    (src dst t₁ t₂ : Fin T) (hdist : [src,dst,t₁,t₂].Nodup)
    (v : HS T Q A U) (S : Stacks T A)
    (hd : S.R dst=[]) (h₁ : S.R t₁=[]) (h₂ : S.R t₂=[]) :
    ∃ v' steps,v'.user=v.user ∧ steps≤16*(S.R src).length+5 ∧
      Exec body (compactHeaderStep src dst t₁ t₂) (mk v S) steps
        (mk v' {S with R:=Function.update S.R dst (compactHeaderWord A (S.R src).length)}) := by
  obtain ⟨v',steps,hu,hm,he⟩ := sxBinConv_exec body hdist v S hd h₁ h₂
  have hp := Exec.act (body:=body) (pushSym dst separator)
    (mk v' {S with R:=Function.update S.R dst ((sxBits (S.R src).length).map bitSymbol)})
  rw [pushSym_run] at hp
  refine ⟨v',steps+1,hu,by omega,Exec.cast (Exec.seq he hp) rfl ?_⟩
  congr 1
  simp only [Function.update_self,Function.update_idem]
  rw [compactHeaderWord,RecursiveChildQuotientsConstant.bits_eq_advance]
  rfl

/-- Prefix of a finite family of independent descriptor destinations. -/
def compactHeaderFill (dst : Fin H → Fin T) (words : Fin H → List (Fin (A+4)))
    (count : ℕ) (R : Fin T → List (Fin (A+4))) (z : Fin T) : List (Fin (A+4)) :=
  if h : ∃ i, dst i=z ∧ i.val<count then words h.choose else R z

lemma compactHeaderFill_at (dst : Fin H → Fin T) (hd : Function.Injective dst)
    (words : Fin H → List (Fin (A+4))) (count : ℕ) (R : Fin T → List (Fin (A+4))) (i : Fin H) :
    compactHeaderFill dst words count R (dst i)=if i.val<count then words i else R (dst i) := by
  unfold compactHeaderFill
  by_cases hi : i.val<count
  · have he : ∃ j,dst j=dst i ∧ j.val<count := ⟨i,rfl,hi⟩
    rw [dite_eq_left he,ite_eq_left hi,hd he.choose_spec.1]
  · have he : ¬∃ j,dst j=dst i ∧ j.val<count := by
      rintro ⟨j,hj,hlt⟩
      exact hi (hd hj ▸ hlt)
    rw [dite_eq_right he,ite_eq_right hi]

lemma compactHeaderFill_out (dst : Fin H → Fin T) (words : Fin H → List (Fin (A+4)))
    (count : ℕ) (R : Fin T → List (Fin (A+4))) (z : Fin T) (hz : ∀ i,dst i≠z) :
    compactHeaderFill dst words count R z=R z := by
  unfold compactHeaderFill
  rw [dite_eq_right (by rintro ⟨i,hi,_⟩; exact hz i hi)]

lemma compactHeaderFill_zero (dst : Fin H → Fin T) (words : Fin H → List (Fin (A+4)))
    (R : Fin T → List (Fin (A+4))) : compactHeaderFill dst words 0 R=R := by
  funext z
  simp [compactHeaderFill]

lemma compactHeaderFill_succ (dst : Fin H → Fin T) (hd : Function.Injective dst)
    (words : Fin H → List (Fin (A+4))) (count : ℕ) (hc : count<H)
    (R : Fin T → List (Fin (A+4))) :
    Function.update (compactHeaderFill dst words count R) (dst ⟨count,hc⟩) (words ⟨count,hc⟩) =
      compactHeaderFill dst words (count+1) R := by
  funext z
  by_cases hz : ∃ i,dst i=z
  · obtain ⟨i,rfl⟩ := hz
    by_cases hi : i=⟨count,hc⟩
    · subst i
      rw [Function.update_self,compactHeaderFill_at dst hd,ite_eq_left (by simp)]
    · rw [Function.update_of_ne (fun h => hi (hd h)),compactHeaderFill_at dst hd,compactHeaderFill_at dst hd]
      have hv : i.val≠count := fun h => hi (Fin.ext h)
      by_cases hlt : i.val<count
      · rw [ite_eq_left hlt,ite_eq_left (by omega)]
      · rw [ite_eq_right hlt,ite_eq_right (by omega)]
  · have ho : ∀ i,dst i≠z := by simpa using hz
    rw [Function.update_of_ne (Ne.symm (ho _)),compactHeaderFill_out dst words count R z ho,
      compactHeaderFill_out dst words (count+1) R z ho]

/-- Fixed finite program: only register locations are compiled, never their runtime values. -/
def compactHeadersBuild (src dst : Fin H → Fin T) (t₁ t₂ : Fin T) : Pr F T Q A U :=
  Prog.seqList ((List.range H).map fun j => if hj : j<H then compactHeaderStep (src ⟨j,hj⟩) (dst ⟨j,hj⟩) t₁ t₂ else .act .done)

/-- Complete conversion of a finite runtime header family with arbitrary outside frame. -/
theorem compactHeadersBuild_exec (body : F → Pr F T Q A U)
    (src dst : Fin H → Fin T) (hd : Function.Injective dst) (t₁ t₂ : Fin T)
    (hsrc : ∀ i j,src i≠dst j) (h₁src : ∀ i,src i≠t₁) (h₂src : ∀ i,src i≠t₂)
    (h₁dst : ∀ i,dst i≠t₁) (h₂dst : ∀ i,dst i≠t₂) (h₁₂ : t₁≠t₂)
    (v : HS T Q A U) (S : Stacks T A)
    (hempty : ∀ i,S.R (dst i)=[]) (h₁ : S.R t₁=[]) (h₂ : S.R t₂=[]) :
    ∃ v' steps,v'.user=v.user ∧
      steps≤(∑ i : Fin H,(16*(S.R (src i)).length+5))+1 ∧
      Exec body (compactHeadersBuild src dst t₁ t₂) (mk v S) steps
        (mk v' {S with R:=compactHeaderFill dst (fun i => compactHeaderWord A (S.R (src i)).length) H S.R}) := by
  let words := fun i => compactHeaderWord A (S.R (src i)).length
  let states := fun j => compactHeaderFill dst words j S.R
  let prog : ℕ → Pr F T Q A U := fun j => if hj : j<H then compactHeaderStep (src ⟨j,hj⟩) (dst ⟨j,hj⟩) t₁ t₂ else .act .done
  let cost := fun j => if hj : j<H then 16*(S.R (src ⟨j,hj⟩)).length+5 else 0
  have hstep (j : ℕ) (hj : j<H) (v₀ : HS T Q A U) (S₀ : Stacks T A) (hS : S₀.R=states j) :
      ∃ v' steps,v'.user=v₀.user ∧ steps≤cost j ∧
        Exec body (prog j) (mk v₀ S₀) steps (mk v' {S₀ with R:=states (j+1)}) := by
    let i : Fin H := ⟨j,hj⟩
    have hs : S₀.R (src i)=S.R (src i) := by
      rw [hS]; dsimp only [states]; rw [compactHeaderFill_out dst words j S.R _ (fun z => (hsrc i z).symm)]
    obtain ⟨v',steps,hu,hm,he⟩ := compactHeaderStep_exec body (src i) (dst i) t₁ t₂
      (by simp [hsrc,h₁src,h₂src,h₁dst,h₂dst,h₁₂]) v₀ S₀
      (by rw [hS]; dsimp only [states]; rw [compactHeaderFill_at dst hd,ite_eq_right (by simp [i]),hempty])
      (by rw [hS]; dsimp only [states]; rw [compactHeaderFill_out dst words j S.R t₁ h₁dst,h₁])
      (by rw [hS]; dsimp only [states]; rw [compactHeaderFill_out dst words j S.R t₂ h₂dst,h₂])
    refine ⟨v',steps,hu,?_,?_⟩
    · simpa only [cost,dite_eq_left hj,hs] using hm
    · dsimp only [prog]
      rw [dite_eq_left hj]
      apply Exec.cast he rfl
      congr 2
      change Function.update S₀.R (dst i) (compactHeaderWord A (S₀.R (src i)).length)=states (j+1)
      rw [hs,hS]
      exact compactHeaderFill_succ dst hd words j hj S.R
  obtain ⟨v',steps,hu,hm,he⟩ := sx_chain_exec body states prog cost H 0
    (by intro j hj v₀ S₀ hS; simpa only [Nat.zero_add] using hstep j hj v₀ S₀ (by simpa using hS))
    v S (compactHeaderFill_zero dst words S.R).symm
  refine ⟨v',steps,hu,?_,?_⟩
  · simpa only [Nat.zero_add,Finset.sum_fin_eq_sum_range,cost] using hm
  · simpa only [Nat.zero_add,prog,states,words,compactHeadersBuild] using he
end
end IntegerMultBounds.MathlibTM2.Node
