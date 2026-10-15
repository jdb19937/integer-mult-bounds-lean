module

public import IntegerMultBounds.MathlibTM2.Node.CompactHeaderBuild

/-! Explicit cleanup of the native original descriptor bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
noncomputable section
variable {T Q A H : ℕ} {U F : Type}

def compactHeadersClear (dst : Fin H → Fin T) : Pr F T Q A U :=
  Prog.seqList ((List.range H).map fun j =>
    if hj : j<H then uclear (dst ⟨j,hj⟩) else .act .done)

/-- Each descriptor is cleared once; source registers and every outside stack
are preserved. The cost includes each unary clear and sequencing overhead. -/
theorem compactHeadersClear_exec (body : F → Pr F T Q A U)
    (dst : Fin H → Fin T) (hd : Function.Injective dst)
    (v : HS T Q A U) (S : Stacks T A) :
    ∃ v' steps,v'.user=v.user ∧
      steps≤(∑ i : Fin H,(2*(S.R (dst i)).length+2))+1 ∧
      Exec body (compactHeadersClear dst) (mk v S) steps
        (mk v' {S with R:=compactHeaderFill dst (fun _ => []) H S.R}) := by
  let words : Fin H → List (Fin (A+4)) := fun _ => []
  let states := fun j => compactHeaderFill dst words j S.R
  let prog : ℕ → Pr F T Q A U := fun j =>
    if hj : j<H then uclear (dst ⟨j,hj⟩) else .act .done
  let cost := fun j => if hj : j<H then 2*(S.R (dst ⟨j,hj⟩)).length+2 else 0
  have hstep (j : ℕ) (hj : j<H) (v₀ : HS T Q A U) (S₀ : Stacks T A)
      (hS : S₀.R=states j) :
      ∃ v' steps,v'.user=v₀.user ∧ steps≤cost j ∧
        Exec body (prog j) (mk v₀ S₀) steps (mk v' {S₀ with R:=states (j+1)}) := by
    let i : Fin H := ⟨j,hj⟩
    have hs : S₀.R (dst i)=S.R (dst i) := by
      rw [hS]; dsimp only [states]
      rw [compactHeaderFill_at dst hd,ite_eq_right (by simp [i])]
    obtain ⟨v',hu,he⟩ := uclear_exec body (dst i) v₀ S₀
    refine ⟨v',2*(S₀.R (dst i)).length+2,hu,?_,?_⟩
    · simp only [cost,dite_eq_left hj,hs,i,le_refl]
    · dsimp only [prog]
      rw [dite_eq_left hj]
      apply Exec.cast he rfl
      congr 2
      change Function.update S₀.R (dst i) []=states (j+1)
      rw [hS]
      exact compactHeaderFill_succ dst hd words j hj S.R
  obtain ⟨v',steps,hu,hm,he⟩ := sx_chain_exec body states prog cost H 0
    (by intro j hj v₀ S₀ hS; simpa only [Nat.zero_add] using hstep j hj v₀ S₀ (by simpa using hS))
    v S (compactHeaderFill_zero dst words S.R).symm
  refine ⟨v',steps,hu,?_,?_⟩
  · simpa only [Nat.zero_add,Finset.sum_fin_eq_sum_range,cost] using hm
  · simpa only [Nat.zero_add,prog,states,words,compactHeadersClear] using he

end
end IntegerMultBounds.MathlibTM2.Node
