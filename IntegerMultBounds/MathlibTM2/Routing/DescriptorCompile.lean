module

public import IntegerMultBounds.MathlibTM2.Routing.DescriptorCompileLoop

/-! Compile a binary selector table and restore its input and all compiler scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

def descriptorCompileProgram {T Q A : ℕ} {P U : Type}
    (rg : BinaryMaskReg → Fin T) (src saved out : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR src)) (.seq (.loop (·.flag) (descriptorCompileLoopBody rg src saved out))
    (moveR saved src id))

theorem descriptorCompile_exec {T Q A M : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (rg : BinaryMaskReg → Fin T) (hrg : Function.Injective rg)
    (src saved out : Fin T) (hss : src ≠ saved) (hso : src ≠ out) (hao : saved ≠ out)
    (hsrc : ∀ r, src ≠ rg r) (hsaved : ∀ r, saved ≠ rg r) (hout : ∀ r, out ≠ rg r)
    (L : ℕ) (hM : M < 2 ^ L) (qs : List (Fin M))
    (v : HS T Q A U) (S : Stacks T A) (hready : DescriptorCompileReady rg S.R L M)
    (hinput : S.R src = descriptorSelectorFrames L qs) (hsave : S.R saved = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ qs.length * (descriptorCompileCallCost L M + 2) +
        2 * (descriptorSelectorFrames (A := A) L qs).length + 4 ∧
      Exec body (descriptorCompileProgram rg src saved out) (mk v S) m
        (mk v' { S with R := Function.update S.R out (descriptorRows qs.reverse ++ S.R out) }) := by
  let input := descriptorSelectorFrames (A := A) L qs
  let rows := descriptorRows (A := A) qs.reverse
  let v₁ := { v with flag := input.head?.isSome }
  have hp : (peekR src : Act T Q A U).run (mk v S) = mk v₁ S := by
    simp only [peekR_run, hinput]; rfl
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := descriptorCompileLoop_exec body rg hrg src saved out
    hss hso hao hsrc hsaved hout L hM qs v₁ S hready hinput rfl
  let S₂ : Stacks T A := { S with R := descriptorCompileLoopBank S.R src saved out input rows }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body saved src hss.symm id v₂ S₂
  have hs₂ : S₂.R saved = input.reverse := by
    simp [S₂, descriptorCompileLoopBank, hao, hsave]
  have hfinal : movedR S₂.R saved src id (S₂.R saved) =
      Function.update S.R out (rows ++ S.R out) := by
    rw [hs₂]
    funext j
    by_cases hj : j = src
    · subst j; simp [movedR, S₂, descriptorCompileLoopBank, hss, hso, hinput, input]
    · by_cases hk : j = saved
      · subst j; simp [movedR, hss.symm, hao, hsave]
      · by_cases ho : j = out
        · subst j; simp [movedR, S₂, descriptorCompileLoopBank, hj, hk]
        · simp [movedR, S₂, descriptorCompileLoopBank, hj, hk, ho]
  rw [hfinal, hs₂, List.length_reverse] at he₃
  exact ⟨v₃, 1 + (m₂ + (2 * input.length + 2)), hu₃.trans hu₂, by dsimp only [input]; omega,
    Exec.seq (hp ▸ Exec.act (body := body) (peekR src) (mk v S)) (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
