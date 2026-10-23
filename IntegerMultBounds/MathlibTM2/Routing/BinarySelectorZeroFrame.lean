module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryZeroField

/-! Construct an absent-selector frame from its binary width. No prepared zero
word is supplied. Binary inputs and scratch are restored, with all work charged. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def binarySelectorZeroFrameProgram (rg : BinaryZeroReg → Fin T) : Pr P T Q A U :=
  .seq (.act (.push (.rt (rg .dst)) (fun _ => separator) .done)) (binaryZeroFieldProgram rg)

theorem binarySelectorZeroFrame_exec (body : P → Pr P T Q A U)
    (rg : BinaryZeroReg → Fin T) (hrg : Function.Injective rg)
    (Lw L : ℕ) (hL : L < 2 ^ Lw) (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg .width) = binSyms Lw L) (hunary : S.R (rg .unary) = [])
    (hscratch : ∀ i, S.R (rg (.scratch i)) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ Lw * (4 * L + 11) + 8 * L + 13 ∧
      Exec body (binarySelectorZeroFrameProgram rg) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg .dst) (binSyms L 0 ++ separator :: S.R (rg .dst)) }) := by
  let S₁ : Stacks T A := { S with R := Function.update S.R (rg .dst) (separator :: S.R (rg .dst)) }
  have hp : (Action.push (.rt (rg .dst)) (fun _ => separator) .done : Act T Q A U).run (mk v S) =
      mk v S₁ := by simp [Action.run, update_rt, S₁]
  obtain ⟨v', steps, hu, ht, he⟩ := binaryZeroField_exec body rg hrg Lw L hL v S₁
    (by simp [S₁, hrg.eq_iff, hwidth])
    (by simp [S₁, hrg.eq_iff, hunary])
    (by intro i; simp [S₁, hrg.eq_iff, hscratch])
  have hf : Function.update S₁.R (rg .dst) (binSyms L 0 ++ S₁.R (rg .dst)) =
      Function.update S.R (rg .dst) (binSyms L 0 ++ separator :: S.R (rg .dst)) := by
    simp [S₁]
  rw [hf] at he
  exact ⟨v', 1 + steps, hu, by omega,
    Exec.seq (hp ▸ Exec.act (body := body) _ (mk v S)) he⟩

end IntegerMultBounds.MathlibTM2.Routing
