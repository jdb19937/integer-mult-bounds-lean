module

public import IntegerMultBounds.MathlibTM2.Routing.MetadataJob

/-! Copy a unary coordinate and remove one symbol, saturating at zero. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def unaryPredecessorProgram (src dst tmp work : Fin T) : Pr P T Q A U :=
  .seq (bcopy src dst tmp work) (.act (.pop (.rt dst) (fun v _ => v) .done))

/-- Remove one symbol from a copied unary tape, preserving its original source. -/
theorem unaryPredecessor_exec (body : P → Pr P T Q A U) (src dst tmp work : Fin T)
    (hreg : [src, dst, tmp, work].Nodup) (v : HS T Q A U) (S : Stacks T A)
    (hdst : S.R dst = []) (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (unaryPredecessorProgram src dst tmp work) (mk v S) (6 * (S.R src).length + 7)
        (mk v' { S with R := Function.update S.R dst (S.R src).tail }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := bcopy_exec body hreg v S htmp hwork
  let S₁ : Stacks T A := { S with R := Function.update S.R dst (S.R src ++ S.R dst) }
  have hp : (Action.pop (.rt dst) (fun v _ => v) .done : Act T Q A U).run (mk v₁ S₁) =
      mk v₁ { S with R := Function.update S.R dst (S.R src).tail } := by
    simp [Action.run, update_rt, S₁, hdst]
  refine ⟨v₁, hu₁, ?_⟩
  exact Exec.cast (Exec.seq he₁ (hp ▸ Exec.act (body := body) _ (mk v₁ S₁))) (by omega) rfl

end IntegerMultBounds.MathlibTM2.Routing
